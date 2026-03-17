#!/usr/bin/env python3
"""rack_review.py — PR review bot for RACK assurance cases.

Reads a PR diff, identifies affected assurance case JSON files,
runs rack_cli --check and --diagnose, and formats a review comment.

Usage (local):
    python rack_review.py --pr 5
    python rack_review.py --diff <(git diff main..HEAD)

Usage (GitHub Actions):
    python rack_review.py --pr "${{ github.event.pull_request.number }}"

Requires: rack_cli on PATH (or RACK_CLI env var), gh CLI for PR operations.
"""

import subprocess
import sys
import os
import json
import re

RACK_CLI = os.environ.get("RACK_CLI", "rack_cli")


def run(cmd, input_data=None, check=False):
    """Run a command, return (returncode, stdout, stderr)."""
    result = subprocess.run(
        cmd, capture_output=True, text=True,
        input=input_data, timeout=120,
    )
    if check and result.returncode != 0:
        print(f"ERROR: {' '.join(cmd)} exited {result.returncode}", file=sys.stderr)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        sys.exit(result.returncode)
    return result.returncode, result.stdout, result.stderr


def get_pr_diff(pr_number):
    """Get PR diff via gh CLI."""
    rc, stdout, _ = run(["gh", "pr", "diff", str(pr_number)])
    if rc != 0:
        print(f"ERROR: could not get diff for PR #{pr_number}", file=sys.stderr)
        sys.exit(1)
    return stdout


def find_case_files(diff_text):
    """Extract paths to .json files that look like assurance cases from a diff."""
    paths = set()
    for line in diff_text.splitlines():
        m = re.match(r'^diff --git a/(.*\.json) b/', line)
        if m:
            paths.add(m.group(1))
    return sorted(paths)


def find_v_files(diff_text):
    """Extract paths to .v files from a diff."""
    paths = set()
    for line in diff_text.splitlines():
        m = re.match(r'^diff --git a/(.*\.v) b/', line)
        if m:
            paths.add(m.group(1))
    return sorted(paths)


def check_case(case_path):
    """Run rack_cli --check on a case file. Returns (passed, errors_json)."""
    if not os.path.exists(case_path):
        return None, None

    with open(case_path, 'r') as f:
        case_json = f.read()

    # Check
    rc_check, stdout_check, _ = run(
        [RACK_CLI, "--check"], input_data=case_json
    )
    passed = rc_check == 0

    # Diagnose
    rc_diag, stdout_diag, _ = run(
        [RACK_CLI, "--diagnose"], input_data=case_json
    )

    errors = []
    if stdout_diag.strip():
        try:
            errors = json.loads(stdout_diag.strip())
        except json.JSONDecodeError:
            errors = [{"raw": stdout_diag.strip()}]

    return passed, errors


def format_review(results, v_files):
    """Format review results as a markdown comment."""
    lines = ["## RACK Assurance Case Review\n"]

    if not results and not v_files:
        lines.append("No assurance case files or Rocq sources affected by this PR.")
        return "\n".join(lines)

    # Case file results
    all_passed = True
    for path, (passed, errors) in results.items():
        if passed is None:
            lines.append(f"- `{path}` — file not found (deleted?)")
            continue
        if passed:
            lines.append(f"- `{path}` — **PASS**")
        else:
            all_passed = False
            lines.append(f"- `{path}` — **FAIL**")
            if errors:
                for err in errors:
                    if isinstance(err, dict) and "error" in err:
                        node = err.get("node", err.get("from", "?"))
                        lines.append(f"  - `{err['error']}` at `{node}`")
                    elif isinstance(err, dict) and "raw" in err:
                        lines.append(f"  - {err['raw'][:200]}")

    # Rocq files touched
    if v_files:
        lines.append("")
        lines.append(f"**Rocq files changed:** {len(v_files)}")
        for vf in v_files[:20]:
            lines.append(f"- `{vf}`")
        if len(v_files) > 20:
            lines.append(f"- ... and {len(v_files) - 20} more")

    # Verdict
    lines.append("")
    if results:
        if all_passed:
            lines.append("> All assurance cases well-formed.")
        else:
            lines.append("> **Action required:** one or more assurance cases failed well-formedness checks.")

    return "\n".join(lines)


def post_comment(pr_number, body):
    """Post a PR comment via gh CLI."""
    rc, _, stderr = run(
        ["gh", "pr", "comment", str(pr_number), "--body", body]
    )
    if rc != 0:
        print(f"ERROR: could not post comment: {stderr}", file=sys.stderr)
        sys.exit(1)


def main():
    args = sys.argv[1:]
    pr_number = None
    diff_file = None

    i = 0
    while i < len(args):
        if args[i] == "--pr" and i + 1 < len(args):
            pr_number = args[i + 1]
            i += 2
        elif args[i] == "--diff" and i + 1 < len(args):
            diff_file = args[i + 1]
            i += 2
        else:
            i += 1

    # Get diff
    if pr_number:
        diff_text = get_pr_diff(pr_number)
    elif diff_file:
        if diff_file == "-":
            diff_text = sys.stdin.read()
        else:
            with open(diff_file, 'r') as f:
                diff_text = f.read()
    else:
        print("Usage: rack_review.py --pr NUMBER | --diff FILE", file=sys.stderr)
        sys.exit(1)

    # Find affected files
    case_files = find_case_files(diff_text)
    v_files = find_v_files(diff_text)

    # Check each case file
    results = {}
    for cf in case_files:
        passed, errors = check_case(cf)
        results[cf] = (passed, errors)

    # Format review
    body = format_review(results, v_files)

    if pr_number:
        post_comment(pr_number, body)
        print(f"Posted review to PR #{pr_number}")
    else:
        print(body)


if __name__ == "__main__":
    main()
