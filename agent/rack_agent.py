#!/usr/bin/env python3
"""rack_agent.py — call Claude (Opus) with RACK-scoped context and output sanitization.

Usage:
    python rack_agent.py "What are the six GSN node kinds?"
    echo "Generate a Rocq Goal node for memory safety" | python rack_agent.py
"""

import subprocess
import sys
import re
import os

AGENT_DIR = os.path.dirname(os.path.abspath(__file__))
PROMPT_FILE = os.path.join(AGENT_DIR, "rack_prompt.txt")

# Patterns that must never appear in output destined for public artifacts.
# These catch common secrets/infrastructure leaks.
REJECT_PATTERNS = [
    r"\b\d{1,3}\.\d{1,3}\.\d{1,3}\.\d{1,3}\b",          # IPv4 addresses
    r"\b200:[0-9a-f:]{4,}\b",                              # Yggdrasil addresses
    r"C:\\Users\\[A-Za-z]",                                 # Windows user paths
    r"/home/[a-z]",                                         # Linux home paths
    r"\bCOM\d+\b",                                          # Serial ports
    r"id_ed25519",                                          # SSH key references
    r"\bSSH\s+alias",                                       # SSH alias mentions
    r"\b(SAURON|Unity|pizero)\b",                           # Mesh node names
    r"\.ssh/",                                              # SSH directory refs
    r"api[_-]?key|secret[_-]?key|token\s*[:=]",            # Credential patterns
]

REJECT_RE = re.compile("|".join(REJECT_PATTERNS), re.IGNORECASE)


def load_system_prompt():
    with open(PROMPT_FILE, "r", encoding="utf-8") as f:
        return f.read().strip()


def sanitize(text):
    """Check output for infrastructure leaks. Returns (ok, text_or_error)."""
    for i, line in enumerate(text.splitlines(), 1):
        m = REJECT_RE.search(line)
        if m:
            return False, f"SANITIZER BLOCKED output at line {i}: matched pattern near '{m.group()[:20]}'"
    return True, text


def call_claude(prompt):
    system_prompt = load_system_prompt()

    cmd = [
        "claude",
        "--print",
        "--model", "opus",
        "--system-prompt", system_prompt,
        "--setting-sources", "",
        prompt,
    ]

    result = subprocess.run(
        cmd,
        capture_output=True,
        text=True,
        timeout=120,
    )

    if result.returncode != 0:
        print(f"ERROR: claude exited {result.returncode}", file=sys.stderr)
        if result.stderr:
            print(result.stderr, file=sys.stderr)
        sys.exit(result.returncode)

    ok, output = sanitize(result.stdout)
    if not ok:
        print(f"ERROR: {output}", file=sys.stderr)
        sys.exit(3)

    return output


def main():
    args = sys.argv[1:]

    if args:
        prompt = " ".join(args)
    elif not sys.stdin.isatty():
        prompt = sys.stdin.read().strip()
    else:
        print("Usage: rack_agent.py \"prompt\"", file=sys.stderr)
        sys.exit(1)

    if not prompt:
        print("ERROR: empty prompt", file=sys.stderr)
        sys.exit(1)

    output = call_claude(prompt)
    print(output)


if __name__ == "__main__":
    main()
