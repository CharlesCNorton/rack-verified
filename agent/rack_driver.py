#!/usr/bin/env python3
"""rack_driver.py — run external verification tools and package results as RACK evidence.

Invokes CBMC, Kani, SAW, or Alloy as subprocesses, parses their output,
and produces RACK-compatible Certificate evidence JSON that can be injected
into an assurance case via rack_cli or hydrate_evidence.

Usage:
    python rack_driver.py cbmc --harness harness.c --unwind 200
    python rack_driver.py kani --crate . --harness verify_altitude
    python rack_driver.py saw --script check.saw
    python rack_driver.py alloy --model system.als --check
"""

import subprocess
import sys
import os
import json
import hashlib
import datetime
import re


def sha256_file(path):
    """SHA-256 hex digest of a file."""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_string(s):
    """SHA-256 hex digest of a string."""
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def now_iso():
    return datetime.datetime.now(datetime.timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


def run_tool(cmd, timeout=600):
    """Run a tool, return (returncode, stdout, stderr)."""
    try:
        result = subprocess.run(
            cmd, capture_output=True, text=True, timeout=timeout,
        )
        return result.returncode, result.stdout, result.stderr
    except FileNotFoundError:
        print(f"ERROR: '{cmd[0]}' not found on PATH", file=sys.stderr)
        sys.exit(127)
    except subprocess.TimeoutExpired:
        print(f"ERROR: '{cmd[0]}' timed out after {timeout}s", file=sys.stderr)
        sys.exit(124)


def make_evidence(tool_id, verdict, blob, artifact_hash, metadata=None):
    """Build a RACK Certificate evidence JSON object."""
    return {
        "type": "Certificate",
        "tool": tool_id,
        "blob": blob,
        "verdict": verdict,
        "artifact_hash": artifact_hash,
        "timestamp": now_iso(),
        "metadata": metadata or {},
    }


# -- CBMC driver --

def driver_cbmc(args):
    harness = None
    unwind = "100"
    extra = []
    i = 0
    while i < len(args):
        if args[i] == "--harness" and i + 1 < len(args):
            harness = args[i + 1]; i += 2
        elif args[i] == "--unwind" and i + 1 < len(args):
            unwind = args[i + 1]; i += 2
        else:
            extra.append(args[i]); i += 1

    if not harness:
        print("ERROR: --harness required for cbmc", file=sys.stderr)
        sys.exit(1)

    cmd = ["cbmc", harness, "--unwind", unwind] + extra
    rc, stdout, stderr = run_tool(cmd)

    if "VERIFICATION SUCCESSFUL" in stdout:
        verdict = "verified"
    elif "VERIFICATION FAILED" in stdout:
        verdict = "falsified"
    else:
        verdict = "unknown"

    blob = f"cbmc:{verdict}:{os.path.basename(harness)}:unwind={unwind}:{now_iso()}"
    artifact_hash = sha256_file(harness)

    return make_evidence(
        tool_id=f"CBMC",
        verdict=verdict,
        blob=blob,
        artifact_hash=artifact_hash,
        metadata={
            "harness": os.path.basename(harness),
            "unwind": unwind,
            "returncode": rc,
        },
    )


# -- Kani driver --

def driver_kani(args):
    crate = "."
    harness = None
    extra = []
    i = 0
    while i < len(args):
        if args[i] == "--crate" and i + 1 < len(args):
            crate = args[i + 1]; i += 2
        elif args[i] == "--harness" and i + 1 < len(args):
            harness = args[i + 1]; i += 2
        else:
            extra.append(args[i]); i += 1

    cmd = ["cargo", "kani"]
    if harness:
        cmd.extend(["--harness", harness])
    cmd.extend(extra)

    rc, stdout, stderr = run_tool(cmd, timeout=900)

    if "VERIFICATION:- SUCCESSFUL" in stdout or "Complete - 0 failures" in stdout:
        verdict = "verified"
    elif "VERIFICATION:- FAILED" in stdout:
        verdict = "falsified"
    else:
        verdict = "unknown"

    blob = f"kani:{verdict}:{harness or 'all'}:{now_iso()}"
    cargo_toml = os.path.join(crate, "Cargo.toml")
    artifact_hash = sha256_file(cargo_toml) if os.path.exists(cargo_toml) else "none"

    return make_evidence(
        tool_id=f"Kani",
        verdict=verdict,
        blob=blob,
        artifact_hash=artifact_hash,
        metadata={
            "harness": harness or "all",
            "crate": crate,
            "returncode": rc,
        },
    )


# -- SAW driver --

def driver_saw(args):
    script = None
    extra = []
    i = 0
    while i < len(args):
        if args[i] == "--script" and i + 1 < len(args):
            script = args[i + 1]; i += 2
        else:
            extra.append(args[i]); i += 1

    if not script:
        print("ERROR: --script required for saw", file=sys.stderr)
        sys.exit(1)

    cmd = ["saw", script] + extra
    rc, stdout, stderr = run_tool(cmd, timeout=900)

    if rc == 0 and "Q.E.D." in stdout:
        verdict = "verified"
    elif "Proof failed" in stdout or rc != 0:
        verdict = "falsified"
    else:
        verdict = "unknown"

    blob = f"saw:{verdict}:{os.path.basename(script)}:{now_iso()}"
    artifact_hash = sha256_file(script)

    return make_evidence(
        tool_id=f"SAW",
        verdict=verdict,
        blob=blob,
        artifact_hash=artifact_hash,
        metadata={
            "script": os.path.basename(script),
            "returncode": rc,
        },
    )


# -- Alloy driver --

def driver_alloy(args):
    model = None
    extra = []
    i = 0
    while i < len(args):
        if args[i] == "--model" and i + 1 < len(args):
            model = args[i + 1]; i += 2
        else:
            extra.append(args[i]); i += 1

    if not model:
        print("ERROR: --model required for alloy", file=sys.stderr)
        sys.exit(1)

    # Alloy CLI analysis
    cmd = ["java", "-jar", os.environ.get("ALLOY_JAR", "alloy.jar"),
           "-c", model] + extra
    rc, stdout, stderr = run_tool(cmd, timeout=300)

    if "No counterexample found" in stdout or "0 unsatisfied" in stdout:
        verdict = "verified"
    elif "Counterexample found" in stdout:
        verdict = "falsified"
    else:
        verdict = "unknown"

    blob = f"alloy:{verdict}:{os.path.basename(model)}:{now_iso()}"
    artifact_hash = sha256_file(model)

    return make_evidence(
        tool_id=f"Alloy",
        verdict=verdict,
        blob=blob,
        artifact_hash=artifact_hash,
        metadata={
            "model": os.path.basename(model),
            "returncode": rc,
        },
    )


DRIVERS = {
    "cbmc": driver_cbmc,
    "kani": driver_kani,
    "saw": driver_saw,
    "alloy": driver_alloy,
}


def main():
    if len(sys.argv) < 2 or sys.argv[1] not in DRIVERS:
        tools = ", ".join(DRIVERS.keys())
        print(f"Usage: rack_driver.py <{tools}> [--node NODE_ID] [tool-args...]", file=sys.stderr)
        sys.exit(1)

    tool = sys.argv[1]
    tool_args = sys.argv[2:]

    # Extract --node if present (for hydration mapping)
    node_id = None
    if "--node" in tool_args:
        idx = tool_args.index("--node")
        if idx + 1 < len(tool_args):
            node_id = tool_args[idx + 1]
            tool_args = tool_args[:idx] + tool_args[idx + 2:]

    evidence = DRIVERS[tool](tool_args)
    if node_id:
        evidence["node_id"] = node_id
    print(json.dumps(evidence, indent=2))


if __name__ == "__main__":
    main()
