#!/usr/bin/env python3
"""Basic tests for rack_agent.py sanitizer."""

import sys
import os
import re

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rack_agent import sanitize, REJECT_RE

def test(label, ok, text):
    result_ok, _ = sanitize(text)
    if result_ok == ok:
        print(f"  PASS  {label}")
    else:
        print(f"  FAIL  {label}: expected {'ok' if ok else 'blocked'}, got {'ok' if result_ok else 'blocked'}")
        sys.exit(1)

print("=== rack_agent sanitizer tests ===")
test("clean text passes", True, "The system is safe.")
test("private IP blocked", False, "Connect to 192.168.1.101 for access")
test("10.x blocked", False, "Server at 10.0.0.1")
test("version string passes", True, "CBMC version 1.2.3.4 installed")
test("Yggdrasil blocked", False, "Address 200:50d9:7666:381a:d149:275d:2924:93f3")
test("Windows path blocked", False, r"File at C:\Users\cnort\secret")
test("Linux home blocked", False, "Config in /home/zootest/.ssh")
test("SSH key ref blocked", False, "Using id_ed25519 key")
test("credential pattern blocked", False, "api_key = abc123")
test("COM port blocked", False, "Device on COM4")
test("mesh node blocked", False, "Connecting to SAURON")
test("public IP passes", True, "Documentation at 8.8.8.8")
test("dotted version passes", True, "Rocq 9.0.0 release")
print("\n=== All sanitizer tests passed ===")
