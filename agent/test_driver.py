#!/usr/bin/env python3
"""Basic tests for rack_driver.py utility functions."""

import sys
import os

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rack_driver import sha256_string, sha256_file, now_iso

def test(label, condition):
    if condition:
        print(f"  PASS  {label}")
    else:
        print(f"  FAIL  {label}")
        sys.exit(1)

print("=== rack_driver utility tests ===")

# sha256_string
test("sha256 empty", sha256_string("") ==
     "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
test("sha256 abc", sha256_string("abc") ==
     "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")

# now_iso produces valid format
ts = now_iso()
test("now_iso format", len(ts) == 20 and ts.endswith("Z") and "T" in ts)

# sha256_file on a temp file
import tempfile
with tempfile.NamedTemporaryFile(mode="w", suffix=".txt", delete=False) as f:
    f.write("hello")
    tmp = f.name
try:
    h = sha256_file(tmp)
    test("sha256_file", h ==
         "2cf24dba5fb0a30e26e83b2ac5b9e29e1b161e5c1fa7425e73043362938b9824")
finally:
    os.unlink(tmp)

print("\n=== All driver tests passed ===")
