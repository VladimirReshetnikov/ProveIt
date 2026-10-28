#!/usr/bin/env python3
"""Verify the delivered file manifest before regenerating any results."""
from pathlib import Path
import hashlib
import json
ROOT=Path(__file__).resolve().parent
def main():
    manifest=json.loads((ROOT/"MANIFEST.sha256.json").read_text())
    for item in manifest["files"]:
        p=ROOT/item["path"]
        if not p.is_file():raise RuntimeError("Missing: "+item["path"])
        b=p.read_bytes()
        if len(b)!=item["bytes"] or hashlib.sha256(b).hexdigest()!=item["sha256"]:
            raise RuntimeError("Changed: "+item["path"])
    print(json.dumps({"status":"passed","verified_files":len(manifest["files"])},indent=2))
if __name__=="__main__":main()
