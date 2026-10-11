#!/usr/bin/env python3
"""Verify the checksum manifest of an unmodified extracted delivery."""
from __future__ import annotations
import hashlib,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def main():
 manifest=ROOT/'MANIFEST.sha256'
 if not manifest.is_file():raise SystemExit('MANIFEST.sha256 not found')
 failed=[];count=0
 for line in manifest.read_text().splitlines():
  digest,name=line.split('  ',1)
  path=(ROOT/name).resolve()
  if not path.is_relative_to(ROOT):raise SystemExit('Unsafe path in manifest')
  if not path.is_file() or hashlib.sha256(path.read_bytes()).hexdigest()!=digest:failed.append(name)
  count+=1
 if failed:
  print('FAILED: '+', '.join(failed),file=sys.stderr);return 1
 print(f'PASS: {count} file hashes match.');return 0
if __name__=='__main__':raise SystemExit(main())
