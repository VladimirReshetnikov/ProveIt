#!/usr/bin/env python3
"""Verify pinned source hashes and dry-run all proposed patches; never modify files."""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('repository',type=Path)
args=parser.parse_args()
package=Path(__file__).resolve().parents[1]
record=json.loads((package/'evidence/patch-metrics.json').read_text())
errors=[]
for item in record['files']:
    path=args.repository/item['file']
    if not path.is_file():
        errors.append(f'Missing: {path}')
    elif hashlib.sha256(path.read_bytes()).hexdigest()!=item['original_sha256']:
        errors.append(f'Content differs from pinned source: {path}')
if errors:
    print('\n'.join(errors),file=sys.stderr)
    raise SystemExit(1)
result=subprocess.run(['git','apply','--check',str(package/'patches/all-proof-refactorings.patch')],cwd=args.repository.resolve())
if result.returncode:
    raise SystemExit(result.returncode)
print(f'All {len(record["files"])} original hashes match; combined patch dry-run passed.')
