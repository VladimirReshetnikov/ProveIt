#!/usr/bin/env python3
"""Read-only check of the optional notation patch against a ProveIt checkout.

This script never applies the patch or changes the repository. It rejects a
changed source snapshot rather than silently patching a different version.
"""
from pathlib import Path
import argparse, hashlib, subprocess, sys
EXPECTED = '044d3825b90dce437ac9007733e6447cf9563098'
REL = Path('Analysis/Polylogarithms/docs/manuscript/chapters/05-real-positive-kernel.tex')
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repository_root',type=Path)
    args=ap.parse_args()
    root=args.repository_root.resolve(); source=root/REL
    if not source.is_file(): raise SystemExit(f'Missing source: {source}')
    data=source.read_bytes()
    actual=hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()
    if actual!=EXPECTED:
        raise SystemExit(f'Source changed: expected blob {EXPECTED}, got {actual}. Review the patch manually.')
    patch=Path(__file__).resolve().parents[1]/'integration'/'notation_corrections.patch'
    subprocess.run(['git','apply','--check',str(patch)],cwd=root,check=True)
    print('PASS: expected source blob and git apply --check. No files changed.')
if __name__=='__main__':
    try: main()
    except (OSError,subprocess.CalledProcessError) as exc:
        print(f'Patch check failed: {exc}',file=sys.stderr);sys.exit(1)
