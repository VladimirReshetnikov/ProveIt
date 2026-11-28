#!/usr/bin/env python3
"""Verify audited Git object IDs at a pinned revision, not mutable working-tree files."""
import argparse, csv, subprocess
from pathlib import Path

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('repo',type=Path,help='local ProveIt Git checkout containing the pinned commit')
    a=ap.parse_args(); root=Path(__file__).resolve().parent
    n=0; failures=[]
    for name in ['source_audit.tsv','proposal_audit.tsv']:
        with (root/name).open() as f:
            for row in csv.DictReader(f,delimiter='\t'):
                ref=row['commit']+':'+row['path']
                cmd=['git','-C',str(a.repo),'rev-parse','--verify',ref]
                p=subprocess.run(cmd,text=True,capture_output=True)
                if p.returncode or p.stdout.strip()!=row['git_object_id']:
                    failures.append((ref,p.stdout.strip(),p.stderr.strip(),row['git_object_id']))
                else:
                    n+=1
    for ref,got,err,want in failures:
        print(f'FAIL {ref}: expected {want}, got {got or err}')
    print(f'{n} object IDs matched; {len(failures)} failures')
    return int(bool(failures))
if __name__=='__main__': raise SystemExit(main())
