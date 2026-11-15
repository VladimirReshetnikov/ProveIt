#!/usr/bin/env python3
"""Replay a finite failed-reduction screen; this proves no state lower bound."""
from pathlib import Path
import argparse,hashlib,json,subprocess,tempfile

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--deep',action='store_true',help='Replay the three additional deeper searches')
    parser.add_argument('--index',type=int,help='Replay just one input index, 0 through93')
    parser.add_argument('--output',type=Path,help='Write JSON replay receipt')
    args=parser.parse_args()
    here=Path(__file__).resolve().parent
    catalogue=json.loads((here/('deep_catalogue.json' if args.deep else 'catalogue.json')).read_text())
    if args.index is not None:catalogue=[x for x in catalogue if x['index']==args.index]
    if not catalogue:raise SystemExit('No selected input')
    results=[]
    with tempfile.TemporaryDirectory(prefix='pa194-edge-search-')as tmp:
        exe=Path(tmp)/'edge_delete'
        subprocess.run(['g++','-O3','-std=c++17',str(here/'edge_delete.cpp'),'-o',str(exe)],check=True)
        for entry in catalogue:
            path=here/entry['input']
            if hashlib.sha256(path.read_bytes()).hexdigest()!=entry['sha256']:
                raise SystemExit(f'Input hash mismatch: {path}')
            p=subprocess.run([str(exe),str(path),str(entry['radius']),str(entry['new_step_bound']),str(entry['start']),str(entry['old_step_bound'])],capture_output=True,text=True,check=True)
            found=[json.loads(line)for line in p.stdout.splitlines()if line.strip()]
            rows=[line for line in p.stderr.splitlines()if line.startswith('Q ')]
            if len(rows)!=193:raise SystemExit(f'Expected193 deletion targets, received{len(rows)}')
            if found:raise SystemExit(f'Unexpected candidate(s) for input{entry["index"]}: {found}')
            result=dict(index=entry['index'],deletion_targets=len(rows),candidates=0,status='PASS_NO_CANDIDATE_IN_STATED_TEMPLATE')
            results.append(result);print(json.dumps(result),flush=True)
    receipt=dict(tables=len(results),status='PASS_FINITE_REPLAY',results=results)
    if args.output:args.output.write_text(json.dumps(receipt,indent=2)+'\n')

if __name__=='__main__':main()
