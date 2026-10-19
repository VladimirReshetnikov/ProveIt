#!/usr/bin/env python3
"""Recompile and replay selected local-search families into a separate folder.

Requires Python3 and a GCC-compatible C++17 compiler. No network access.
"""
import argparse, hashlib, json, subprocess
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
p=argparse.ArgumentParser(description=__doc__)
g=p.add_mutually_exclusive_group(required=True)
g.add_argument('--controls',action='store_true',help='replay the two positive controls')
g.add_argument('--all',action='store_true',help='replay all completed searches (several minutes)')
g.add_argument('--family',action='append',help='one family name; may be repeated')
p.add_argument('--out',type=Path,required=True,help='separate output directory')
a=p.parse_args()
recipes=json.loads((ROOT/'search_receipt.json').read_text())['families']
names={x['name'] for x in recipes}
if a.family:
    missing=set(a.family)-names
    if missing:raise SystemExit('Unknown family: '+', '.join(sorted(missing)))
selected=[x for x in recipes if a.all or (a.controls and x.get('positive_control')) or (a.family and x['name'] in a.family)]
a.out.mkdir(parents=True,exist_ok=True);build=a.out/'build';build.mkdir(exist_ok=True)
compiled={};records=[]
for spec in selected:
    source=ROOT/'code'/spec['source']
    if source.name not in compiled:
        binary=build/source.stem
        subprocess.run(['g++','-O3','-std=c++17',str(source),'-o',str(binary)],check=True)
        compiled[source.name]=binary
    args=[str(compiled[source.name])]
    for value in spec['arguments']:
        args.append(str(ROOT/value) if isinstance(value,str) and value.startswith(('input/','results/')) else str(value))
    stdout=a.out/(spec['name']+'.txt');stderr=a.out/(spec['name']+'.log')
    with stdout.open('w') as out,stderr.open('w') as err:
        run=subprocess.run(args,stdout=out,stderr=err)
    if run.returncode:raise RuntimeError((spec['name'],run.returncode,stderr.read_text()))
    expected=ROOT/'results'/(spec['name']+'.txt')
    if stdout.read_bytes()!=expected.read_bytes():
        raise AssertionError(('candidate output changed',spec['name']))
    last=stderr.read_text().splitlines()[-1]
    if not last.startswith('FINISHED'):raise AssertionError(('search did not complete',spec['name'],last))
    record={'name':spec['name'],'returncode':run.returncode,'stdout_sha256':hashlib.sha256(stdout.read_bytes()).hexdigest(),'final_log':last,'candidate_output_matches':True}
    records.append(record);print(json.dumps(record),flush=True)
(a.out/'replay_receipt.json').write_text(json.dumps(records,indent=2)+'\n')
