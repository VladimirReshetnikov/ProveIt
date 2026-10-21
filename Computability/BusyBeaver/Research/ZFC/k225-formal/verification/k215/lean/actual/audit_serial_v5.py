#!/usr/bin/env python3
"""Closed-client audit with exact current module/edge/companion checks and group-safe execution."""
from pathlib import Path
import argparse, hashlib, importlib.util, json, os, signal
P=Path(__file__).resolve().parent
ROOT=Path('/home/codex/.codex/worktrees/ec20/Proofs')
W=P/'workspace'; O=W/'.lake/build/lib/lean'
SUP=P/'portable-supervisor.py'
spec=importlib.util.spec_from_file_location('k215_supervisor',SUP)
sup=importlib.util.module_from_spec(spec);spec.loader.exec_module(sup)
sha=sup.sha
def interrupted(signum, frame):
 raise KeyboardInterrupt(f"Signal {signum}")
signal.signal(signal.SIGTERM,interrupted)
parser=argparse.ArgumentParser();parser.add_argument('source');parser.add_argument('label');args=parser.parse_args()
src=Path(args.source).resolve();dest=P/'audit'/args.label;dest.mkdir(parents=True,exist_ok=False)
inv=json.loads((P/'inventory-v5.json').read_text());entries={x['module']:x for x in inv['project_modules']}
completion=json.loads((P/'build-complete.json').read_text());done=json.loads((P/'completed.json').read_text())
assert completion['status']=='FULL_CURRENT_SOURCE_CLOSURE_PASS'
assert completion['completed_sha256']==sha(P/'completed.json')
assert set(done)==set(entries) and len(done)==204
assert inv['order']==[x['module'] for x in inv['project_modules']]
pins={str(P/'inventory-v5.json'):sha(P/'inventory-v5.json'),str(P/'completed.json'):sha(P/'completed.json'),str(SUP):sha(SUP),str(Path(__file__)):sha(Path(__file__))}
for m,entry in entries.items():
 row=done[m];source=ROOT/entry['relative_source'];obj=O/(m.replace('.','/')+'.olean')
 assert row['status']=='PASS' and row['exit_code']==0 and not row['timed_out'],m
 assert row['source']==str(source) and sha(source)==entry['sha256']==row['source_sha256'],m
 expected={d:done[d]['object_sha256'] for d in entry['imports'] if d in entries}
 assert row['dependencies']==expected,(m,'dependency mismatch')
 assert sha(obj)==row['object_sha256'],m
 assert row['companions'] and str(obj) in row['companions'],m
 assert sha(row['log'])==row['log_sha256'],m
 pins[str(source)]=sha(source);pins.update(row['companions']);pins[row['log']]=row['log_sha256']
boundary=json.loads((P/'toolchain-boundary-v5.json').read_text())
for key in ('lean','lake','Init.olean','project_toolchain'):
 q=boundary[key];pins[q['path']]=q['sha256']
for p,h in pins.items():assert sha(p)==h,p
pins[str(src)]=sha(src)
(dest/src.name).write_bytes(src.read_bytes())
cmd=['lake','env','lean','-j1','-M12288','--root='+str(src.parent),'-o',str(dest/(src.stem+'.olean')),str(src)]
row=dict(command=cmd,cwd=str(W),source=str(src),source_sha256=sha(src),before=pins,timeout_seconds=120,memory_mebibytes=12288,exact_module_set=True,exact_direct_dependency_edges=True,modules=204)
env=os.environ.copy();env.pop('LEAN_PATH',None);env['LEAN_NUM_THREADS']='1'
ok=sup.run_locked(cmd,W,env,Path('/tmp/proveit-k215-proof-build.lock'),dest/'compiler.log',120,row,dest/'verification.json')
row['after']={p:sha(p) for p in pins};row['inputs_unchanged']=row['before']==row['after'];assert row['inputs_unchanged']
row['fresh_companions']={str(p):sha(p) for p in dest.glob(src.stem+'.olean*')}
if ok:assert str(dest/(src.stem+'.olean')) in row['fresh_companions']
sup.save(dest/'verification.json',row)
print(json.dumps({k:v for k,v in row.items() if k not in ('before','after')},indent=2));print((dest/'compiler.log').read_text())
raise SystemExit(0 if ok else 1)
