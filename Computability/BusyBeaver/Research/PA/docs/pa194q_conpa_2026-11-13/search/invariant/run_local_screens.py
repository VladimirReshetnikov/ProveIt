#!/usr/bin/env python3
"""Replay the three precisely bounded local deletion searches on frozen windows."""
from pathlib import Path
import subprocess,shutil,sys,json
P=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(P/'verify_inputs.py')],check=True)
cc=shutil.which('g++')or shutil.which('clang++')
if not cc:raise SystemExit('A C++17 compiler is required')
out=P/'local_replay';out.mkdir(exist_ok=True)
patterns=P/'contexts_C_affine/patterns_k5.txt';table=P/'machine.native.tm';summary={}
for name in ['action_merge_all','bypass_all','bypass_join']:
 exe=out/name;subprocess.run([cc,'-std=c++17','-O3',str(P/(name+'.cpp')),'-o',str(exe)],check=True)
 args=[str(exe),str(table),'5']+(['500',str(patterns)]if name=='action_merge_all'else[str(patterns),'500'])
 with (out/(name+'.jsonl')).open('w')as stdout,(out/(name+'.log')).open('w')as stderr:
  subprocess.run(args,stdout=stdout,stderr=stderr,check=True)
 summary[name]=sum(1 for _ in(out/(name+'.jsonl')).open())
(out/'summary.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
