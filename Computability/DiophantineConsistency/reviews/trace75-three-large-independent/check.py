#!/usr/bin/env python3
"""Inspect frozen generic three-large receipt/provider selection without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75ThreeLarge.lean';o=P/'observations/threelarge-attempt05';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-threelarge-v5.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75ThreeLarge.olean')==t['object_sha256']=='d8e8d07e7b91ee60a8afe6ea393f839f9c49aa386185d134d2bdefee8ca7b604','object')
for p,h in t['inputs'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75ThreeLarge.impossible' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['DiophantineConsistency.ArithmeticPellHalfIndex','Mathlib.Tactic.Linarith'],'imports');selected=[]
for m in imports:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selection '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p)})
for i in range(1,5):need(json.loads((P/f'observations/threelarge-attempt0{i}/terminal.json').read_text())['exit']!=0,'failed attempt '+str(i))
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
