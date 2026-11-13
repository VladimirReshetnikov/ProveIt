#!/usr/bin/env python3
"""Inspect the frozen halt first-seed receipt and providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-halt-first-seed-prototype';s=P/'DirectBFSHaltFirstSeed.lean';o=P/'observations/directbfshaltfirst-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner')
need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source')
need(sha(root/'DirectBFSHaltFirstSeed.olean')==t['object_sha256']=='0b2e073e622c771e5c52a0ef1ef6ceeaeb69c6c402451d076a6479c70fe82fd4','object')
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'DirectBFSHaltFirstSeed.halt_first_seed' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','axioms')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']],'imports')
expected=['8d9892b6ff938f9766c042609e1a4bdd78da4769b6b2bd946fb7c275ddcd7762','0361b27d675a978705be3e5a4ecda7191acf249e4e4625d7db3cff3182040ca5']
for x,h in zip(t['direct_imports'],expected):
 rel=x['module'].replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256']==h,'selection '+x['module'])
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'stage_receipts':len(t['stage_receipts']),'lean_replayed':False},indent=2,sort_keys=True))
