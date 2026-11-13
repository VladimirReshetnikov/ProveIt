#!/usr/bin/env python3
"""Inspect frozen halt-chosen-rank receipt and providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-halt-chosen-rank-prototype';s=P/'DirectBFSHaltChosenRank.lean';o=P/'observations/directbfshaltchosen-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner')
need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source')
need(sha(root/'DirectBFSHaltChosenRank.olean')==t['object_sha256']=='a0ef6012dbb42a769e8c4ae3bae81ee73d9b57f427e0abc5e48236454af65690','object')
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
names=['DirectBFSHaltChosenRank.halt_pulse_stable','DirectBFSHaltChosenRank.halt_chosen_rank']
need((o/'stdout').read_text()==''.join(f"'{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in names) and (o/'stderr').read_text()=='','axioms')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']],'imports')
expected=['8df3e8efff5816547309041a01d0a62a3b19231e367650ec6a8e520ae7b001fc','d001ed95c02c91dbe3516e2134f3e78b2e55121d644f3e593f96a97601a18ff3','4aa19a2a942e445dcd33f22d16b8e75e9b0546e85a249ed95446f2efa905c372']
for x,h in zip(t['direct_imports'],expected):
 rel=x['module'].replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256']==h,'selection '+x['module'])
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
failed=P/'observations/directbfshaltchosen-attempt01';ft=json.loads((failed/'terminal.json').read_text());need(ft['exit']!=0,'previous failed')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'stage_receipts':len(t['stage_receipts']),'lean_replayed':False},indent=2,sort_keys=True))
