#!/usr/bin/env python3
"""Inspect frozen pulse receipt and direct providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-cell-pulse-equality-prototype';s=P/'DirectBFSCellPulseEquality.lean';o=P/'observations/directbfscellpulseeq-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner')
need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source')
need(sha(root/'DirectBFSCellPulseEquality.olean')==t['object_sha256']=='d001ed95c02c91dbe3516e2134f3e78b2e55121d644f3e593f96a97601a18ff3','object')
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
names=['DirectBFSCellPulseEquality.cell_one','DirectBFSCellPulseEquality.cell_pulse']
need((o/'stdout').read_text()==''.join(f"'{x}' depends on axioms: [propext, Classical.choice, Quot.sound]\n" for x in names) and (o/'stderr').read_text()=='','axioms')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']],'imports')
for x in t['direct_imports']:
 rel=x['module'].replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256'],'selection '+x['module'])
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'stage_receipts':len(t['stage_receipts']),'lean_replayed':False},indent=2,sort_keys=True))
