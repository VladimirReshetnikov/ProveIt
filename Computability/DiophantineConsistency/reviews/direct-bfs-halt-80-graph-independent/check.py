#!/usr/bin/env python3
"""Inspect halt-to-80 graph receipt, direct pins and selected common objects."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/direct-bfs-halt-80-graph-prototype';s=P/'DirectBFSHalt80Graph.lean';o=P/'observations/directbfshalt80-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root']);pins=t['pins']
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None and pins==t['after'] and t['direct_imports']==t['direct_imports_after'],'state')
need(sha(P/'run.py')==pins['runner'] and sha(t['command'][0])==pins['lean'],'runner')
need(sha(s)==pins['source']==sha(o/'source.txt')==sha(root/s.name),'source')
need(sha(root/'DirectBFSHalt80Graph.olean')==t['object_sha256']=='95f9655fe3b57826b1ef5b786396ae31ea089c3e859dbc59e04c355204278de3','object')
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'DirectBFSHalt80Graph.halt_zero_of_model_ports' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','axioms')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==[x['module'] for x in t['direct_imports']],'imports')
expected=['8d9892b6ff938f9766c042609e1a4bdd78da4769b6b2bd946fb7c275ddcd7762','aa879b5d70f582eedce7f0d0665d916c3703fb33540925411d96520e746c021e','756f04d7b963bab9c56670afd2652d9ea30671e3e9558c1f6f8c761f04d5da12','317c0619b647d15f16cfa51455574b88822fb39225a66eb5cbee12a00064a960']
for x,h in zip(t['direct_imports'],expected):
 rel=x['module'].replace('.','/')+'.olean';p=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(p and p.resolve()==pathlib.Path(x['path']).resolve() and sha(p)==x['sha256']==h,'selection '+x['module'])
for x in t['stage_receipts']:need(sha(x['path'])==x['sha256'],'stage receipt')
selected=[]
for m,h in {'Direct80Graph':'95eb93d8d48d28df810997b666e061ff20aab90e0adbf357e7590c511d2465d4','DirectBFSSymbolicKernel':'69f4a2f9d32229b6846ec7f0b84fe4b4d69d5eba8de1ff5c9ddb063e1d855c3f','DirectBFSFourFieldsPacking':'cfd3cc0045adbca24395a947ac2a4855ac94b313318f9c81660e38818ee3601c','DiophantineConsistency.ModelDifferenceRing':'d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74'}.items():
 rel=m.replace('.','/')+'.olean';q=next((pathlib.Path(z)/rel for z in t['lean_path'].split(':') if (pathlib.Path(z)/rel).is_file()),None)
 need(q and sha(q)==h,'shared selected '+m);selected.append({'module':m,'path':str(q),'sha256':sha(q)})
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'direct_imports':t['direct_imports'],'selected_common':selected,'stage_receipts':len(t['stage_receipts']),'lean_replayed':False},indent=2,sort_keys=True))
