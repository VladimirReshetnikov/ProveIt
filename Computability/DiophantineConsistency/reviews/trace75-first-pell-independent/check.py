#!/usr/bin/env python3
"""Inspect the frozen first Pell receipt and direct providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Pell.lean';o=P/'observations/pell-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-pell.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75Pell.olean')==t['object_sha256']=='cea9dcd9cc72467aa28113a65178cb7763170960ef0a4b215153537fb77bfbb9','object')
for p,h in t['inputs'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75Pell.first_and_doubled' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['Trace75Factors','DiophantineConsistency.ArithmeticPellFirstNorm'],'imports')
selected=[]
for m in imports+['Trace75RootNonzero','Trace75Root','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','ProductRoot']:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selected '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
need(selected[0]['sha256']=='1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975','factors provider')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
