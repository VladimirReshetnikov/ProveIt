#!/usr/bin/env python3
"""Audit the frozen adjacent packet and selected providers; no Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Adjacent.lean';o=P/'observations/adjacent-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-adjacent.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75Adjacent.olean')==t['object_sha256']=='f8b22b6107778dd98a51e6aa356d8190a0be377c811bceeff43dfcd1b19f17ea','object')
for p,h in t['inputs'].items():need(sha(p)==h,'input '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75Adjacent.graph_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','reports')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['Trace75Factors','AdjacentInteger'],'direct imports')
mods=['Trace75Factors','AdjacentInteger','AdjacentComplete','AdjacentStep','AdjacentBounds','AdjacentDenominator','AdjacentPreserve','Trace75RootNonzero','Trace75Root','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing','DiophantineConsistency.ArithmeticGcdNormalization','ProductRoot','TenPositiveDoubling','ScaledSquare'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selection '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
need(selected[0]['sha256']=='1bae9331cfbca4e35cb48916f135b63eedc8b5c827f8f24ae6f12b2dff111975','factors provider')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'source_sha256':sha(s),'runner_sha256':sha(P/'run-adjacent.py'),'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
