#!/usr/bin/env python3
"""Audit frozen trace75 carrier-bound receipt/providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75CarrierBound.lean';o=P/'observations/carrierbound-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-carrierbound.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75CarrierBound.olean')==t['object_sha256']=='8ef47fc9a296744657c3f3dfd7130aeab24058371533a995a247e045318af923','object')
for p,h in t['inputs'].items():need(sha(p)==h,'pin '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75CarrierBound.graph_carrier_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['Direct80CarrierEstimate','CarrierSizes','Trace75Adjacent','Trace75Residue'],'direct imports')
mods=imports+['AdjacentBounds','Trace75Factors','Trace75RootNonzero','Trace75Root','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selection '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
need(selected[2]['sha256']=='f8b22b6107778dd98a51e6aa356d8190a0be377c811bceeff43dfcd1b19f17ea' and selected[3]['sha256']=='205d69b70c084f2613a94f465f3b46fd59f142f755e34897dd4257b16c819e8d','trace providers')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
