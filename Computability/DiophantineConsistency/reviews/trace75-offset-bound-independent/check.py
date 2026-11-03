#!/usr/bin/env python3
"""Inspect trace75 offset bound and selected generic providers without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75OffsetBound.lean';o=P/'observations/offsetbound-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-offsetbound-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75OffsetBound.olean')==t['object_sha256']=='ff61154c7dfec50724c92d55a95b3610d41bccb8c294b02b0a888ef4db11236b','object')
for p,h in t['inputs'].items():need(sha(p)==h,'pin '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75OffsetBound.graph_offset_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['OffsetBound','Trace75Residue'],'direct imports')
mods=imports+['CarrierTransport','TransportOrder','Trace75Factors','Trace75RootNonzero','Trace75Root','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),'selection '+m)
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
expected={'OffsetBound':'1702af9273f8d0211bc57a013b97fe58c7e58a0791bb4b217f1207c6a27923a4','CarrierTransport':'05b15e987fa4eeb289936785ac2aaf7d4d2b0916fe29fd44ad9d52402c9da53d','TransportOrder':'6696792c784a1f6dc56e06076350015ca235a8973caf3ecda2a9328128056da2','Trace75Residue':'205d69b70c084f2613a94f465f3b46fd59f142f755e34897dd4257b16c819e8d'}
for m,h in expected.items():
 x=next(x for x in selected if x['module']==m);need(x['sha256']==h,'hash '+m)
 if m in ('OffsetBound','CarrierTransport','TransportOrder'):need(x['path'].startswith('/tmp/generic-transport-ufzumibs/'),'fresh generic '+m)
need(json.loads((P/'observations/offsetbound-attempt01/terminal.json').read_text())['exit']!=0,'prior failed')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
