#!/usr/bin/env python3
"""Inspect retained trace75 signed offset divisibility author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75OffsetDiv.lean';o=P/'observations/offsetdiv-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-offsetdiv-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='668bb42e1b78379d170f4d82e1f76a7a20c51d6a9b801c9916da4a1695f4c283'
assert sha(root/'Trace75OffsetDiv.olean')==t['object_sha256']=='994ed10ffec11931a4231a88100ab14fdb45cc0acd1eb92715c9a7c56ea99cde'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75OffsetDiv.graph_offset_divisible' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75CarrierBound']
mods=imports+['Direct80CarrierEstimate','CarrierSizes','Trace75Residue','Trace75Adjacent','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
bad=P/'observations/offsetdiv-attempt01';bt=json.loads((bad/'terminal.json').read_text());bl=(bad/'stdout').read_text()+(bad/'stderr').read_text();assert bt['exit']==0 and len(re.findall(r'warning:',bl))==4 and (bad/'source.txt').read_text().replace('ports,X,Y,q,b','ports,q,b')==s.read_text()
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
