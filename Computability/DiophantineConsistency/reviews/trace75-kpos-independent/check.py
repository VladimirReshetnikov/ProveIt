#!/usr/bin/env python3
"""Audit retained trace75 K positivity evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Kpos.lean';o=P/'observations/kpos-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-kpos-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='58984eb7a1d8f12a0fa6685c63c3d8c8897b4b968dab0328c53bed30a7c6937c'
assert sha(root/'Trace75Kpos.olean')==t['object_sha256']=='c9dcda78a63d32accfcd4efc52e19f8e69747cc704c26f5fbdbd29e2eb9aa7d6'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75Kpos.graph_K_positive' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75Size','Trace75Residue']
mods=imports+['Trace75Adjacent','Trace75Index','Trace75Pell','Trace75Fold','Trace75Joined','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
f=P/'observations/kpos-attempt01';bad=json.loads((f/'terminal.json').read_text());assert bad['exit']!=0 and "unknown module prefix 'Trace75Adjacent'" in (f/'stdout').read_text()
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
