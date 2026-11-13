#!/usr/bin/env python3
"""Inspect retained trace75 strict power bound author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75PowerBound.lean';o=P/'observations/powerbound-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-powerbound.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='38bf55d1fda450f272f7752c3896361e2ac7e1aa98793d293a1b7001b0972110'
assert sha(root/'Trace75PowerBound.olean')==t['object_sha256']=='b4e6a42fc8abe23e8282d6ad12c354f5938d99ce10e0918222e1d54ce4447271'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75PowerBound.graph_power_bound' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75IndexAlignment','Direct80ScaledGrowthMinus']
mods=imports+['Trace75FirstResidue','Trace75RankExact','Trace75Rank','Trace75Pell','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
