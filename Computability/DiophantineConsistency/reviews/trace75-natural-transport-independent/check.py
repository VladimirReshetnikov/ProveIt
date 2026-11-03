#!/usr/bin/env python3
"""Inspect retained trace75 natural transport author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75NaturalTransport.lean';o=P/'observations/naturaltransport-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-naturaltransport.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='63a39f230b4922c5268c32c8529f84a0b4cdafafe814ea2cecc44814b25da6d0'
assert sha(root/'Trace75NaturalTransport.olean')==t['object_sha256']=='7dc95f3eafbc65d70f873dcfbc34815ff30618f5161e3c36a99a0729e1c49786'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75NaturalTransport.graph_natural_transport' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75IntegralTransport']
mods=imports+['Trace75Kappa','Trace75OffsetExact','Trace75Transport','Trace75GraphPower','Trace75Rank','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
name='DiophantineConsistency.ModelRatioBounds';rel=name.replace('.','/')+'.olean';path=next(pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file());assert sha(path)=='fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7' and str(path) in t['inputs'] and t['inputs'][str(path)]==sha(path);print('post-hoc first-resolved pinned ModelRatioBounds',path,path.resolve(),sha(path))
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
