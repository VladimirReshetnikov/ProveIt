#!/usr/bin/env python3
"""Inspect retained trace75 population author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75Population.lean';o=P/'observations/population-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-population.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='8ae8cf2699028822fb18fd1f8d403034902a889124248aca6733be640c8a2ea5'
assert sha(root/'Trace75Population.olean')==t['object_sha256']=='489720787a2df7640be88dc68768b1b62a9e9e3d7172128fe246c90a13f20332'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75Population.graph_population' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75SandwichBoth','Trace75Repunit','ScaledPellRounding','DiophantineConsistency.ArithmeticHalfBinomial']
mods=imports+['Trace75RadixAlignment','Trace75GraphPower','Trace75VariableHeight','Trace75GraphProduct','Trace75ProductPower','Trace75ProductHeight','Trace75RankExact','Trace75Rank','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
name='DiophantineConsistency.ModelRatioBounds';rel=name.replace('.','/')+'.olean';path=next(pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file());assert sha(path)=='fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7' and str(path) in t['inputs'] and t['inputs'][str(path)]==sha(path);print('post-hoc first-resolved pinned ModelRatioBounds',path,path.resolve(),sha(path))
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
