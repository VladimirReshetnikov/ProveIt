#!/usr/bin/env python3
"""Inspect retained trace75 joined-square author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75JoinedSquare.lean';o=P/'observations/joinedsquare-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-joinedsquare.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='39c3780be09f7e533a44ff5a59123c5b3d67d70141a1ba49e07cbdd59196f86c'
assert sha(root/'Trace75JoinedSquare.olean')==t['object_sha256']=='09ab5f30401baa3f93c69db97a44b4c6f5c3fc0dbdd7b08770ba623af925d620'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert ' '.join((o/'stdout').read_text().split())=="'Trace75JoinedSquare.strong_and_auxiliary_indices_with_graph_residue' depends on axioms: [propext, Classical.choice, Quot.sound]" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75Residue','Trace75Adjacent','DiophantineConsistency.ArithmeticPellHalfIndex']
mods=imports+['Trace75Factors','AdjacentInteger','AdjacentStep','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
