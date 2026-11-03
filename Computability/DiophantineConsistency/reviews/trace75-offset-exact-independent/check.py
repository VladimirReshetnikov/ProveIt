#!/usr/bin/env python3
"""Inspect retained trace75 exact offset author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75OffsetExact.lean';o=P/'observations/offsetexact-attempt01';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-offsetexact.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='49cee3f97902d1c7b94046a9289628bbc4b11e03082cfc5b7aa7b2062b5a5373'
assert sha(root/'Trace75OffsetExact.olean')==t['object_sha256']=='8b92370631be7284e641d6a8a27f0d78d9ae7e8f0e372f49d330c10c79d8970a'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75OffsetExact.graph_offset_exact' depends on axioms: [propext, Classical.choice, Quot.sound]\n'Trace75OffsetExact.graph_offset_full_divisibility' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75IndexAlignment']
mods=imports+['Trace75FirstResidue','Trace75RankExact','Trace75Rank','Trace75Pell','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
name='DiophantineConsistency.ModelRatioBounds';rel=name.replace('.','/')+'.olean';path=next(pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file());assert sha(path)=='fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7' and str(path) not in t['inputs'];assert not any((pathlib.Path(x)/'Trace75GraphPower.olean').is_file() for x in t['lean_path'].split(':'));print('post-hoc unpinned candidate (not proved loaded):',path,path.resolve(),sha(path))
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
