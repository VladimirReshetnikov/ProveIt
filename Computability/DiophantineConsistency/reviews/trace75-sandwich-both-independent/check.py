#!/usr/bin/env python3
"""Inspect retained trace75 both sandwiches author evidence without Lean replay."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75SandwichBoth.lean';o=P/'observations/sandwichboth-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(p):return hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
assert t['exit']==0 and t['reason'] is None
assert sha(P/'run-sandwichboth-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name)=='b80eda4851c30dd211f19eabaea1405154bb9171c27abde2eb21e6e5b9f3f98a'
assert sha(root/'Trace75SandwichBoth.olean')==t['object_sha256']=='9fdadd9aa0bf5288531f7a3692cd4958e7e8799633fcd5fd189ac816ef85d57d'
for p,h in t['inputs'].items():assert sha(p)==h,p
assert sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256']
assert (o/'stdout').read_text()=="'Trace75SandwichBoth.graph_sandwich_both' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and not (o/'stderr').read_text()
assert not re.search(r'\b(?:sorry|admit)\b',s.read_text());imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);assert imports==['Trace75SandwichLower','PellScaledUpper','Trace75GraphPower','DiophantineConsistency.ArithmeticHalfBinomial']
mods=imports+['PellScaledSandwich','PellVariableGrowth','Trace75VariableHeight','Trace75GraphProduct','Trace75ProductPower','Trace75ProductHeight','Trace75IndexAlignment','Trace75RankExact','Trace75Rank','Trace75Factors','DiophantineConsistency.TenPositiveTrace75','DiophantineConsistency.ModelDifferenceRing'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 assert p and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items()),m
 selected.append({'module':m,'path':str(p),'resolved':str(p.resolve()),'sha256':sha(p),'direct':m in imports})
name='DiophantineConsistency.ModelRatioBounds';rel=name.replace('.','/')+'.olean';path=next(pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file());assert sha(path)=='fcf4152e49cb9a989bd9f8ba08259a26c646dfca18370b0c6e1ce7ebfb33b8a7' and str(path) in t['inputs'] and t['inputs'][str(path)]==sha(path);print('post-hoc first-resolved pinned ModelRatioBounds',path,path.resolve(),sha(path))
bad=P/'observations/sandwichboth-attempt01';bt=json.loads((bad/'terminal.json').read_text());bl=(bad/'stdout').read_text()+(bad/'stderr').read_text();assert bt['exit']!=0 and "unknown module prefix 'Trace75GraphProduct'" in bl
print(json.dumps({'status':'PASS','selected':selected,'object_sha256':t['object_sha256'],'lean_replayed':False},indent=2,sort_keys=True))
