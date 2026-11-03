#!/usr/bin/env python3
"""Audit main-three contradiction receipt and selected providers without Lean."""
import hashlib,json,pathlib,re
D=pathlib.Path(__file__).resolve().parents[2];P=D/'research/trace75-root-probe';s=P/'Trace75ThreeExcluded.lean';o=P/'observations/threeexcluded-attempt02';t=json.loads((o/'terminal.json').read_text());root=pathlib.Path(t['output_root'])
def sha(x):return hashlib.sha256(pathlib.Path(x).read_bytes()).hexdigest()
def need(b,m):
 if not b:raise RuntimeError(m)
need(t['exit']==0 and t['reason'] is None,'exit')
need(sha(P/'run-threeexcluded-v2.py')==t['runner_sha256'] and sha(s)==t['inputs'][str(s)]==sha(o/'source.txt')==sha(root/s.name),'source/runner')
need(sha(root/'Trace75ThreeExcluded.olean')==t['object_sha256']=='8846a1b0774206168399b693decd4ac80688271928caac534eb36dcf82b9794a','object')
for p,h in t['inputs'].items():need(sha(p)==h,'pin '+p)
need(sha(o/'stdout')==t['stdout_sha256'] and sha(o/'stderr')==t['stderr_sha256'],'logs')
need((o/'stdout').read_text()=="'Trace75ThreeExcluded.main_three_impossible' depends on axioms: [propext, Classical.choice, Quot.sound]\n" and (o/'stderr').read_text()=='','report')
need(not re.search(r'\b(?:sorry|admit)\b',s.read_text()),'placeholder')
imports=re.findall(r'^import\s+([\w.]+)\s*$',s.read_text(),re.M);need(imports==['Trace75ThreeTwo','Trace75ThreeGap'],'direct imports')
mods=imports+['Trace75ThreeBinding','Trace75Index','Trace75ThreeLarge','Trace75Fold','Trace75Pell','PellRecovery','PellOddFold','PellFold','DiophantineConsistency.ArithmeticPellFirstNorm'];selected=[]
for m in mods:
 rel=m.replace('.','/')+'.olean';p=next((pathlib.Path(x)/rel for x in t['lean_path'].split(':') if (pathlib.Path(x)/rel).is_file()),None)
 need(p is not None,'selection '+m)
 pin=any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in t['inputs'].items())
 if m!='DiophantineConsistency.ArithmeticPellFirstNorm':need(pin,'unpinned '+m)
 else:
  old=json.loads((P/'observations/pell-attempt01/terminal.json').read_text());need(not pin and any(pathlib.Path(q).resolve()==p.resolve() and h==sha(p) for q,h in old['inputs'].items()),'firstnorm previous pin')
 selected.append({'module':m,'path':str(p),'resolved_path':str(p.resolve()),'sha256':sha(p),'direct':m in imports,'pinned_here':pin})
need(selected[0]['sha256']=='c6526cbc36bbc37365527ea028d25e46e514bca5461ef2a803e3d489725f7053' and selected[1]['sha256']=='3f25660d7a2263e82d60dbdea5815063a74bf29fcdabc3e8dc3c976f6d1a1850','direct providers')
need(json.loads((P/'observations/threeexcluded-attempt01/terminal.json').read_text())['exit']!=0,'first failed')
print(json.dumps({'status':'PASS','object_sha256':t['object_sha256'],'selected':selected,'lean_replayed':False},indent=2,sort_keys=True))
