#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
d=Path(__file__).resolve().parents[2];p=d/'research/nine-sharing-sign33-first-cut-retry01';old=d/'research/nine-sharing-sign33-first-cut-check'
def h(q):return hashlib.sha256(q.read_bytes()).hexdigest()
for n,v in {'run.py':'4fe3b6a48e13c12594c51d377f1f9c0eccb619de6852a129063e6aca830a37c8','provider_survey.py':'60b66763bd24df531a7191a914fff34f43f0f3d5b77739e65eb03aedf9de74ba','source-manifest.json':'6d443b7d1dc5d002feca9bcd4a4eb0bd0e5d31b35360361505282982b11830b1','src/DiophantineConsistency/Sign33FirstCut.lean':'57cc9442200276eb3e15fb659ea4a729f213e22f1ab17e7402136a7ad8f4e962'}.items():assert h(p/n)==v
a=(old/'src/DiophantineConsistency/Sign33FirstCut.lean').read_text();b=(p/'src/DiophantineConsistency/Sign33FirstCut.lean').read_text();assert a.count('(List.mem_cons_self _ _)')==1 and a.replace('(List.mem_cons_self _ _)','(List.mem_cons_self)')==b
r=subprocess.run([sys.executable,'-I','-S','-B',str(p/'run.py'),'--preflight'],capture_output=True,text=True,check=True);o=json.loads(r.stdout);assert o['status']=='PASS_NO_LEAN_PREFLIGHT' and o['stage_count']==1
print(json.dumps({'status':'PASS','preflight':o,'scope':'single membership proof repair; no Lean replay'},sort_keys=True,indent=2))
