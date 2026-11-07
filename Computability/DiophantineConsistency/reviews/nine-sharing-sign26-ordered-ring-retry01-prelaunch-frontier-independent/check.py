#!/usr/bin/env python3
import hashlib,json,subprocess,sys
from pathlib import Path
D=Path(__file__).resolve().parents[2];P=D/'research/nine-sharing-sign26-ordered-ring-retry01';H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
for n,h in {'run.py':'1cbb8d74ad5656334289acdb47b67dda8f5d6e15ebab19a71e588056d8d33288','input-pins.json':'b875158725f89fd2700028a0f5e27c5ccf2884437117cef96426bb5c12ab3b1c','src/Sign26OrderedRing.lean':'62f7bfe8ecf03d54da4a870c8da0a2f6941e565c60f5f7dab6618fa5f64bb58f'}.items():assert H(P/n)==h
s=(P/'src/Sign26OrderedRing.lean').read_text();old=(D/'research/nine-sharing-sign26-ordered-ring-check/src/Sign26OrderedRing.lean').read_text();assert s==old.replace('import Mathlib.Tactic.Linarith\n','import Mathlib.Tactic.Linarith\nimport Mathlib.Tactic.Ring\n',1)
pins=json.loads((P/'input-pins.json').read_text());assert len(pins['direct_candidate_guard'])==80 and pins['modules']==['Init','Mathlib.Algebra.Order.Ring.Defs','Mathlib.Tactic.Linarith','Mathlib.Tactic.Ring']
up=D/'reviews/nine-sharing-sign26-ordered-ring-failure-frontier-independent/check.py';assert H(up)=='ee7f3fc8825d6eabda29a86fd835a1c1b2ef7565c235b9a597b032e00c429cd1';subprocess.run([sys.executable,'-I','-S','-B',str(up)],capture_output=True,check=True,timeout=120)
r=subprocess.run([sys.executable,'-I','-S','-B',str(P/'run.py'),'--preflight'],capture_output=True,text=True,check=True,timeout=120);j=json.loads(r.stdout);assert not r.stderr and j['status']=='PASS_NO_LEAN_PREFLIGHT' and j['guard_slots']==80
print(json.dumps({'status':'PASS_STATIC_AND_NO_LEAN_PREFLIGHT','scope':'sole source delta adds Mathlib.Tactic.Ring to failed generic lemmas; model hypotheses and representation remain unproved'},sort_keys=True,indent=2))
