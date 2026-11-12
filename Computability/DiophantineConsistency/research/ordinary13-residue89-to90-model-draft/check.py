#!/usr/bin/env python3
"""Read-only row edit/source and finite graph controls; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue89-to90-model-draft/Residue89RootSwitchTransport.lean.src': 'f0d0607cd42e6d1226ee498686dd134819cfdbf50f895f27629cb98e09d94c4a', 'research/ordinary13-residue89-to90-model-draft/Residue89To90Transport.lean.src': '8cdbb1809435b9eb09fa930db4e1e13c112ba459aa93d4338d73af2cbf94b0fe', 'research/ordinary13-residue89-to90-model-draft/generate.py': '99fde52e6f6581f3d5359cad177be19e53229bb689eff394949046b89083b963', 'research/ordinary13-residue89-to90-model-draft/generated.json': '040024350b02c4c2ba558a86d8a5890961d5f32c88e16daedd4a01012351979c', 'research/ordinary13-residue90-to82-model-draft/Residue90To82Transport.lean.src': 'bd8ac5e52ff1e82b732b0a0bbeebce88b5d39629a5695aceee5e9a4565436e83', 'research/ordinary13-residue90-to82-model-draft/check.py': '0e84f1ba35e762c0f33213ad9b982fb6771d1ce52bf1a21e313df1c31b68bdfe', 'research/ordinary13-residue90-to82-model-draft/receipt.json': '03a911d8adcd840c5458531650c16a19b25bf86368f2524441e2155f6817f2f0', 'research/ordinary13-residue-folds-model-draft/ResidueFoldP89.lean.src': '1cf3ece1241b09402110f78d7be1712b508e431c763772af5a0f6e91d3bb2a73', 'research/ordinary13-residue-folds-model-draft/ResidueFoldP89Residuals.lean.src': '02849926cb905aa822f0c077329ddef012c8058184ffd719a62c5350a24717c4', 'research/ordinary13-residue89-r-model-draft/Residue89RArithmetic.lean.src': 'be421b34e6701a194c3f68806a06099e373d2d64fba4bda9134fafd0460748aa', 'research/ordinary13-residue89-r-model-draft/check.py': 'a14ca99e0e39e463b29660fe308559b463e0fe7d925dd6b60195ab8d51340ac1', 'research/ordinary13-residue89-r-model-draft/receipt.json': 'bd4ee8b52dd71295f2b48a5f9d42da103b63269f62c38ccdc15ca7de548dacb3', 'research/ordinary13-residue-root-switch-model-draft/ResidueRootSwitchArithmetic.lean.src': 'c9adec7548db6d9f1dd2e633e109ccb52b2ccc73490b31bd60bd7d7ae363de13', 'research/ordinary13-residue-root-switch-model-draft/check.py': '2259104f91ca92802a5caca028a573f50880526b6a51030f3d6cd2980e77b31d', 'research/ordinary13-residue-root-switch-model-draft/receipt.json': '46276b017358f08988b62178bc74514b69d3a6bd99ae623985b30158a8ff24b1', 'research/ordinary13-natural-residue-forced89-degree56/candidate.json': 'c18892fc5e50e091411cf24511481995ad2fdbab20e55068787722feca41a22a', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-residue89-to90-model-draft','generate.py','generated.json'),('ordinary13-residue90-to82-model-draft','check.py','receipt.json'),('ordinary13-residue89-r-model-draft','check.py','receipt.json'),('ordinary13-residue-root-switch-model-draft','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==2
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
t=src['Residue89To90Transport.lean.src'];r=src['Residue89RootSwitchTransport.lean.src']
assert sorted(re.findall(r'^theorem relation(\d\d)',t,re.M))==['00','01','02','03']
for x in ['def ForcedR','h82 : PolynomialBridge','compact_no_zero_iff']:
 assert x in t,x
for x in ['def PositiveReplacement','∃ w : Fin 13','forced_implies_replacement','h82 : PolynomialBridge']:
 assert x in r,x
p=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());c=json.loads((D/'research/ordinary13-natural-residue-forced89-degree56/candidate.json').read_text())
assert p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals']
rows=[]
for row in p['source']:
 if row[0]=='shift_r':continue
 n,o,a,b=row;rows.append([n,o,'n_r' if a=='shift_r' else a,'n_r' if b=='shift_r' else b])
assert rows==c['source']
def ev(g,v,p):
 env=dict(zip(g['witnesses'],v));env.update(zip(g['fixed_numerals'],p))
 for n,o,x,y in g['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 return [env[z] for z in ('A0','A1','Fam','g72','out')]
rng=random.Random(138990);cases=0
for _ in range(200):
 v=[rng.randrange(-5,6) for _ in range(13)];pp=[rng.randrange(-5,6) for _ in range(4)];w=v.copy();w[8]+=1
 assert ev(p,v,pp)==ev(c,w,pp);cases+=1
print(json.dumps({'scope':'exact r-shift row edit and bounded controls, no Lean','pinned_files':len(pins),'finite_signed_graph_cases':cases,'strong_forced_and_weak_existential_interfaces_explicit':True,'parent_82_bridge_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
