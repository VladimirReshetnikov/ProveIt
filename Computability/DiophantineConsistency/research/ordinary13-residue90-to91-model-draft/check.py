#!/usr/bin/env python3
"""Bounded source, exact row edit and finite graph controls; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-to91-model-draft/Residue90To91Transport.lean.src': 'f11b374e46e2c8347a55ddc6f7c43cd60af88b9465aec6160fb0f1834ae1121b', 'research/ordinary13-residue90-to91-model-draft/Residue91Literal.lean.src': '93c7c115fb28aebc97899ec166ccf6b013a778df628619bfed72a3a2afd536de', 'research/ordinary13-residue90-to91-model-draft/Residue91Residuals.lean.src': 'c812879f3c7057b272eac00d0e2b251e64e471560e0217296b71a4bc05218c98', 'research/ordinary13-residue90-to91-model-draft/generate.py': 'f2c8da4055ec7052ba4f0eb5aa9281e2a559a69fba4002c033395e6dafeed870', 'research/ordinary13-residue90-to91-model-draft/generated.json': 'd49067d240cbdc949efc2ecdadf139f24ebf0ea2568179245999fe7ff596efe3', 'research/ordinary13-residue90-to91-model-draft/generate_transport.py': '5070c41e0948790eee3394b55d89099cceaf7a798ebaf496093435d5a80dbd6f', 'research/ordinary13-residue90-to91-model-draft/transport-generated.json': '5f7333a9cd8a13f47fa961316b5fcdff5e70bd85d0672c25d1757dec36416cd7', 'research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src': '8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d', 'research/ordinary13-residue90-xzero-graph-draft/check.py': '7774ef7cb20917e48a421fc40e438a70a8a5b07a71912a3a46fd24011c0a6713', 'research/ordinary13-residue90-xzero-graph-draft/receipt.json': '5935ede63713efe63f0d32d907a8ded2689cb9438e8df256a383fc4ee5629004', 'research/ordinary13-residue90-norm-model-draft/Residue90Literal.lean.src': '00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af', 'research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src': 'efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'research/ordinary13-natural-residue-forced91-degree56/candidate.json': 'b5318de6a5bb49faf1ba764408dc618cfedc4d4f42281dcbda72f8cd846e7170', 'research/ordinary13-natural-residue-forced91-degree56/check.py': '239e61b0de20457aaa431f5900a33748b08eca68149b0ca7387ed063b466850f', 'research/ordinary13-natural-residue-forced91-degree56/receipt.json': '8b1549e4ee0d3b61d969468bac8704a03c402d829c9c6e6ca4e22e4638fd3f51'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-residue90-to91-model-draft','generate.py','generated.json'),('ordinary13-residue90-to91-model-draft','generate_transport.py','transport-generated.json'),('ordinary13-residue90-xzero-graph-draft','check.py','receipt.json'),('ordinary13-natural-residue-forced91-degree56','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==3
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
r=src['Residue91Residuals.lean.src'];m=re.findall(r'^  !\[([^\n]+)\]$',r,re.M);assert ': Fin 4 → Expr (Fin 13)' in r and len(m)==1 and m[0].split(',')==['A0','A1','Fam','g72']
t=src['Residue90To91Transport.lean.src'];assert sorted(re.findall(r'^theorem relation(\d\d)',t,re.M))==['00','01','02','03']
for x in ['raiseGamma','lowerGamma','compact_gamma_positive','hparent : PolynomialBridge']:
 assert x in t,x
p=json.loads((D/'research/ordinary13-natural-residue-forced91-degree56/candidate.json').read_text());c=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text())
assert p['witnesses']==c['witnesses'] and p['fixed_numerals']==c['fixed_numerals']
rows=[]
for row in p['source']:
 if row[0]=='shift_gamma':continue
 n,o,a,b=row;rows.append([n,o,'n_gamma' if a=='shift_gamma' else a,'n_gamma' if b=='shift_gamma' else b])
assert rows==c['source']
rng=random.Random(139091);cases=0
def ev(g,v,p):
 env=dict(zip(g['witnesses'],v));env.update(zip(g['fixed_numerals'],p))
 for n,o,x,y in g['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 return [env[z] for z in ('A0','A1','Fam','g72','out')]
for _ in range(200):
 v=[rng.randrange(-5,6) for _ in range(13)];pp=[rng.randrange(-5,6) for _ in range(4)];w=v.copy();w[12]+=1
 assert ev(p,v,pp)==ev(c,w,pp);cases+=1
print(json.dumps({'scope':'exact row edit and bounded controls, no Lean','pinned_files':len(pins),'finite_signed_graph_cases':cases,'residual_relations':4,'parent_bridge_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
