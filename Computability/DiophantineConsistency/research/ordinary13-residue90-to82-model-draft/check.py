#!/usr/bin/env python3
"""Read-only exact row substitution and finite source checks; no Lean."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-to82-model-draft/Residue82Literal.lean.src': 'fa20dbc55a71afe4168864237eaab5ec22b31a1f558d1bc70c9b17bcbc657295', 'research/ordinary13-residue90-to82-model-draft/Residue82Residuals.lean.src': 'ef8ffe28d4d80fd1448ee87817d5eb3c2ee8e7bd0c403d4bb050272cce6f80ff', 'research/ordinary13-residue90-to82-model-draft/Residue90To82Transport.lean.src': 'bd8ac5e52ff1e82b732b0a0bbeebce88b5d39629a5695aceee5e9a4565436e83', 'research/ordinary13-residue90-to82-model-draft/generate.py': '502f85558401a8f90f2ba8216ec564935a1235004231d6c322e1d0dc6f5d651d', 'research/ordinary13-residue90-to82-model-draft/generated.json': '791ea4a5e93bd82d324a2becd54436578aeebd3a4c87227dbee7e733ea1bdb7a', 'research/ordinary13-residue90-to82-model-draft/generate_transport.py': '49a18268c0c91b3a8501a95949373ae583b159719de6df72e66342ee0d31cdb8', 'research/ordinary13-residue90-to82-model-draft/transport-generated.json': '63ac821de1f2bdf30a69a4026f7ec0a665f99a7d1d0e1aa86f30e2c6d9f72a1b', 'research/ordinary13-residue90-fy-model-draft/Residue90FyForce.lean.src': '1d4bd8b0f99b20a5796fe04f1ff0c4f5a825af65b1ba548a79aa0c0940a6e21a', 'research/ordinary13-residue90-fy-model-draft/check.py': 'dea3f83f6e516367e5ea6403be5f18639edae1de56acf7bf716667282731cf69', 'research/ordinary13-residue90-fy-model-draft/receipt.json': '06a116dee14ac52c48ef0e979cafa00502f7c875279c42b9decf13e3cac70e12', 'research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src': '8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d', 'research/ordinary13-residue90-norm-model-draft/Residue90Literal.lean.src': '00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af', 'research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src': 'efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'research/ordinary13-residue-first82/candidate.json': 'bb90faa3815c5ff46f5fdbf41c2d001790d565baa17d97c79514c33fa928f1d2', 'research/ordinary13-residue-first82/check.py': 'bfaa266b2deb25ba2e02c1117f83289294d8baa19470a08f7ac5484db2cb3a5b', 'research/ordinary13-residue-first82/result.json': 'd2961329d5b4b4f24750577a8e2e09b28656b2dfcb02170190af71c8ee9ee469'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-residue90-to82-model-draft','generate.py','generated.json'),('ordinary13-residue90-to82-model-draft','generate_transport.py','transport-generated.json'),('ordinary13-residue90-fy-model-draft','check.py','receipt.json'),('ordinary13-residue-first82','check.py','result.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==3
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
r=src['Residue82Residuals.lean.src'];m=re.findall(r'^  !\[([^\n]+)\]$',r,re.M);assert ': Fin 4 → Expr (Fin 13)' in r and len(m)==1 and m[0].split(',')==['A0','A1','Fam','g72']
t=src['Residue90To82Transport.lean.src'];assert sorted(re.findall(r'^theorem relation(\d\d)',t,re.M))==['00','01','02','03']
for x in ['forced_pos','mixed_lower','f_y_positive','compact_gamma_positive','hparent : PolynomialBridge']:
 assert x in t,x
parent=json.loads((D/'research/ordinary13-residue-first82/candidate.json').read_text());child=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());forced={'J','f','X','y','gamma'}
assert child['forced_unshifted']==sorted(forced) and child['witnesses']==['n_'+x for x in parent['witnesses']]
shifted={x:'shift_'+x for x in parent['witnesses'] if x not in forced};rename={x:'n_'+x for x in parent['witnesses']}
def rep(x):return shifted.get(x,rename.get(x,x)) if isinstance(x,str) else x
expect=[['shift_'+x,'+','n_'+x,1] for x in parent['witnesses'] if x not in forced]+[[n,o,rep(a),rep(b)] for n,o,a,b in parent['source']]
assert expect==child['source']
def ev(g,v,p):
 env=dict(zip(g['witnesses'],v));env.update(zip(g['fixed_numerals'],p))
 for n,o,x,y in g['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 return [env[z] for z in ('A0','A1','Fam','g72','out')]
rng=random.Random(139082);cases=0
for _ in range(200):
 v=[rng.randrange(-5,6) for _ in range(13)];pp=[rng.randrange(-5,6) for _ in range(4)];mixed=[x if name in forced else x+1 for name,x in zip(parent['witnesses'],v)]
 assert ev(child,v,pp)==ev(parent,mixed,pp);cases+=1
print(json.dumps({'scope':'exact mixed row edit and bounded controls, no Lean','pinned_files':len(pins),'finite_signed_graph_cases':cases,'forced_indices':[0,3,6,11,12],'parent_bridge_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
