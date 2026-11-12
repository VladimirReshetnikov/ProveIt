#!/usr/bin/env python3
"""Read-only graph/wiring and bounded ring controls, not a Lean check."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-norm-model-draft/Residue90CompactPortBounds.lean.src': '11ba8e4e01d29b956926a26b04815d5a660b79caabfce7b8cc1ce6d5c85d615a', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphGamma.lean.src': '1260994075d32f7ba5f927c1444ee8ad9c954134ec0f563185c3e2b846a52d5b', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-residue90-norm-model-draft/Residue90Literal.lean.src': '00ec512e2f9069bafd06edb3cf1cb86a7bd3ca2656b6d67a840981294d1b69af', 'research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src': 'efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925', 'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src': 'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a', 'research/ordinary13-residue90-norm-model-draft/generate.py': '8afe9c14fd5a52580638f21fb546142bcf3ac40f66e9f01527f6361f22eb81f9', 'research/ordinary13-residue90-norm-model-draft/generated.json': 'c92f8bea4d10368c9f5fe1a95b6edebaa4d077f2897da6082d3ce589139dbc8e', 'research/ordinary13-residue90-gamma-model-draft/Residue90GammaModel.lean.src': '7a9f8a98e28bad9f94a8dccdab57d16753058f7eb55144fb5282f51a19314af7', 'research/ordinary13-residue90-gamma-model-draft/check.py': 'd079ff75ee08682fcd2a01cbe9bf520a46e8440f98944e4d49a39d32f66f20fa', 'research/ordinary13-residue90-gamma-model-draft/receipt.json': '956af5033043daa00444ccdecbc2a639be6728d39842e559062be9ec274ea5ef', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'research/ordinary13-natural-residue-forced90-degree56/check.py': '5f55c54a80c510b7862d5459c2ffddab585d18904d9b6d66c6a0fd0446195b5c', 'research/ordinary13-natural-residue-forced90-degree56/receipt.json': '81187a393eefdd7936c8bc9a1c4ad501c171b1e9ba01fd720ac8a06815d11efc', 'Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean': 'c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c', 'Lean/DiophantineConsistency/Compact44/P72Root.lean': '066fce52d35ab720519ee8817d9b56c2eacc9ac4f6bb7bf6e92286a87f44d091', 'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean': 'bcb892e7ae6b0d3cf329a248ca6b468e36a9a1b582d75cacafb7fd49f89025ea', 'Lean/DiophantineConsistency/Compact44/CompactSymbolicPorts.lean': '0fc8eb4f60e801b38a3a516cd23d9f44c1e9eda62609d34bd76764de7ac51414', 'Lean/DiophantineConsistency/ArithmeticAdaptiveQuotients2011.lean': '40070b23fceee62a689a1002f97f6f612057634b5bd8472949f0d2dcab136884', 'Lean/DiophantineConsistency/ArithmeticAdaptiveRankWindow2011.lean': '0895f6e74b29c2cc2e4542d739b238352778750da62766819caeb105995fb794'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet,check,receipt in [('ordinary13-residue90-norm-model-draft','generate.py','generated.json'),('ordinary13-residue90-gamma-model-draft','check.py','receipt.json'),('ordinary13-natural-residue-forced90-degree56','check.py','receipt.json')]:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/check)],cwd=D)==(p/receipt).read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==6
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
r=src['Residue90Residuals.lean.src'];m=re.findall(r'^  !\[([^\n]+)\]$',r,re.M)
assert ': Fin 4 → Expr (Fin 13)' in r and len(m)==1 and m[0].split(',')==['A0','A1','Fam','g72']
a=src['Residue90SignedNorms.lean.src'];g=src['Residue90GraphNorms.lean.src'];c=src['Residue90CompactPortBounds.lean.src'];e=src['Residue90GraphGamma.lean.src']
for x in ['natural_magnitude_square','scaled_quotient','ι_magnitude_sq','first_natural_norm','main_natural_norm']:
 assert x in a,x
for x in ['all_residuals_zero','first_ring_norm','rank_representation','main_ring_norm_at_zero','v 12=0']:
 assert x in g,x
for x in ['CompactFixedBeta.bounds','scalar_rank_window','(hgap : F+alpha<q)']:
 assert x in c,x
for x in ['gamma_positive_of_graph_facts','(hb :','(hU :','(hY :','(hR :','first_ring_norm','main_ring_norm_at_zero']:
 assert x in e,x
j=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text())
rng=random.Random(1790);cases=0
for trial in range(80):
 v=[rng.randrange(0,5) for _ in range(13)];v[0]=rng.randrange(1,5);v[1]=0;v[2]=0;v[12]=0
 ports=[rng.randrange(2,6),rng.randrange(0,5),rng.randrange(0,4),rng.randrange(0,5)]
 env=dict(zip(j['witnesses'],v));env.update(zip(j['fixed_numerals'],ports))
 for n,o,x,y in j['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 b=v[0]*ports[0];q=1+b;Y=q*q*q*(v[7]+1);kk=(v[9]+1)+(v[10]+1);mm=v[6]*Y*Y
 F=v[1]+1;alpha=v[2]+1;C=q-F-alpha;Bt=C*(v[6]+ports[1])-F;ell=mm*kk
 z=b*(ell+kk+(v[8]+1)-kk*Bt)-Bt
 assert env['A0']==z*z-b*b*(1+mm*(mm+1)*kk*kk)
 R=((q-1)*(q-F)+alpha)*(q*q-1)+(ports[2]+q*ports[3])*v[0]
 assert env['R']==R
 aa=v[6]*Y+Y;H=3+4*aa;delta=H+aa*aa;cc=(v[9]+1)+Y*kk;U=Y*q*q
 PP=U*(v[6]+aa*cc)+H*(R+v[6]*Y*q+1);NN=H*kk
 assert env['A1']==(PP-NN)**2-U*U*(1+delta*cc*cc)
 cases+=1
print(json.dumps({'scope':'bounded source and graph/ring controls; no Lean','pinned_files':len(pins),'source_files':len(src),'finite_graph_cases':cases,'graph_first_and_gamma_zero_main_checked_on_samples':True,'graph_positivity_and_compact_binding_obligations_explicit':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
