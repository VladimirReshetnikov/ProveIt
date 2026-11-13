#!/usr/bin/env python3
"""Bounded actual-main graph/algebra controls; no Lean verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-main-congruence-model-draft/ResidueMainCongruence.lean.src': 'c92cbbca34371870b01f03042de0a4a024bd56a6175d909c43b6887736700ce8', 'research/ordinary13-residue-first-index-model-draft/ResidueFirstIndexModel.lean.src': '0b69fb042a913232ef9f4a92757107f60d8a590f855176134587939012b1b93b', 'research/ordinary13-residue-first-index-model-draft/check.py': '326f626d2d09dc43ba08c11849e912a5fe8830f7e85729b58d0f94f1493ebf20', 'research/ordinary13-residue-first-index-model-draft/receipt.json': '0a6fa5d8a83af0132714f600742bccc91c78f9a3e65fe96b0aef3cae0ea9ef1b', 'research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src': '8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d', 'research/ordinary13-residue90-xzero-graph-draft/check.py': '7774ef7cb20917e48a421fc40e438a70a8a5b07a71912a3a46fd24011c0a6713', 'research/ordinary13-residue90-xzero-graph-draft/receipt.json': '5935ede63713efe63f0d32d907a8ded2689cb9438e8df256a383fc4ee5629004', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-residue90-norm-model-draft/Residue90SignedNorms.lean.src': 'f0f7b2af039ed45c19cb45170d8f6bed601451f794d871b7b21c818fd1cac70a', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'Lean/DiophantineConsistency/Compact44/FreeJMainOrientation.lean': 'd02beb02122e682deef3e89c3dcb8e3e6aea31ddfbc4f320fe6af9a3df7f9a6b', 'Lean/DiophantineConsistency/Compact44/DirectMainNorm.lean': '29c748582368b4ab2bcdb4b4cdd4f7890dda32f77718e33355b590b8f07b7fbd'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue-first-index-model-draft','ordinary13-residue90-xzero-graph-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
s=(P/'ResidueMainCongruence.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['main_pair_identity','actual_main_magnitude_norm','arithmetic_congruence_of_balance','rank_congruence_of_actual_main','early_index_of_actual_graph','rank p v+v 6*Y p v*q p v','DirectMainNorm.direct_main_orientation','FreeJMainOrientation.rank_congruence_from_main']:
 assert x in s,x
assert 'core.z' not in s.split('theorem main_pair_identity',1)[1]
j=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());rng=random.Random(139012);cases=0
for _ in range(200):
 v=[rng.randrange(0,5) for _ in range(13)];v[0]=rng.randrange(1,5);v[1]=0;v[2]=0;p=[rng.randrange(2,6),rng.randrange(0,5),rng.randrange(0,5),rng.randrange(0,5)]
 env=dict(zip(j['witnesses'],v));env.update(zip(j['fixed_numerals'],p))
 for n,o,x,y in j['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 q=1+v[0]*p[0];ss=v[7]+1;Y=q**3*ss;X=v[6];kk=(v[9]+1)+(v[10]+1);aa=X*Y+Y;cc=v[9]+1+Y*kk;H=3+4*aa;U=Y*q*q;F=v[1]+1;alpha=v[2]+1
 R=((q-1)*(q-F)+alpha)*(q*q-1)+(p[2]+q*p[3])*v[0]
 PP=U*(X+aa*cc)+H*(U*v[12]+(R+X*Y*q)+1);NN=H*kk
 assert env['Dstar']==PP-NN and env['R']==R and U==q**5*ss
 main=rng.randrange(0,7)
 lhs=H*(X*Y*q+R+1)+q**5*(ss*(X+aa*cc+H*v[12]));rhs=H*kk+q**5*(ss*main)
 assert lhs-rhs==PP-NN-U*main
 cases+=1
print(json.dumps({'scope':'bounded actual-main source/algebra controls, no Lean','pinned_files':len(pins),'finite_graph_cases':cases,'adjusted_rank_term_checked':True,'graph_port_provider_and_later_index_obligations_open':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
