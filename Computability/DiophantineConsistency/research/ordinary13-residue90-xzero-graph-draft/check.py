#!/usr/bin/env python3
"""Bounded source and graph ring controls, not a Lean proof."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src': '8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d', 'research/ordinary13-residue90-xzero-model-draft/Residue90XZeroArithmetic.lean.src': '144b5447d8fde7f6384e3fb5ae8311bc051bf563190d204db3dad4810df5914b', 'research/ordinary13-residue90-xzero-model-draft/check.py': '619edda0d96d36a4af7e789ee7bddd1460ce336322d6fad3dbf1657c8d155df7', 'research/ordinary13-residue90-xzero-model-draft/receipt.json': 'e77b05aced2e3f36b8e76aaa1b446f2a7bc92f4bd8aedfbb0239d9b0c3cd454a', 'research/ordinary13-residue90-first-norm-J-draft/Residue90FirstNormJ.lean.src': 'ea7cdcfe04446f9d2fcf50849377e20959fda16df4cadafe7e5b07c1c5c815f6', 'research/ordinary13-residue90-first-norm-J-draft/check.py': 'e6b79a94166e54c2f2e9442c5a9824e610dc09e50c013922fcebd9d388b36e27', 'research/ordinary13-residue90-first-norm-J-draft/receipt.json': '031acc58613a6fd8121710115cba780d59879678449ab6a39d929be9f048aae5', 'research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src': 'efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-residue90-norm-model-draft/Residue90CompactGraphGamma.lean.src': '02c81eb303910d459890f3a001b8bdd65dccbe5f52e9bc05a24a6ddac383604b', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'Lean/DiophantineConsistency/ModelDifferenceRing.lean': '5f8007e437fe309d0801bed075c03dc7ef5e7cba0138210aa1805e43a0869998'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue90-xzero-model-draft','ordinary13-residue90-first-norm-J-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
s=(P/'Residue90XZeroGraph.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['def rankRing','def shiftRing','def mainRoot','theorem main_ring_norm','theorem X_positive','xzero_impossible','theorem compact_X_positive','theorem compact_gamma_positive']:
 assert x in s,x
j=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());rng=random.Random(139006);cases=0
for trial in range(200):
 v=[rng.randrange(0,7) for _ in range(13)];p=[rng.randrange(0,7) for _ in range(4)]
 env=dict(zip(j['witnesses'],v));env.update(zip(j['fixed_numerals'],p))
 for n,o,x,y in j['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 b=v[0]*p[0];q=1+b;Y=q*q*q*(v[7]+1);k=(v[9]+1)+(v[10]+1);c=(v[9]+1)+Y*k;a=v[6]*Y+Y;H=3+4*a;U=Y*q*q
 R=((v[2]+1)+(q-(v[1]+1))*b)*(q*q-1)+v[0]*(p[2]+p[3]*q)
 S=U*v[12]+v[6]*Y*q+R+1-k;Z=U*(v[6]+a*c)+H*S
 assert env['R']==R and env['shift']==S and env['Dstar']==Z
 assert env['A1']==Z*Z-U*U*(1+(H+a*a)*c*c)
 cases+=1
print(json.dumps({'scope':'bounded source and graph ring controls; no Lean','pinned_files':len(pins),'finite_graph_cases':cases,'signed_rank_and_main_identities_checked_on_samples':True,'authenticated_fixed_kernel_and_endpoint_claimed':False,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
