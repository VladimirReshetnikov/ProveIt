#!/usr/bin/env python3
"""Bounded source/graph controls; no Lean verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue-aux-bounds-adapter-draft/ResidueAuxBoundsAdapter.lean.src': '4b6e7be4c6dd5aad302146018e304ae0fc8b523371b73c68707f02dfa8dd2e11', 'research/ordinary13-residue-aux-bounds-adapter-draft/ResidueExactIndexFromGraph.lean.src': '169c4e604a573fa1da69ca5d642d9d9de4b125515badb88f67b17f78b24601f1', 'research/ordinary13-residue-aux-witness-model-draft/ResidueAuxWitness.lean.src': '1037e3a296285ae16c221d5beeebdde89050ee2ce74acf9e6335ba11a1935a1e', 'research/ordinary13-residue-aux-witness-model-draft/check.py': 'f96cd4b6e68c32d48abb5fee80d802d2cc8e0709c8734030f67ea5c0d965fe35', 'research/ordinary13-residue-aux-witness-model-draft/receipt.json': 'c18aa9dedb91cc052068b98a2a868667a58fed984d61bef9b9be28951d7c4125', 'research/ordinary13-residue-exact-index-model-draft/ResidueExactIndexModel.lean.src': 'dc941fd8914795ac46f513f45979ef7c69c22a6d1be4dc332605f1ddb7a3a79a', 'research/ordinary13-residue-exact-index-model-draft/check.py': '9f9220d37a64a503d5c0a7804fcccbcaeebc729818f9c0cb0550227e145ba759', 'research/ordinary13-residue-exact-index-model-draft/receipt.json': 'db4dff7a02d19777927fd80f70093c36dc51b5f6d09409093d93918994857e81', 'research/ordinary13-residue-rank-lower-model-draft/ResidueRankLower.lean.src': '86fd995a873fedeeeaa79a2a476276870a4a1be26bfc0a273ce052600e941b2f', 'research/ordinary13-residue-rank-lower-model-draft/check.py': '8d27b89248f77ca67ccb00352954f9578f98318b4a5b70596cceb03cdf11c0ef', 'research/ordinary13-residue-rank-lower-model-draft/receipt.json': 'a92c2cd45412312d719338aaa64b0f14eaeeaed6e2da3ae6dc802ad97dc30209', 'research/ordinary14-natural81-combined-slim-overlay/source/NormsToBounds.lean.src': 'c93161930052792db7b9ebb08f04f897e70d70fa84d390926521b7b4e28a70f8', 'research/ordinary14-natural81-combined-slim-overlay/source/AuxRootBounds.lean.src': 'f7e198e882e31c67e915c0c7953f5a37c03e2c8c2ddb0a8c0043d2b8b71ca504', 'research/ordinary14-natural81-combined-slim-overlay/source/AuxGeometry.lean.src': '88de9d4d0e92e43ca9483dcb90ae96a7e16284e69b8384cd41c9e16a7ad87b77', 'research/ordinary14-natural81-combined-slim-overlay/source/MainSquareGap.lean.src': '6639167627e5cf01814d1ae48f3975d42a72a6451863b31c9795b427ec6c5e68', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
for packet in ['ordinary13-residue-aux-witness-model-draft','ordinary13-residue-exact-index-model-draft','ordinary13-residue-rank-lower-model-draft']:
 p=D/'research'/packet
 assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes(),packet
src={x.name:x.read_text() for x in P.glob('*.lean.src')};assert len(src)==2
for n,s in src.items():assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s),n
a=src['ResidueAuxBoundsAdapter.lean.src'];e=src['ResidueExactIndexFromGraph.lean.src']
for x in ['main_natural_of_graph','ordinate_square_large','aux_bounds_of_natural_norms','(hJ : 0<v 0)','(hbeta : 0<(p 0:V))','(hX : 0<v 6)','v 9+1','v 10+1','v 4+1']:
 assert x in a,x
for x in ['exact_indices_of_graph','old_aux_of_direct_graph','graph_rank_at_least_26','exact_indices_of_actual_graph','(hwindow :','(hgap :']:
 assert x in e,x
assert 'Bez' not in e and 'q ∣' not in e
j=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());rng=random.Random(139026);cases=0
for _ in range(200):
 v=[rng.randrange(0,6) for _ in range(13)];p=[rng.randrange(0,6) for _ in range(4)];env=dict(zip(j['witnesses'],v));env.update(zip(j['fixed_numerals'],p))
 for n,o,x,y in j['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 q=1+v[0]*p[0];Y=q**3*(v[7]+1);k=(v[9]+1)+(v[10]+1);c=v[9]+1+Y*k;a=v[6]*Y+Y;delta=3+4*a+a*a
 R=((v[2]+1)+(q-(v[1]+1))*(v[0]*p[0]))*(q*q-1)+v[0]*(p[2]+p[3]*q);z=v[3]*v[3]*((v[5]+1)*c-R)-c
 I=c*c*(v[4]+1);Q=delta*(v[3]*v[3]-1)
 assert env['V']==z and env['Delta']==delta and env['g72']==I*I-Q and (a+2)**2==delta+1
 assert z+c==v[3]*v[3]*((v[5]+1)*c-R) and v[9]+1>0 and v[10]+1>0 and v[4]+1>0
 cases+=1
print(json.dumps({'scope':'bounded actual-graph source controls, no Lean','pinned_files':len(pins),'source_files':len(src),'finite_graph_cases':cases,'shifted_eta_zeta_i_checked':True,'eta_zero_generalization_claimed':False,'rank_window_and_later_Bezout_open':True,'source_sha256':{n:hashlib.sha256(s.encode()).hexdigest() for n,s in sorted(src.items())}},sort_keys=True,indent=2))
