#!/usr/bin/env python3
"""Finite graph/source controls, not Lean verification."""
from pathlib import Path
import hashlib,json,re,subprocess,sys,random
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={'research/ordinary13-residue90-fy-model-draft/Residue90FyForce.lean.src': '1d4bd8b0f99b20a5796fe04f1ff0c4f5a825af65b1ba548a79aa0c0940a6e21a', 'research/ordinary13-residue90-xzero-graph-draft/Residue90XZeroGraph.lean.src': '8cf6259e9070171383ad8f18a886cee3bccabef43274a5719a2059b63f7c5a0d', 'research/ordinary13-residue90-xzero-graph-draft/check.py': '7774ef7cb20917e48a421fc40e438a70a8a5b07a71912a3a46fd24011c0a6713', 'research/ordinary13-residue90-xzero-graph-draft/receipt.json': '5935ede63713efe63f0d32d907a8ded2689cb9438e8df256a383fc4ee5629004', 'research/ordinary13-residue90-norm-model-draft/Residue90GraphNorms.lean.src': '422b2bf043181eacdaf047204eeed952ce36383afe84ee614999da4912ad6805', 'research/ordinary13-residue90-norm-model-draft/Residue90Residuals.lean.src': 'efc4bac39b680966c387f03d5a1f2df65899ee5b470adf0d9fbb769bd1069925', 'research/adaptive-aq17-forced105-model-draft/AQ17Forced105Arithmetic.lean.src': 'b3057437cfb476170b28114283783bb0bd392a28f1de1ba4a39b6bf264b5e330', 'research/ordinary13-natural-residue-forced90-degree56/candidate.json': 'e65b2aa417a94320aafc0f93b2ae5d30ec69ca1d401762668f0f13d1d431f946', 'Lean/DiophantineConsistency/Compact44/ReducedNormSigned.lean': 'c01a13fd7f48c5abeb8a6741e19adad7b9d848fc57d51057c8bbb4694139674c'}
for f,h in pins.items():assert hashlib.sha256((D/f).read_bytes()).hexdigest()==h,f
p=D/'research/ordinary13-residue90-xzero-graph-draft'
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')],cwd=D)==(p/'receipt.json').read_bytes()
s=(P/'Residue90FyForce.lean.src').read_text();assert not re.search(r'\b(?:sorry|admit|axiom|unsafe)\b',s)
for x in ['Qnat_at_least_four','strong_identity','auxiliary_identity','natural_magnitude_square','y_pos_of_zero_product','theorem f_y_positive']:
 assert x in s,x
j=json.loads((D/'research/ordinary13-natural-residue-forced90-degree56/candidate.json').read_text());rng=random.Random(139011);cases=0
for trial in range(250):
 v=[rng.randrange(0,7) for _ in range(13)];p=[rng.randrange(0,7) for _ in range(4)];env=dict(zip(j['witnesses'],v));env.update(zip(j['fixed_numerals'],p))
 for n,o,x,y in j['source']:
  a=x if type(x)==int else env[x];b=y if type(y)==int else env[y];env[n]={'+' : lambda:a+b,'-' : lambda:a-b,'*' : lambda:a*b}[o]()
 q=1+v[0]*p[0];Y=q*q*q*(v[7]+1);k=(v[9]+1)+(v[10]+1);c=(v[9]+1)+Y*k;a=v[6]*Y+Y;H=3+4*a;delta=H+a*a;I=c*c*(v[4]+1);Q=delta*(v[3]*v[3]-1)
 R=((v[2]+1)+(q-(v[1]+1))*(v[0]*p[0]))*(q*q-1)+v[0]*(p[2]+p[3]*q)
 Z=v[3]*v[3]*((v[5]+1)*c-R)-c
 assert I>=2 and env['g72']==I*I-Q and env['Fam']==v[11]*v[11]-Q*(v[11]*v[11]-Z*Z)-1
 cases+=1
print(json.dumps({'scope':'finite source and graph controls, no Lean','pinned_files':len(pins),'finite_graph_cases':cases,'strong_and_aux_identities_checked_on_samples':True,'source_sha256':hashlib.sha256(s.encode()).hexdigest()},sort_keys=True,indent=2))
