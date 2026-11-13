#!/usr/bin/env python3
"""Independent bounded source, rank, and graph factor checks; no Lean."""
from pathlib import Path
from hashlib import sha256
import json,random,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
p=Path('research/ordinary13-eta-natural-graph-strong-aux-model-draft')
fs=[p/'EtaNaturalGraphStrongAux.lean.src',p/'README.md',p/'check.py',p/'pins.json',p/'receipt.json',
Path('research/ordinary13-eta-zero-graph-adapter-audit/prototype.json'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitGraph.lean.src'),
Path('research/ordinary13-eta-natural-unit-norm-bridge-draft/EtaNaturalUnitBridge.lean.src'),
Path('research/ordinary13-eta-natural-graph-norm-model-draft/EtaNaturalGraphNorms.lean.src'),
Path('research/ordinary13-eta-natural-gap-rank-model-draft/EtaNaturalGapRank.lean.src'),
Path('research/ordinary13-eta-natural-strong-aux-adapter-draft/EtaNaturalStrongAux.lean.src'),
Path('research/ordinary13-eta-zero-index-parity-contradiction-draft/EtaZeroIndexParity.lean.src')]
s=[f.read_text() for f in fs]
for x in ['theorem field_f','theorem field_y','theorem field_I','theorem field_ordinate',
 '(hFq : v 1+1≤q p v)','rank_representation p v hFq','theorem ordinary_strong',
 'theorem direct_auxiliary','theorem index_hypotheses_of_geometry',
 'ordinary_strong_of_signed','f_positive_of_strong','strict_bounds_of_strong','index_aux_of_direct']:
 assert x in s[0],x
for x in ['theorem ordinary_strong_of_signed','theorem f_positive_of_strong',
 'theorem strict_bounds_of_strong','theorem index_aux_of_direct','(hc : 1<c)',
 '(hDelta : 0<Delta)','(hsmall : Delta<c*c*c)']:
 assert x in s[10],x
assert '(hs\' :' in s[11] and '(haux :' in s[11]
G=json.loads(s[5]); assert G['witnesses'][3:6]==['n_f','n_i','n_T'] and G['witnesses'][11]=='n_y'
rng=random.Random(79344);count=eta_zero=signed_negative=0
for t in range(1200):
 v={key:rng.randrange(0,7) for key in G['witnesses']+G['fixed_numerals']}
 if t%2==0:v['n_eta']=0
 e=v.copy()
 for name,op,l,r in G['source']:
  x=l if isinstance(l,int) else e[l];y=r if isinstance(r,int) else e[r]
  e[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 q=e['q'];F=e['F']
 if F>q:continue
 J=v['n_J'];f=v['n_f'];i=v['n_i']+1;T=v['n_T']+1;y=v['n_y']
 X=q*v['n_w'];Y=q**3*(v['n_s']+1);k=v['n_eta']+v['n_zeta']+1;c=v['n_eta']+Y*k
 a=X*Y+Y;D=3+4*a+a*a
 R=((q-1)*(q-F)+(v['n_alpha']+1))*(q*q-1)+(v['MC']+q*v['MF'])*J
 z=f*f*(T*c-R)-c;A=f*f*T*c;B=f*f*R+c
 assert e['c']==c and e['Delta']==D and e['I']==c*c*i and e['R']==R
 assert e['V']==z==A-B and e['n_f']==f and e['n_y']==y
 assert e['g72']==(i*c*c)**2+D-D*f*f
 assert e['Fa']==y*y-D*(f*f-1)*(y*y-z*z)
 eta_zero+=v['n_eta']==0;signed_negative+=z<0;count+=1
assert count>100 and eta_zero>20 and signed_negative>0
assert subprocess.run([sys.executable,'-I','-S','-B',str(p/'check.py')],capture_output=True,check=True).stdout==fs[4].read_bytes()
print(json.dumps({'sha256':{str(f):sha256(f.read_bytes()).hexdigest() for f in fs},
 'represented_natural_rank_graph_controls':count,'eta_zero_controls':eta_zero,
 'negative_signed_ordinate_controls':signed_negative,'author_receipt_reproduced':True,
 'lean_executed':False,'result':'no concrete mismatch found; source and finite control only'},sort_keys=True,indent=2))
