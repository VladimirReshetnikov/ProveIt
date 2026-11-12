#!/usr/bin/env python3
"""Inspect literal main-pair source and finite ring controls without Lean."""
from pathlib import Path
import hashlib,json,random
P=Path(__file__).resolve().parent;D=P.parents[1]
pins={
 P/'Natural80MainPairs.lean':'22350958652773aa4f900c69e99b0891b4811168d70c479a4c463bb0924028c0',
 D/'research/ordinary14-natural80-guard-gap-draft/Natural80GuardGap.lean':'df59908f11990a28b4b788d0014757a897f2bdc1a4011772e0e825397cad43eb',
 D/'research/ordinary14-natural80-ownzero-norm-draft/Natural80OwnZeroNorm.lean':'670f8a6e7208afccde1051d72b3154990e1347cbf8d51a3845a89f56f81fcb74',
 D/'research/ordinary14-pair-eval-ring-bridge-draft/PairEvalRingBridge.lean':'0fdb641db2008362ae3ec363bea66f6b4a4b475c1de2d5d00b7c1e9a81adc510',
 D/'research/ordinary14-positive-guard74/candidate.json':'e70af4f896013695368180743f514c027faa86f8b3cedd5479b22e64e4c26093',
}
sources={}
for p,h in pins.items():
 b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==h,str(p);sources[p.name]=b.decode()
s=sources['Natural80MainPairs.lean']
for x in ('theorem rhs_eval','theorem rhs_rep','theorem root_eval','theorem root_rep',
          '(hgap : u 1+u 2<q beta u)', '(hMC : (p 2 : DiffRing V)=ι MC)',
          '(hMF : (p 3 : DiffRing V)=ι MF)','theorem norm_from_representations',
          'theorem norm_of_80_zero','units_of_80_zero','gap_of_80_zero',
          '#print axioms DiophantineConsistency.Natural80MainPairsDraft.rhs_rep',
          '#print axioms DiophantineConsistency.Natural80MainPairsDraft.root_rep',
          '#print axioms DiophantineConsistency.Natural80MainPairsDraft.norm_of_80_zero'):
 assert x in s,x
assert 'sorry' not in s and 'admit' not in s
g=json.loads(sources['candidate.json']);rng=random.Random(148074)
def calc(v):
 e=v.copy()
 for n,op,x,y in g['source']:
  x=x if type(x) is int else e[x];y=y if type(y) is int else e[y]
  e[n]=x+y if op=='+' else x-y if op=='-' else x*y
 return e
zero_gamma=0
for i in range(500):
 beta=rng.randrange(2,8);J=rng.randrange(1,5);q=1+J*beta
 F=rng.randrange(1,q-1);alpha=rng.randrange(1,q-F)
 v={n:rng.randrange(0,5) for n in g['witnesses']}
 v.update({'J':J,'F':F,'alpha':alpha,'w':rng.randrange(1,5),'s':rng.randrange(1,5),
           'eta':rng.randrange(1,5),'zeta':rng.randrange(1,5),
           'gamma':0 if i%2==0 else rng.randrange(1,5),
           'beta':beta,'K0':rng.randrange(1,5),'MC':rng.randrange(0,5),'MF':rng.randrange(0,5)})
 assert F+alpha<q
 e=calc(v);b=J*beta;X=q*v['w'];Y=q**3*v['s'];U=Y*q*q;k=v['eta']+v['zeta']
 a=X*Y+Y;c=v['eta']+Y*k;H=3+4*a
 R=(alpha+(q-F)*b)*(q*q-1)+J*(v['MC']+v['MF']*q)
 pp=U*(X+a*c)+H*(U*v['gamma']+R+1);nn=H*k
 rhs=U*U*(1+(H+a*a)*c*c)
 assert e['R']==R and e['Dstar']==pp-nn and e['g65']==rhs
 zero_gamma+=v['gamma']==0
print(json.dumps({'scope':'unelaborated source and finite literal arithmetic controls only',
                  'represented_four_ports_explicit_at_own_zero':True,'guard_gap_explicit_at_root_cut':True,
                  'no_gamma_positivity_premise':True,'controls':500,'gamma_zero_controls':zero_gamma,
                  'axiom_print_commands_not_executed':3},sort_keys=True,indent=2))
