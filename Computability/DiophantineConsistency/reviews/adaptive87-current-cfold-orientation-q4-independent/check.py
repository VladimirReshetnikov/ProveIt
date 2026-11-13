#!/usr/bin/env python3
"""Independent exact-row and elementary-congruence controls; no Lean."""
import json,hashlib,math,random,subprocess,sys
from pathlib import Path
R=Path(__file__).resolve().parents[2];D=Path(__file__).resolve().parent
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
for f,h in json.loads((D/'pins.json').read_text()).items():assert hashlib.sha256((R/f).read_bytes()).hexdigest()==h,f
g=json.loads((R/'research/adaptive87-current-cfold88-degree28/graph.json').read_bytes()); rows={r[0]:r[1:] for r in g['source']}
# Include the first norm as well as the rank and main carrier on which the
# argument relies; omitted outputs are not certified by these checks.
need={'qm':['*','J','beta'],'q':['+',1,'qm'],'q2':['*','q','q'],'q3':['*','q','q2'],'M':['*','q3','qm'],'U':['*','Y','q2'],'qF':['-','q','F'],'C':['-','qF','alpha'],'E':['*','X','Y'],'k':['+','eta','zeta'],'kY':['*','Y','k'],'c':['+','eta','kY'],'c2':['*','c','c'],'ell':['*','E','kY'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],'g19':['*','a','c'],'b0':['+','X','g19'],'g25':['*','K0','q'],'g26':['+','X','g25'],'g27':['*','C','g26'],'g28':['*','F','q'],'Bt':['-','g27','g28'],'g30':['+','ell','k'],'g31':['+','g30','r'],'root_skew':['*','k','C'],'root_inner':['-','g31','root_skew'],'root_scaled':['*','M','root_inner'],'g33':['*','Y','qm'],'root_btq3':['*','Bt','q3'],'root_sum':['+','root_scaled','g33'],'Z':['-','root_sum','root_btq3'],'g38':['*','Z','Z'],'g39':['*','M','M'],'g40':['*','ell','g30'],'g41':['+',1,'g40'],'g42':['*','g39','g41'],'A0':['-','g38','g42'],'g44':['*','qF','qm'],'G':['+','alpha','g44'],'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],'g49':['+','MC','g48'],'g50':['*','J','g49'],'R':['+','g47','g50'],'g52':['-','k','R'],'r0':['-','g52',1],'g54':['*','U','gamma'],'g55':['*','E','q'],'g56':['+','g54','g55'],'shift':['-','g56','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65']}
assert all(rows[n]==v for n,v in need.items())
# Test q-divisible-by-three and coprime cases, including high powers of 3.
cases=0
for q in range(3,101):
 for s in range(1,5):
  for X in range(1,5):
   Y=q**3*s; H=3+4*Y*(X+1); h=math.gcd(H,q**5)
   assert h==math.gcd(3,q) and q%h==0
   if q%3==0:assert H%9==3
   d=q**5//h
   assert d%(q**4)==0 and (X*Y*q)%(q**4)==0
   for z in [-2,-1,0,1,2]:
    w=d*z-X*Y*q
    assert H*(X*Y*q+w)%q**5==0 and w%q**4==0
   cases+=1
# Verify exact graph formulas with a separately written evaluator, including
# signed masks/ranks, as a wiring check rather than a universal argument.
rng=random.Random(137);controls=0
for _ in range(100):
 v={n:rng.randrange(1,6) for n in g['witnesses']};v.update({n:rng.randrange(-3,5) for n in g['fixed_numerals']})
 for n,op,a,b in g['source']:
  x=v[a] if isinstance(a,str) else a;y=v[b] if isinstance(b,str) else b
  v[n]=x+y if op=='+' else x-y if op=='-' else x*y
 assert v['Z']==v['M']*(v['ell']+v['k']+v['r']-v['k']*v['C'])+v['Y']*v['qm']-v['q3']*v['Bt']
 assert v['A0']==v['Z']**2-v['M']**2*(1+v['ell']*(v['ell']+v['k']))
 assert v['Dstar']==v['U']*(v['X']+v['a']*v['c'])+v['H']*(v['U']*v['gamma']+v['E']*v['q']+v['R']+1-v['k'])
 assert v['A1']==v['Dstar']**2-v['U']**2*(1+v['Delta']*v['c']**2)
 controls+=1
out=subprocess.check_output([sys.executable,'-I','-S','-B',str(R/'research/adaptive87-current-cfold-orientation-q4/check.py')],cwd=R)
assert out==(R/'research/adaptive87-current-cfold-orientation-q4/result.json').read_bytes()
print(json.dumps({'exact_literal_rows':len(need),'q_s_X_controls':cases,'signed_congruence_controls':5*cases,'separate_graph_wiring_controls':controls,'author_receipt_reproduced':True,'limitations':'standard integers only; no graph-zero to Cal, index alignment, power-recovery or Lean claim'},sort_keys=True,indent=2))
