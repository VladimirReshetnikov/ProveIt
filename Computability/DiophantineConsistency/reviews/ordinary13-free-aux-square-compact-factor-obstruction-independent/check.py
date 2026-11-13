#!/usr/bin/env python3
"""Independent, bounded verification of the source-pinned partial construction."""
import hashlib,json,math
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for name,digest in json.loads((here/'pins.json').read_text()).items():
 assert hashlib.sha256((root/name).read_bytes()).hexdigest()==digest,name
p=json.loads((root/'research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text())
c=json.loads((root/'research/ordinary13-free-aux-square-compact-factor-obstruction/candidate.json').read_text())
assert len(p['source'])==85 and len(c['source'])==84
assert p['witnesses'][11]=='n_y' and c['witnesses'][11]=='n_y2'
assert p['witnesses'][:11]+['n_y2']+p['witnesses'][12:]==c['witnesses']
assert p['fixed_numerals']==c['fixed_numerals'] and p['output']==c['output']
rows=[]
for name,op,a,b in p['source']:
 if name=='y2':
  assert (op,a,b)==('*','n_y','n_y');continue
 rows.append([name,op, 'n_y2' if a=='y2' else a, 'n_y2' if b=='y2' else b])
assert rows==c['source']
# The exact rank and remaining factor fields are those used in the argument.
r={x[0]:x[1:] for x in c['source']}
for k,v in {'q':['+',1,'qm'],'qF':['-','q','F'],'G':['+','alpha','g44'],
 'g44':['*','qF','qm'],'R':['+','g47','g50'],'c':['+','n_eta','kY'],
 'Q':['*','Delta','rho'],'I':['*','c2','i'],'g72':['-','g71','Q'],
 'g74':['*','T','c'],'g75':['-','g74','R'],'V':['-','g76','c'],
 'g81':['-','n_y2','V2'],'Fa':['-','n_y2','g82']}.items():assert r[k]==v,(k,r[k])
fixed=(root/'Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in fixed
N=67*8807
assert pow(2,N,17)==15 and pow(2,N,5)==2
assert math.gcd(15-1,17)==math.gcd(2+1,5)==1
# Direct algebra controls across q, with gcd and k reconstruction independently checked.
for q in range(2,202,2):
 Y=q**3;a=Y*(q+1);Delta=(a+2)**2-1;C=q*q-1;cc=Delta+2
 assert cc%Y==5 and cc==(a*a+4*a+5)
 assert cc%(q-1)==17%(q-1) and cc%(q+1)==5%(q+1)
 assert math.gcd(C,cc)==math.gcd(q-1,17)*math.gcd(q+1,5)
 k=(cc-5)//Y
 assert cc==Y*k+5 and k>5
 for I in (2,3,10):
  y2=I**4-3*I*I+1;V=I*I-2
  assert y2-I*I*(y2-V*V)==1 and V*V<y2<(I*I-1)**2
# Independent exact complete-graph toy, no value converted to decimal text.
q=2;beta=q-1;Y=q**3;X=0;a=Y;A=a+2;D=A*A-1;cc=D+2;C=q*q-1
alpha=next(a0 for a0 in range(1,cc+1) if ((a0+beta**2)*C-2)%cc==0)
R=(alpha+beta**2)*C;T=(R+D)//cc
u,v=1,0;n=0
while True:
 u,v=(A*u+D*v)%(cc*cc),(u+A*v)%(cc*cc);n+=1
 if (u,v)==(1,0):break
 assert n<=cc**8
# Binary powering of the Pell unit.
f,v=1,0;u,t=A,1;h=n
while h:
 if h&1:f,v=f*u+D*v*t,f*t+v*u
 u,t=u*u+D*t*t,2*u*t;h//=2
assert v>0 and v%(cc*cc)==0 and f*f-D*v*v==1
i=D*(v//(cc*cc));I=cc*cc*i;V=I*I-2;y2=I**4-3*I*I+1
k,eta=divmod(cc,Y);zeta=k-eta
vals=[1,0,alpha-1,f,i-1,T-1,0,0,0,eta,zeta,y2,0]
assert all(x>=0 for x in vals)
def evaluate(g,values,ports):
 env=dict(zip(g['witnesses'],values));env.update(zip(g['fixed_numerals'],ports))
 for name,op,l,r in g['source']:
  l=env[l] if isinstance(l,str) else l;r=env[r] if isinstance(r,str) else r
  env[name]=l+r if op=='+' else l-r if op=='-' else l*r
 return env
out=evaluate(c,vals,[beta,1,0,0])
assert (out['R'],out['c'],out['I'],out['V'])==(R,cc,I,V)
assert out['g72']==0 and out['Fa']==1 and out['A0']!=0 and out['A1']!=0
assert V*V<y2<(I*I-1)**2
print(json.dumps({'parent_rows':85,'candidate_rows':84,'literal_parent_to_child_map_verified':True,
 'fixed_q_mod17':15,'fixed_q_mod5':2,'gcd_expression_checked_for_even_q_through_200':True,
 'eta_five_and_zeta_natural_checked':True,'auxiliary_identity_and_nonsquare_checked':True,
 'independent_toy_period':n,'toy_first_main_residuals_nonzero':True,
 'compact_full_zero_claimed':False,'lean_executed':False},sort_keys=True,indent=2))
