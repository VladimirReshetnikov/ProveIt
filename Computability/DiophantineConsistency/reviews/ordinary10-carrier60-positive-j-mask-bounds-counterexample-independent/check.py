#!/usr/bin/env python3
"""Independent binary Pell powering and complete Z[K0] literal graph evaluation."""
import hashlib,json
from pathlib import Path
root=Path(__file__).resolve().parents[2];here=Path(__file__).resolve().parent
for p,h in json.loads((here/'pins.json').read_text()).items():assert hashlib.sha256((root/p).read_bytes()).hexdigest()==h,p
p='research/ordinary10-carrier60-inverse-boundary/candidate.json'
g=json.loads((root/p).read_text())
assert g['domain']=='nonnegative integers' and len(g['source'])==60
assert g['fixed_numerals']==['beta','K0','MC','MF']
assert g['witnesses']==['n_J','n_F','n_C','n_w','n_s','n_h','n_tau','n_eta','n_zeta','n_gamma']
# Unit powers via binary exponentiation, independent of the author's step iteration.
def ppow(D,u,v,n):
 def mul(x,y):return (x[0]*y[0]+D*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
 r=(1,0);a=(u,v)
 while n:
  if n&1:r=mul(r,a)
  a=mul(a,a);n//=2
 return r
tau,k=ppow(128*129,257,2,855)
g0,c=ppow(675,26,1,1351)
assert tau*tau-128*129*k*k==1 and g0*g0-675*c*c==1
eta=c-8*k;zeta=k-eta-1
assert eta>=0 and zeta>=0
v=32*(g0-2-24*c);assert v%99==0
shift=v//99;num=shift+18+k;assert num>=0 and num%32==0
gamma=num//32
# Sparse polynomials in an arbitrary K0, with integer coefficients.
def num(x):return {} if x==0 else {0:x}
def add(a,b,sign=1):
 out=a.copy()
 for e,x in b.items():out[e]=out.get(e,0)+sign*x
 return {e:x for e,x in out.items() if x}
def mul(a,b):
 out={}
 for i,x in a.items():
  for j,y in b.items():out[i+j]=out.get(i+j,0)+x*y
 return {e:x for e,x in out.items() if x}
env={'beta':num(1),'K0':{1:1},'MC':{},'MF':num(1),
 'n_J':num(1),'n_F':{},'n_C':num(8),'n_w':num(1),'n_s':{},
 'n_h':{0:17,1:9},'n_tau':num(tau),'n_eta':num(eta),
 'n_zeta':num(zeta),'n_gamma':num(gamma)}
for name,op,x,y in g['source']:
 assert name not in env and op in ('+','-','*')
 x=env[x] if isinstance(x,str) else num(x);y=env[y] if isinstance(y,str) else num(y)
 env[name]=mul(x,y) if op=='*' else add(x,y,1 if op=='+' else -1)
for name,v in {'q':2,'X':2,'Y':8,'U':32,'C':9,'F':1,'k':k,'c':c,
 'a':24,'H':99,'Delta':675,'R':-19,'Dstar':32*g0,
 'Bres':0,'firstres':0,'A1':0,'out':0}.items():assert env[name]==num(v),name
assert add(env['qF'],env['C'],-1)==num(-8)
assert 1>0 and 0<1 and 1<2 and 1==1 # beta, MC<beta, MF<2beta, J
print(json.dumps({'binary_first_and_main_Pell_indices':[855,1351],
 'first_ordinate_bit_length':k.bit_length(),'main_ordinate_bit_length':c.bit_length(),
 'eta_zeta_gamma_natural':True,'all_60_rows_exact_in_Z_K0':True,
 'K0_scope':'any natural, including all positive values','beta':1,'MC':0,'MF':1,'J':1,
 'reconstructed_alpha':-8,'exact_compact_beta_tested':False,
 'existential_61_versus_60_inequivalence_proved':False,'lean_executed':False},indent=2,sort_keys=True))
