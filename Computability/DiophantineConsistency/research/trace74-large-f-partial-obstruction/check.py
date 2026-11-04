#!/usr/bin/env python3
"""Fixed-payload C≤q and F≥q³ partial scalar example, no full graph zero."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
here=Path(__file__).resolve().parent;root=here.parents[1]
p=root/'research/trace74-mask-coordinate-probe/candidate.json';pin='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
def sha(x):return hashlib.sha256(x).hexdigest()
assert sha(p.read_bytes())==pin
x=json.loads(p.read_text());rows={r[0]:r[1:] for r in x['source']};coef=root/'candidates/ten-positive-qcube-product-square/coefficients';ports={};payload={}
for name,item in x['coefficient_binding']['ports'].items():
 data=(coef/item['file']).read_bytes();raw=gzip.decompress(data)
 assert sha(data)==item['parent_gzip_sha256'] and sha(raw)==item['raw_sha256']
 ports[name]=int.from_bytes(raw,'little');assert ports[name].bit_length()==item['bits'];payload[name]=sha(raw)
beta=ports['beta'];mc=ports['MC'];mf=ports['MF'];q=beta+1
assert q==2**(67*8807) and 31<=beta and 0<mc<beta<mf<2*beta
q4=q**4;q3=q**3;P=q**7;k=8*P+4
assert mc>3
C=q+3-mc
assert 0<C<=q
A0=q*q*(q*q-1)-C*(q*q-1)+mc+q*mf
N=A0-(k-1)
assert N%q==0
F0=(-(1+q*q)*(N//q))%q3;F=F0+q3
assert 0<=F0<q3 and F>=q3
assert (q*(q*q-1)*F-N)%q4==0
a={'beta':beta,'MC':mc,'MF':mf,'J':1,'F':F,'C':C,'w':1,'s':1,'eta':1,'zeta':k-1}
def evaluate(n):
 if type(n) is int:return n
 if n in a:return a[n]
 op,l,r=rows[n];l=evaluate(l);r=evaluate(r);a[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]();return a[n]
R=evaluate('R');e=evaluate('e')
assert evaluate('q')==q and evaluate('X')==q and evaluate('Y')==q**3 and evaluate('k')==k
assert R==A0-q*(q*q-1)*F and R<0 and R%q4==3 and e==k-R-1 and e%q4==0
assert a['zeta']>0 and a['F']+a['C']>q and 8*P+4<=k and 2*q4<k*q3+1
# Sparse polynomial arithmetic checks the actual Dtau row and two Pell steps
# in Z[t], hence after substituting t=q, without huge dense squared integers.
def add(u,v,sign=1):
 w=dict(u)
 for deg,c in v.items():w[deg]=w.get(deg,0)+sign*c
 return {deg:c for deg,c in w.items() if c}
def mul(u,v):
 w={}
 for i,a0 in u.items():
  for j,b0 in v.items():w[i+j]=w.get(i+j,0)+a0*b0
 return {deg:c for deg,c in w.items() if c}
one={0:1}; t={1:1}; Pp={7:1}; kp=add({7:8},{0:4}); zp=add(kp,one,-1)
sym={'q':t,'w':one,'s':one,'eta':one,'zeta':zp}
def poly(n):
 if type(n) is int:return {0:n} if n else {}
 if n in sym:return sym[n]
 op,l,r=rows[n];l=poly(l);r=poly(r);sym[n]=add(l,r) if op=='+' else add(l,r,-1) if op=='-' else mul(l,r);return sym[n]
assert poly('X')==t and poly('Y')=={3:1} and poly('k')==kp
B=add(mul({0:2},add(Pp,one,-1)),one);base=add(B,{0:2});delta=mul(add(B,one),add(B,{0:3}))
x0,y0=one,{};x1=add(mul(base,x0),mul(delta,y0));y1=add(x0,mul(base,y0));x2=add(mul(base,x1),mul(delta,y1));y2=add(x1,mul(base,y1))
assert mul({0:2},y2)==kp and x2=={14:8,7:8,0:1}
assert poly('Dtau')==mul(x2,x2)==add(one,mul(mul(Pp,add(Pp,one)),mul(kp,kp)))
assert sha(p.read_bytes())==pin
print(json.dumps({'status':'PASS','source_candidate_sha256':pin,'raw_fixed_port_sha256':payload,'q_bits':q.bit_length(),'J':1,'F':'F0+q^3','w':1,'s':1,'eta':1,'zeta':'k-1','C':'q+3-MC','C_in_1_to_q':True,'F_at_least_q3':F>=q3,'A0':'q^2*(q^2-1)-C*(q^2-1)+MC+q*MF','R':'A0-q*(q^2-1)*F','R_negative':R<0,'e':'k-R-1','e_divisible_q4':e%q4==0,'first_Pell_index':2,'first_Pell_x':'8*q^14+8*q^7+1','first_Pell_y':'4*q^7+2','k':'8*q^7+4','first_Pell_E_polynomial_identity':True,'k_lower_bound':True,'c_gt_two_q4':True,'reverse_guard':False,'scope':'Fixed payload, 0<C≤q<F partial R/e cones, plus exact sparse-polynomial source Dtau and first Pell recurrence at n=2 only; no second Pell, carrier/adjacent factors, full 74 zero, fixed-port theorem or iPRA claim.'},sort_keys=True,indent=2))
