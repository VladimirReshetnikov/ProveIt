#!/usr/bin/env python3
"""UNREVIEWED: fixed-payload partial rank example with a genuine odd ordinate."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
root=Path(__file__).resolve().parents[2]
def sha(x):return hashlib.sha256(x).hexdigest()
p=root/'research/trace74-mask-coordinate-probe/candidate.json'; pin='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
assert sha(p.read_bytes())==pin
x=json.loads(p.read_text());rows={r[0]:r[1:] for r in x['source']};coef=root/'candidates/ten-positive-qcube-product-square/coefficients';ports={};payload={}
for name,item in x['coefficient_binding']['ports'].items():
 data=(coef/item['file']).read_bytes();raw=gzip.decompress(data)
 assert sha(data)==item['parent_gzip_sha256'] and sha(raw)==item['raw_sha256']
 ports[name]=int.from_bytes(raw,'little');assert ports[name].bit_length()==item['bits'];payload[name]=sha(raw)
beta=ports['beta'];mc=ports['MC'];mf=ports['MF'];q=beta+1
assert q==2**(67*8807) and q>=32 and 0<mc<beta<mf<2*beta
# Pell y_5 as a sparse Z[q] polynomial; A=q^4+q^3, b=A-1.
def add(a,b,sign=1):
 z=dict(a)
 for i,c in b.items():z[i]=z.get(i,0)+sign*c
 return {i:c for i,c in z.items() if c}
def mul(a,b):
 z={}
 for i,c in a.items():
  for j,d in b.items():z[i+j]=z.get(i+j,0)+c*d
 return {i:c for i,c in z.items() if c}
one={0:1};A={4:1,3:1};base=add(A,one);delta=mul(A,add(A,{0:2}));xx=one;yy={}
for _ in range(5):xx,yy=add(mul(base,xx),mul(delta,yy)),add(xx,mul(base,yy))
assert all(v>=0 for v in yy.values())
c=sum(v*q**i for i,v in yy.items());q3=q**3;q4=q**4;Y=q3;X=q
# Choose largest k≡4 mod q⁴ with kY<c. Its remainder eta is positive.
k=4+q4*((c-1-4*Y)//(q4*Y));eta=c-k*Y;zeta=k-eta
assert k%q4==4 and 0<eta<k and zeta>0 and k>8*(X*Y*Y)+4 and c>2*q4
# First-Pell k_n=2*y_n(B), B=2*(q^7-1)+1: k_2=8*q^7+4, k_3=32*q^14+32*q^7+6.
# If these exact inequalities pass, strict ordinate growth excludes any positive first-Pell n.
first_k2=8*q**7+4;first_k3=32*q**14+32*q**7+6
assert first_k2<k<first_k3
C=q3+q+3-mc
assert C>q and C%q==(3-mc)%q
A0=q*q*(q*q-1)-C*(q*q-1)+mc+q*mf;N=A0-(k-1)
assert N%q==0
F0=(-(1+q*q)*(N//q))%q3;F=F0+q3
assert 0<=F0<q3 and (q*(q*q-1)*F-N)%q4==0
a={'beta':beta,'MC':mc,'MF':mf,'K0':ports['K0'],'J':1,'F':F,'C':C,'w':1,'s':1,'eta':eta,'zeta':zeta}
def evaluate(n):
 if type(n) is int:return n
 if n in a:return a[n]
 op,l,r=rows[n];l=evaluate(l);r=evaluate(r);a[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]();return a[n]
R=evaluate('R');e=evaluate('e');B=evaluate('Bt')
assert evaluate('X')==X and evaluate('Y')==Y and evaluate('c')==c and evaluate('k')==k
assert R==A0-q*(q*q-1)*F and R<0 and e==k-R-1 and e%q4==0
assert B==(ports['K0']+1)*C-F and B>0
assert sha(p.read_bytes())==pin
print(json.dumps({'status':'PASS','source_candidate_sha256':pin,'raw_fixed_port_sha256':payload,'q_bits':q.bit_length(),'X':'q','Y':'q^3','odd_index':5,'ordinate_polynomial':yy,'k':'4+q^4*floor((c-1-4q^3)/q^7)','k_mod_q4':4,'eta':'c-k*q^3','zeta':'k-eta','c_is_odd_ordinate':True,'first_index_congruence_only':2,'first_Pell_equation_checked':False,'between_first_Pell_k2_k3':True,'size_bound':True,'C':'q^3+q+3-MC','F':'F0+q^3','R_negative':True,'e_divisible_q4':True,'B_positive':True,'scope':'External fixed-payload scalar coordinates only; actual first-Pell equation, scaled second-Pell, adjacency and full graph zero not checked; strict growth plus the checked first-Pell recurrence excludes the tuple; no Lean fixed-port binding.'},sort_keys=True,indent=2))
