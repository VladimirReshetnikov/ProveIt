#!/usr/bin/env python3
"""Fixed-payload partial scalar example satisfying the actual first Pell index."""
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
q4=q**4;A=q*(q-1)*(q*q-1)+mc+q*mf
C0=((1-A)*(q*q+1))%q4;C=C0+q4
assert 0<=C0<q4 and C>0
a={'beta':beta,'MC':mc,'MF':mf,'J':1,'F':1,'C':C,'w':1,'s':1,'eta':1,'zeta':1}
def evaluate(n):
 if type(n) is int:return n
 if n in a:return a[n]
 op,l,r=rows[n];l=evaluate(l);r=evaluate(r);a[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]();return a[n]
R=evaluate('R');k=evaluate('k');e=evaluate('e');X=evaluate('X');Y=evaluate('Y');E=evaluate('Dtau')
assert R==A-C*(q*q-1) and R<0 and R%q4==1 and e==1-R and e%q4==0
assert X==q and Y==q**3 and k==2 and a['F']+a['C']>q
P=X*Y*Y;B=2*(P-1)+1;tau=2*P+1
# First successor of (x0,y0)=(1,0) in ArithmeticPellRecurrence.advance.
x0,y0=1,0;x1=(B+2)*x0+(B+1)*(B+3)*y0;y1=x0+(B+2)*y0
assert P==q**7 and 0<tau and E==tau*tau and E==1+P*(P+1)*k*k
assert x1==tau and 2*y1==k and 0<1<=k
assert sha(p.read_bytes())==pin
print(json.dumps({'status':'PASS','source_candidate_sha256':pin,'raw_fixed_port_sha256':payload,'q_bits':q.bit_length(),'J':1,'F':1,'w':1,'s':1,'eta':1,'zeta':1,'C':'((1-A)*(q^2+1) mod q^4)+q^4','A':'q*(q-1)*(q^2-1)+MC+q*MF','R':'A-C*(q^2-1)','R_negative':R<0,'e':'1-R','e_divisible_q4':e%q4==0,'first_Pell_index':1,'first_Pell_x':'2*P+1','first_Pell_y':1,'first_Pell_E_is_square':E==tau*tau,'P':'q^7','reverse_guard':False,'scope':'Fixed payload and partial scalar graph cones plus first Pell recurrence at n=1 only; no second Pell, carrier/adjacent factors, full 74 zero, fixed-port theorem or iPRA claim.'},sort_keys=True,indent=2))
