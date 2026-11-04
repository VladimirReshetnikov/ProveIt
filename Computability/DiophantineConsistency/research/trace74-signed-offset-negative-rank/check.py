#!/usr/bin/env python3
"""Fixed-payload rank/offset scalar counterexample; never evaluates full output."""
import gzip,hashlib,json,sys
from pathlib import Path
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:raise SystemExit('invoke python3 -I -S -B')
here=Path(__file__).resolve().parent;root=here.parents[1]
p=root/'research/trace74-mask-coordinate-probe/candidate.json';pin='dafefaa40173c9f75c414171896e19ddcf5f5eec82a0612d82a4e23988ee7353'
def sha(x):return hashlib.sha256(x).hexdigest()
assert sha(p.read_bytes())==pin
x=json.loads(p.read_text());rows={r[0]:r[1:] for r in x['source']};coef=root/'candidates/ten-positive-qcube-product-square/coefficients';ports={};payload={}
for n,item in x['coefficient_binding']['ports'].items():
 data=(coef/item['file']).read_bytes();raw=gzip.decompress(data)
 assert sha(data)==item['parent_gzip_sha256'] and sha(raw)==item['raw_sha256']
 ports[n]=int.from_bytes(raw,'little');assert ports[n].bit_length()==item['bits'];payload[n]=sha(raw)
beta=ports['beta'];mc=ports['MC'];mf=ports['MF'];q=beta+1
assert q==2**(67*8807) and 31<=beta and 0<mc<beta<mf<2*beta and mc%2==0
a={'beta':beta,'MC':mc,'MF':mf,'J':1,'F':q*q,'C':q*q+1}
def evaluate(n):
 if type(n) is int:return n
 if n in a:return a[n]
 op,l,r=rows[n];l=evaluate(l);r=evaluate(r);a[n]={'+':lambda:l+r,'-':lambda:l-r,'*':lambda:l*r}[op]();return a[n]
R=evaluate('R');assert R==-q**5+q**3-q**2+1+mc+q*mf and R<0
k=R+1+2*q**5;assert k>2 and k%2==0
a['eta']=1;a['zeta']=k-1
assert evaluate('k')==k and a['zeta']>0
e=evaluate('e');assert e==2*q**5 and e%q**4==0
residue=k%(q**4);assert residue>0 and residue%2==0
first_index=residue//2;assert 0<first_index<=k and (2*first_index)%(q**4)==residue
assert a['F']+a['C']>q and q-a['F']-a['C']<0
assert sha(p.read_bytes())==pin
print(json.dumps({'status':'PASS','source_candidate_sha256':pin,'raw_fixed_port_sha256':payload,'q_bits':q.bit_length(),'J':1,'F':'q^2','C':'q^2+1','R':'-q^5+q^3-q^2+1+MC+q*MF','R_negative':R<0,'k':'R+1+2*q^5','eta':1,'zeta':'k-1','e':'2*q^5','e_divisible_q4':e%q**4==0,'first_index_candidate':'(k mod q^4)/2','first_index_positive':first_index>0,'first_index_le_k':first_index<=k,'k_congruent_twice_index':(2*first_index)%(q**4)==residue,'reverse_guard':False,'scope':'Fixed compressed payloads and partial scalar R/e cones only; no full 74 zero, no first-Pell recurrence, no fixed-port theorem or iPRA claim.'},sort_keys=True,indent=2))
