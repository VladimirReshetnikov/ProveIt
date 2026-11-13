from pathlib import Path
from hashlib import sha256
import json,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-eta-zeta84-unshift-i-positive-ports-zero')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
parent=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());child=json.loads(Path('research/ordinary13-eta-zeta84-unshift-i-signed-full-zero/probe.json').read_text())
assert len(parent['source'])==85 and len(child['source'])==84
rows=[]
for row in parent['source']:
 if row==['i','+','n_i',1]:continue
 rows.append(['n_i' if x=='i' else x for x in row])
assert rows==child['source']
def pell(A,n):
 x,y=1,0;delta=A*A-1
 for _ in range(n):x,y=A*x+delta*y,x+A*y
 return x,y
beta,K0,MC,MF=3,2,914,1;q=4;J=1;F=1;alpha=2
X=2**35;w=X//q;Y=q**3;U=Y*q*q;M=X*Y*Y;R=(alpha+(q-F)*beta)*(q*q-1)+MC+q*MF
assert R==1083 and U==1024
n,m=30,35;tau,yfirst=pell(2*M+1,n);k=2*yfirst;a=Y*(X+1);H=3+4*a;main,c=pell(a+2,m);eta=c-Y*k
assert 0<eta<k and (X+K0-F)%beta==0
h=(X+K0-F)//beta;r=tau-M*k-k+(k*beta+1)*h
assert (k-R-1)%U==0 and (main-X-a*c)%H==0
gamma=(main-X-a*c)//H+(k-R-1)//U
witness=[1,0,1,1,0,0,w,0,r,eta,k-eta,1,gamma];ports=[beta,K0,MC,MF]
assert min(witness)>=0 and min(ports)>0 and MC>beta
def ev(graph):
 d=dict(zip(graph['witnesses'],witness));d.update(zip(graph['fixed_numerals'],ports))
 for name,op,x,y in graph['source']:
  x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
  d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return d
u=ev(child);v=ev(parent)
for name,value in [('q',q),('Y',Y),('U',U),('R',R),('kbase',k),('c',c),('Z',beta*tau),('Dstar',U*main),('A0',0),('A1',0),('Q',0),('I',0),('g72',0),('Fa',1),('out',0)]:assert u[name]==value,name
assert v['out']==c**4 and v['out']>0
# Digest exact tuple in canonical decimal without emitting long numerals.
encoded=json.dumps({'witness':witness,'ports':ports},separators=(',',':')).encode()
print(json.dumps({'ports':ports,'first_pell_index':n,'main_pell_index':m,'R':R,'X':'2^35','Y':Y,'U':U,'all_84_child_and_85_parent_rows_evaluated':True,'child_output':0,'parent_same_tuple_output':'c^4 > 0','strict_eta_between_zero_and_k':True,'witness_sha256':sha256(encoded).hexdigest(),'witness_bit_lengths':[x.bit_length() for x in witness],'compact_mask_bounds_hold':False,'existential_zero_equivalence_refuted':False,'lean_executed':False},sort_keys=True,indent=2))
