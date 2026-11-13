from pathlib import Path
from hashlib import sha256
import json,sys,subprocess
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary10-divisible61-coarse-symbolic-zero')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
for name in ('ordinary10-two-norm-divisible61','ordinary13-eta-zeta84-unshift-i-coarse-bounds-zero'):
 p=Path('research')/name;assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary10-two-norm-divisible61/candidate.json').read_text());assert len(g['source'])==61
L=2172;n=L*(2*L+1);m=n+L;q=128;beta=127;K0=87;F=119;alpha=8;MC=54;MF=139
R=(alpha+(q-F)*beta)*(q*q-1)+MC+q*MF
assert (n,m,R)==(9437340,9439512,18874679) and R==2*n-1 and (pow(2,m,beta)-32)%beta==0
assert L>=21 and m>=7 and (m-1)*(m+L+1)==L+1+(n-1)*(m+2*L+2)
# Recompute the prior smaller toy and evaluate all 61 actual rows.
def pell(A,n):
 d=A*A-1;x,y=1,0
 for _ in range(n):x,y=A*x+d*y,x+A*y
 return x,y
q=4;beta=3;K0=1;MC=MF=1;L=6;n=L*(2*L+1);m=n+L;X=2**m;Y=2**L;M=X*Y*Y
R=155;assert R==2*n-1
tau,yFirst=pell(2*M+1,n);k=2*yFirst;a=Y*(X+1);H=4*a+3;g0,c=pell(a+2,m)
eta=c-Y*k;assert 0<eta<k and (2*X+1)%beta==0
h=(2*X+1)//beta;U=Y*q*q;assert (g0-X-a*c)%H==0 and (k-R-1)%U==0
gamma=(g0-X-a*c)//H+(k-R-1)//U
w=[1,0,0,X//q,0,h,tau,eta,k-eta-1,gamma];ports=[beta,K0,MC,MF];assert min(w)>=0
d=dict(zip(g['witnesses'],w));d.update(zip(g['fixed_numerals'],ports))
for name,op,x,y in g['source']:
 x=d[x] if isinstance(x,str) else x;y=d[y] if isinstance(y,str) else y
 d[name]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
assert (d['Bres'],d['firstres'],d['A1'],d['out'])==(0,0,0,0)
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'prior_receipts_reproduced':True,'symbolic_coarse_ports':[127,87,54,139],
 'symbolic_indices':[9437340,9439512],'coarse_full_numerals_materialized':False,
 'all_61_rows_zero_in_separate_q4_control':True,'fixed_compact_zero_proved':False,
 'original_85_parent_zero_proved':False,'lean_executed':False},sort_keys=True,indent=2))
