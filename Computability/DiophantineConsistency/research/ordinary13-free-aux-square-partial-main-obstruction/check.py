from pathlib import Path
from hashlib import sha256
from math import isqrt
import json,sys,subprocess,itertools
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('research/ordinary13-free-aux-square-partial-main-obstruction')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
p=Path('research/ordinary13-free-aux-square-compact-factor-obstruction')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(p/'check.py')])==(p/'receipt.json').read_bytes()
g=json.loads((p/'candidate.json').read_text());r={row[0]:row[1:] for row in g['source']}
for n,row in {'s':['+','n_s',1],'q':['+',1,'qm'],'Y':['*','q3','s'],'U':['*','Y','q2'],'a':['+','E','Y'],'H':['+',3,'g15'],'Delta':['+','H','g17'],'c2':['*','c','c'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],'F1':['+',1,'A1'],'P01':['*','F0','F1'],'P012':['*','P01','Fa'],'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert r[n]==row,(n,r.get(n))
# Exact univariate polynomial identity in A.
def add(a,b):return [(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))]
def mul(a,b):
 o=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):o[i+j]+=x*y
 return o
def clean(a):
 while len(a)>1 and a[-1]==0:a.pop()
 return a
A=[0,1];A2=mul(A,A);c=add(A2,[1]);delta=add(A2,[-1])
rad=add([1],mul(delta,mul(c,c)))
rhs=mul(A2,add(add(mul(A2,A2),A2),[-1]))
assert clean(rad)==clean(rhs)
# Main factor can never be -1 modulo 4: consequently any integer
# product-output zero must have A1=0, regardless of the other factors.
for u,a,c,d in itertools.product(range(4),repeat=4):
 Delta=a*a+4*a+3
 assert (1+d*d-u*u*(1+Delta*c*c))%4!=3
controls=0
for A in range(2,1000):
 r=1+(A*A-1)*(A*A+1)**2
 assert r==A*A*(A**4+A*A-1)
 assert (A*A)**2<A**4+A*A-1<(A*A+1)**2
 assert isqrt(r)**2!=r
 controls+=1
print(json.dumps({'partial_assignment_receipt_reproduced':True,'candidate_main_and_output_rows_checked':True,'radicand_identity_exact':True,'main_negative_unit_mod4_cases':256,'bounded_nonsquare_radicand_controls':controls,'partial_assignment_extends_to_full_zero':False,'other_aux_square_candidates_excluded':False,'lean_executed':False},sort_keys=True,indent=2))
