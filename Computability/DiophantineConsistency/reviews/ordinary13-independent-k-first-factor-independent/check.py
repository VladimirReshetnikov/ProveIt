from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-first-factor-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-independent-k-first-factor-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text());r={x[0]:x[1:] for x in g['source']}
assert g['domain']=='nonnegative integers' and len(g['source'])==84
for name,row in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'F':['+','n_F',1],
 'alpha':['+','n_alpha',1],'qF':['-','q','F'],'C':['-','qF','alpha'],
 'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],
 's':['+','n_s',1],'Y':['*','q3','s'],'U':['*','Y','q2'],
 'E':['*','X','Y'],'a':['+','E','Y'],'g15':['*',4,'a'],
 'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17'],
 'c':['+','n_eta','kY'],'c2':['*','c','c'],'g19':['*','a','c'],
 'b0':['+','X','g19'],'g26':['+','X','K0'],'g27':['*','C','g26'],
 'Bt':['-','g27','F'],'kY':['*','Y','n_k'],
 'ell':['*','E','kY'],'g31':['+','g30','n_r'],'folded_kBt':['*','n_k','Bt'],
 'g30':['+','ell','n_k'],'folded_g31':['-','g31','folded_kBt'],
 'g32':['*','qm','folded_g31'],'Z':['-','g32','Bt'],
 'g38':['*','Z','Z'],'g39':['*','qm','qm'],'g40':['*','ell','g30'],
 'g41':['+',1,'g40'],'g42':['*','g39','g41'],
 'A0':['-','g38','g42'],'g44':['*','qF','qm'],'G':['+','alpha','g44'],
 'g46':['-','q2',1],'g47':['*','G','g46'],'g48':['*','MF','q'],
 'g49':['+','MC','g48'],'g50':['*','n_J','g49'],'R':['+','g47','g50'],
 'r0base':['-','n_k','R'],'r0':['-','r0base',1],
 'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],
 'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],
 'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],
 'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],
 'F0':['+',1,'A0'],'F1':['+',1,'A1'],'Fs':['+',1,'g72'],
 'P01':['*','F0','F1'],'P012':['*','P01','Fa'],
 'P0123':['*','P012','Fs'],'out':['-','P0123',1]}.items():assert r[name]==row,(name,r[name])
# Independent exact sparse integer-polynomial identities.
N=6;Z=(0,)*N
def C(n):return {Z:n} if n else {}
def V(i):
 a=[0]*N;a[i]=1;return {tuple(a):1}
def add(x,y,sgn=1):
 out=x.copy()
 for k,v in y.items():out[k]=out.get(k,0)+sgn*v
 return {k:v for k,v in out.items() if v}
def mul(x,y):
 out={}
 for a,v in x.items():
  for b,w in y.items():
   k=tuple(i+j for i,j in zip(a,b));out[k]=out.get(k,0)+v*w
 return {k:v for k,v in out.items() if v}
def sub(x,y):return add(x,y,-1)
def sq(x):return mul(x,x)
one=C(1);two=C(2);three=C(3);four=C(4)
ell,t,b,rr,B,d=[V(i) for i in range(N)];k=add(one,t)
assert sub(sq(add(ell,k)),add(one,mul(ell,add(ell,k))))==add(mul(ell,k),sub(sq(k),one))
assert all(v>=0 for v in sub(sq(k),one).values())
z=sub(mul(b,rr),B)
assert sub(sq(z),sq(b))==mul(sub(z,b),add(z,b))
q,F,alpha,d,b_unused,_=[V(i) for i in range(N)]
qF=sub(q,F);bb=sub(q,one);B=sub(mul(sub(qF,alpha),d),F)
assert add(B,bb)==sub(sub(mul(qF,add(d,one)),mul(alpha,d)),one)
# Main inequality's exact positive decomposition after q=Q+2.
Q,a,mc,mf,_,_=[V(i) for i in range(N)];q=add(Q,two);U=mul(a,sq(q));H=add(three,mul(four,a))
rank=add(add(mul(q,sub(sq(q),one)),mc),mul(q,mf))
left=sub(mul(H,add(rank,one)),mul(two,mul(U,q)))
right=add(add(mul(two,mul(mul(a,q),sub(sq(q),two))),mul(three,mul(q,sub(sq(q),one)))),mul(H,add(add(mc,mul(q,mf)),one)))
assert left==right and left.get(Z,0)>0 and all(c>=0 for c in left.values())
# Finite controls evaluate the actual graph; the proof applies to this family only.
def ev(v,p):
 e=dict(zip(g['witnesses'],v));e.update(zip(g['fixed_numerals'],p))
 for n,op,x,y in g['source']:
  x=e[x] if isinstance(x,str) else x;y=e[y] if isinstance(y,str) else y
  e[n]={'+':lambda:x+y,'-':lambda:x-y,'*':lambda:x*y}[op]()
 return e
count=0
for beta in range(1,8):
 q=beta+1
 for K in range(3):
  for MC in range(3):
   for MF in range(3):
    for s in range(3):
     for gamma in range(3):
      for eta in range(q+1):
       v=[0]*13;v[0]=1;v[1]=beta-1;v[7]=s;v[9]=eta;v[12]=gamma
       e=ev(v,[beta,K,MC,MF]);assert e['Bt']==-beta and e['Z']==beta and e['A0']==0
       assert e['A1']>0 and (e['out']+1)%e['F1']==0 and e['out']!=0;count+=1
# k=0 quadratic split and its unique negative branch, over finite integers.
for b in range(1,8):
 for rr in range(8):
  for B in range(-12,40):
   if (b*rr-B)**2==b*b:
    assert B in (b*(rr-1),b*(rr+1))
    if B<0:assert rr==0 and B==-b
assert 'def betaNat : ℕ := 2^(67*8807)-1' in Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduces':True,'actual_graph_rows_checked':True,
 'first_norm_and_exceptional_relation_polynomial_identities':True,
 'main_inequality_positive_coefficient_certificate':True,
 'finite_main_family_controls_eta_zero_through_q':count,
 'original_exclusion_eta_1_through_q_confirmed':True,
 'additional_eta_zero_case_for_same_family':True,
 'standard_integer_output_nonzero_for_same_family':True,
 'other_k_zero_cases_or_all_full_zeros_excluded':False,'lean_executed':False,
 'scope':'External arithmetic for one exceptional family only; no all-model replacement theorem, Lean or iPRA endpoint.'},sort_keys=True,indent=2))
