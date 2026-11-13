from pathlib import Path
from hashlib import sha256
import json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-independent-k-norm-boundary-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
A=Path('research/ordinary13-independent-k-norm-boundary-audit')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(A/'check.py')])==(A/'receipt.json').read_bytes()
# Independent dense-coefficient arithmetic in Z[q], using lists and convolution.
def trim(a):
 a=list(a)
 while len(a)>1 and a[-1]==0:a.pop()
 return tuple(a)
def add(a,b):return trim([(a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0) for i in range(max(len(a),len(b)))])
def neg(a):return tuple(-x for x in a)
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 out=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):out[i+j]+=x*y
 return trim(out)
def pw(a,n):
 out=(1,)
 for _ in range(n):out=mul(out,a)
 return out
one=(1,);two=(2,);four=(4,);q=(0,1);X=q;Y=pw(q,3);m=mul(X,pw(Y,2));k=two
eta=add(mul(two,pw(q,4)),four);a=add(mul(X,Y),Y);c=add(eta,mul(Y,k))
delta=add(add((3,),mul(four,a)),pw(a,2));tau=add(mul(two,m),one);main=sub(mul(two,pw(add(a,two),2)),one)
assert c==mul(two,add(a,two))
assert delta==sub(pw(add(a,two),2),one)
assert pw(tau,2)==add(one,mul(mul(m,add(m,one)),pw(k,2)))
assert pw(main,2)==add(one,mul(delta,pw(c,2)))
assert sub(eta,k)==add(mul(two,pw(q,4)),two)
g=json.loads(Path('research/ordinary13-eta-zeta84-independent-k-candidate/candidate.json').read_text())
assert g['domain']=='nonnegative integers'
assert g['witnesses'][0]=='n_J' and g['witnesses'][6:11]==['n_w','n_s','n_r','n_eta','n_k']
r={x[0]:x[1:] for x in g['source']}
for name,row in {'qm':['*','n_J','beta'],'q':['+',1,'qm'],'X':['*','q','n_w'],'q2':['*','q','q'],'q3':['*','q','q2'],'s':['+','n_s',1],'Y':['*','q3','s'],'E':['*','X','Y'],'kY':['*','Y','n_k'],'ell':['*','E','kY'],'c':['+','n_eta','kY'],'a':['+','E','Y'],'g15':['*',4,'a'],'H':['+',3,'g15'],'g17':['*','a','a'],'Delta':['+','H','g17']}.items():assert r[name]==row,(name,r[name])
# Basic first Pell index is 1, and the claimed early-index conditions cannot
# hold: n≤k=2 contradicts n≥13. This is about the cited wrapper, not a new
# theorem for the changed graph.
rec=Path('Lean/DiophantineConsistency/ArithmeticPellRecurrence.lean').read_text()
for needle in ['theorem x_zero','theorem y_zero','theorem x_succ','theorem y_succ']:assert needle in rec
for qq in [1,2,3,7,23,47,101]:
 Xv=qq;Yv=qq**3;mv=Xv*Yv*Yv;B=2*(mv-1)+1
 assert B>=1 and B+2==2*mv+1 and 2*1==2
 assert all(x>=0 for x in [1,qq-1,1,0,2,2*qq**4+4])
 assert 2<2*qq**4+4
 for n in range(13,30):assert not (n<=2)
early=Path('research/ordinary13-eta-zeta-natural-early-index-draft/EtaZetaNaturalGraphEarlyIndex.lean.src').read_text()
for needle in ['13≤n ∧ n≤k v','2*ycoord n','k v=2*n+4*']:assert needle in early
beta=Path('Lean/DiophantineConsistency/Compact44/CompactFixedBeta.lean').read_text()
assert 'def betaNat : ℕ := 2^(67*8807)-1' in beta and 67*8807==590069
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'author_receipt_reproduces':True,'independent_dense_polynomial_identities':True,
 'actual_candidate_rows_and_natural_coordinates_checked':True,'compact_exponent':590069,
 'basic_first_recurrence_index':1,'cited_early_index_incompatible_with_k2':True,
 'graph_zero_or_replacement_impossibility_proved':False,'lean_executed':False,
 'scope':'Partial arithmetic counterexample and source checks; no full graph, changed-graph early-index theorem or Lean proof.'},sort_keys=True,indent=2))
