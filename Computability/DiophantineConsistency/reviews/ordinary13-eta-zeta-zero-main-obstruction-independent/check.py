from pathlib import Path
import hashlib,json,subprocess,sys
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
D=Path('reviews/ordinary13-eta-zeta-zero-main-obstruction-independent')
for path,expected in json.loads((D/'pins.json').read_text()).items():
 assert hashlib.sha256(Path(path).read_bytes()).hexdigest()==expected,path
P=Path('research/ordinary13-eta-zeta-zero-main-obstruction-draft')
assert subprocess.check_output([sys.executable,'-I','-S','-B',str(P/'check.py')])==(P/'receipt.json').read_bytes()
s=(P/'ZeroOrdinateMainObstruction.lean.src').read_text()
for text in ['(hq : 2≤q) (hY : q^3≤Y) (hX : X=q*w)', '(hnorm : z*z=ι (Y*(q*q))*ι (Y*(q*q)))', 'rcases mul_eq_zero.mp hfactor with hp | hm', 'ι U*(ι X-1)', 'ι U*(ι X+1)', 'by_cases hw : w=0', 'P72Root.ι_tsub hX1', 'Trace75IntegralTransport.natural_dvd_of_signed H (3*(q*q)*L) hthreeSigned', 'le_of_dvd hpos hthree']:
 assert text in s,text
reflection=Path('Lean/DiophantineConsistency/BFS943/Trace75IntegralTransport.lean').read_text()
assert 'theorem natural_dvd_of_signed (a b : V) (hd : (ι a : DiffRing V)∣ι b) : a∣b' in reflection
assert 'theorem ι_tsub {a b : V} (h : b ≤ a)' in Path('Lean/DiophantineConsistency/Compact44/P72Root.lean').read_text()
g=json.loads(Path('research/ordinary13-eta85-zeta-zero-boundary-audit/probe.json').read_text());rows={r[0]:r[1:] for r in g['source']}
required={'kbase':['+','n_eta','n_zeta'],'kY':['*','Y','kbase'],'c':['+','n_eta','kY'], 'a':['+','E','Y'],'E':['*','X','Y'],'H':['+ ',3,'g15'], 'g15':['*',4,'a'],'b0':['+','X','g19'],'g19':['*','a','c'],'r0base':['-','kbase','R'],'r0':['-','r0base',1], 'g54':['*','U','n_gamma'],'shift':['-','g54','r0'],'g58':['*','U','b0'],'g59':['*','H','shift'],'Dstar':['+','g58','g59'],'c2':['*','c','c'],'g61':['*','Dstar','Dstar'],'g62':['*','U','U'],'g63':['*','Delta','c2'],'g64':['+',1,'g63'],'g65':['*','g62','g64'],'A1':['-','g61','g65'],'U':['*','Y','q2'],'q2':['*','q','q'],'q3':['*','q','q2'],'Y':['*','q3','s'],'s':['+','n_s',1],'X':['*','q','n_w']}
required['H']=['+',3,'g15']
for n,r in required.items():assert rows[n]==r,(n,rows[n],r)
# The certificate is verified coefficient by coefficient using a sparse
# polynomial ring in X,Y,q,L,t; multiplication/subtraction are exact.
def var(i):
 e=[0]*5;e[i]=1;return {tuple(e):1}
def add(a,b):
 c=a.copy()
 for k,v in b.items():c[k]=c.get(k,0)+v
 return {k:v for k,v in c.items() if v}
def scale(a,n):return {k:n*v for k,v in a.items() if n*v}
def sub(a,b):return add(a,scale(b,-1))
def mul(a,b):
 c={}
 for ka,va in a.items():
  for kb,vb in b.items():
   k=tuple(x+y for x,y in zip(ka,kb));c[k]=c.get(k,0)+va*vb
 return {k:v for k,v in c.items() if v}
one={(0,)*5:1};X,Y,q,L,t=(var(i) for i in range(5)); xp=add(X,one);q2=mul(q,q); U=mul(Y,q2);H=add(scale(one,3),scale(mul(Y,xp),4))
lhs=sub(scale(mul(q2,L),3),mul(H,sub(mul(q2,L),scale(mul(xp,t),4))))
rhs=scale(mul(xp,sub(mul(U,L),mul(H,t))),-4)
assert lhs==rhs
print(json.dumps({'exact_certificate_polynomial_identity':True,'both_signed_root_cases_and_natural_divisibility_interface_checked':True,'probe_zero_ordinate_main_rows_checked':True,'source_elaborated':False,'graph_unit_extraction_established':False},indent=2,sort_keys=True))
