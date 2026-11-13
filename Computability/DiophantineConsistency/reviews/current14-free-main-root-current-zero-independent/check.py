from pathlib import Path
from hashlib import sha256
import json,gzip,sys,math,resource
from fractions import Fraction
assert sys.flags.isolated and sys.flags.no_site and sys.dont_write_bytecode
resource.setrlimit(resource.RLIMIT_AS,(384*1024**2,384*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_CORE,(0,0))
D=Path('reviews/current14-free-main-root-current-zero-independent')
for p,h in json.loads((D/'pins.json').read_text()).items():assert sha256(Path(p).read_bytes()).hexdigest()==h,p
P=Path('research/current14-free-main-root-current-zero-obstruction');oldpath=Path('candidates/one-page-padding-staircase-carrier65-2011/polynomial.json')
old=json.loads(oldpath.read_text());probe=json.loads((P/'graph.json').read_text());result=json.loads((P/'result.json').read_text())
cut={'ac','main_base','gammaH','main_root'}
expected=[[('root' if z=='main_root' else z) for z in row] for row in old['source'] if row[0] not in cut]
assert len(old['source'])==65 and probe['source']==expected and len(expected)==61
assert probe['witnesses']==old['witnesses'][:-1]+['root'] and len(probe['witnesses'])==14
assert probe['fixed_numerals']==old['fixed_numerals']==['beta','K0','MC','MF']
rows={x[0]:x[1:] for x in expected}
for name,expr in {'qm':['*','beta','J'],'q':['+','qm',1],'q2':['*','q','q'],'q3':['*','q2','q'],
 'X':['*','w','q'],'Y':['*','s','q3'],'E':['*','X','Y'],'k':['+','eta','zeta'],
 'kY':['*','k','Y'],'ell':['*','E','kY'],'c':['+','kY','eta'],'a':['+','E','Y'],
 'H':['+','four_a',3],'Delta':['+','a2','H'],'main_square':['*','root','root'],
 'N1':['-','main_square','Dc2'],'C':['-','qF','alpha'],'gap':['+','gap_product','alpha'],
 'R':['+','rproduct','mask'],'tau':['-','tau_partial','R'],'N0':['-','tau2','first_product'],
 'Nt':['-','transport_partial','zqm'],'V':['-','f2inner','c'],'normalized_S':['*','i','Dc2'],
 'Na':['+','aux_product','y2'],'scaled_Ns':['-','scaled_f2','normalized_S2'],
 'product0':['*','N0','N1'],'product1':['*','product0','Na'],'product3':['*','product1','Nt'],
 'product4':['*','product3','scaled_Ns'],'polynomial':['-','product4','Delta']}.items():assert rows[name]==expr,(name,rows[name])
# Verify topology and all witness and row liveness.
available=set(probe['witnesses']+probe['fixed_numerals']);used=set();seen=set()
for name,op,a,b in expected:
 assert name not in available and op in '+-*' and all(isinstance(x,int) or x in available for x in (a,b));available.add(name)
def walk(x):
 if isinstance(x,int):return
 if x not in rows:used.add(x);return
 if x in seen:return
 seen.add(x)
 for z in rows[x][1:]:walk(z)
walk(probe['output']);assert len(seen)==61 and used==set(probe['witnesses']+probe['fixed_numerals'])
# Independently load and authenticate each graph payload including metadata.
bind=old['coefficient_binding'];ports={};digests={}
for key,meta in bind['ports'].items():
 packed=(oldpath.parent/bind['path']/meta['file']).read_bytes();raw=gzip.decompress(packed)
 assert sha256(packed).hexdigest()==meta['gzip_sha256'] and sha256(raw).hexdigest()==meta['raw_sha256']
 val=int.from_bytes(raw,'big');assert len(raw)==meta['raw_bytes'] and val.bit_length()==meta['bits']
 ports[key]=val;digests[key]=sha256(raw).hexdigest()
beta,K,lo,mf=(ports[k] for k in ('beta','K0','MC','MF'));B=94517;q=1<<B;hi=mf-beta
assert beta==q-1 and 0<lo<beta<mf<2*beta
F=q-hi;alpha=lo+hi-beta;C=beta-lo
assert min(F,alpha,C)>0 and q-F-alpha==C
G=beta*(q-F)+alpha;R=G*(q*q-1)+lo+q*mf
assert G==q*(hi-1)+lo+1 and R==(G+1)*q*q-1
assert R%4==3 and R.bit_count()==3*B+2
N=(R-1)//2;assert N.bit_count()==3*B+1 and R>3*B+2 and N>=13
assert math.gcd(C,beta)==1
# One combined modular inversion is independent of the reviewed split inverse.
residue=pow(2,R%B,beta);combined=(C*residue)%beta
t=((F-K*C)*pow(combined,-1,beta))%beta
assert 0<t<beta and ((K+residue*t)*C-F)%beta==0
th=sha256(t.to_bytes((t.bit_length()+7)//8,'big')).hexdigest()
assert th==result['t_sha256'] and t.bit_length()==result['t_bits'] and R%B==result['R_mod_B']
# Test binomial floor and both Pell bounds for strictly larger X, without current enormous values.
def pell(A,j):
 x,y=1,0;delta=A*A-1
 for _ in range(j):x,y=A*x+delta*y,x+A*y
 return x,y
def v2(x):return (x&-x).bit_length()-1
count=0
for n in range(1,10):
 R0=2*n+1
 for multiplier in (2,3,5,11):
  X=max(multiplier,(144*n)//2**R0+1)*2**R0
  Y=sum(math.comb(2*n,j)*X**(n-j) for j in range(n+1))//2
  assert X>2**R0 and X>144*n
  assert Y>0 and v2(Y)==n.bit_count()-1
  M=X*Y*Y;a=Y*(X+1);tau,k0=pell(2*M+1,n+1);k=2*k0;root,c=pell(a+2,R0)
  assert Y*k<c<(Y+1)*k
  A=a+2;Pfirst=2*M+1;base=Fraction((X+1)**2,X)
  lower=Fraction((2*A-1)**2,2*Pfirst);upper=Fraction((2*A)**2,2*Pfirst-1)
  middle=base**n/2;eps=Fraction(9,Y)
  assert lower>base and upper<base+eps
  assert (base+eps)**(n-1)<2*base**(n-1)
  assert base**(n-1)<2*X**(n-1)
  assert Fraction(9*n,1)*base**(n-1)/Y < Fraction(36*n,X) < Fraction(1,4)
  assert 0<middle-Y<Fraction(1,4)
  assert middle<Fraction(c,k)<middle+Fraction(1,4)<Y+Fraction(1,2)
  H=4*a+3;assert (root-a*c-pow(2,R0,H))%H==0
  assert 0<X-2**R0<H and (root-X-a*c)%H!=0
  count+=1
# Independent quotient/Chebyshev and strong exponent controls.
def poly_next(p0,p1,t):return (4*t-2)*p1-p0
for A in range(2,7):
 for j in range(5):
  n=2*j+1;y=pell(A,n)[1];t0=1-A*A;p0,p1=1,4*t0-3
  for _ in range(j):p0,p1=p1,poly_next(p0,p1,t0)
  assert p0==(-1)**j*y
  p0,p1=1,-3
  for _ in range(j):p0,p1=p1,-2*p1-p0
  assert p0==(-1)**j*(2*j+1)
for A in range(2,5):
 delta=A*A-1
 for idx in (1,2,3):
  g,c=pell(A,idx);x,L=1,0
  for _ in range(c):x,L=g*x+delta*c*L,c*x+g*L
  assert L%(c*c)==0 and x*x-delta*L*L==1
print(json.dumps({'pins_sha256':sha256((D/'pins.json').read_bytes()).hexdigest(),
 'literal_65_to_61_cut_and_all_rows_checked':True,'all_four_port_payloads_authenticated':True,
 'transport_combined_inverse_verified':True,'rank_and_population_checked':True,
 'strictly_larger_X_finite_floor_controls':count,'strong_and_chebyshev_controls_checked':True,
 'huge_symbolic_witness_evaluated':False,'actual_original_zero_proved':False,'lean_executed':False},indent=2,sort_keys=True))
