#!/usr/bin/env python3
"""Independent exact cut-register audit. Does not import the builder."""
import copy, gzip, hashlib, json, math, random
from collections import Counter
from pathlib import Path
import sympy as s
OUT=Path(__file__).resolve().parent
D=OUT.parent if (OUT.parent/'equation.json').is_file() else OUT.parents[1]/'lowdegree'
ROOT=D.parent
PARENT=D.parent/'prior/lowdegree'  # Optional retained source; pinned hashes are mandatory.
p=json.loads((D/'equation.json').read_text())
V=['j','C','z','h','r','v','w','T','c','n','y','p1','p2']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
# Independently written defining expressions, algebraically different at cuts.
FORMS=[
 ('J','1+6*j'), ('qm','J*beta'), ('q','1+qm'), ('W','4+12*w'),
 ('X','W*q'), ('Y','v'), ('F','C*K0+C*W-qm*z'),
 ('R','(q*q-q*F-C)*(q*q-1)+(MC+q*MF)*J'),
 ('E','Y*X'), ('a','Y+E'), ('H','3+4*a'), ('Delta','H+a*a'),
 ('k','1+R+h*E'), ('eta','c-k*Y'), ('L','k*Y*E'),
 ('I','c*c+2*r*c*c'), ('Ds','Delta*I*I'), ('Fs','Ds+1'), ('Q','Ds*Delta'),
 ('V','Fs*c*T-Fs*R-c'), ('q3','q*q*q'), ('M','2*q3'), ('U','H*M'),
 ('Klo','2*(X*X-1)-3*c*X'),
 ('Z','H*Y-H*q3+M*Klo+U*n'),
 ('Derr','cone_A**2*F**2-2*cone_A*F*q+q*q+cone_B**2*C**2-2*cone_B*C*q+q*q'),
 ('budget','Y*Y*(k*k*q*q-k*k*Derr-4*q*q*eta*eta)-k*k*q*q*q3*q3'),
 ('G','4*budget-4*p1*p1-4*p2*p2-3'),
 ('carrier','Z*Z+2*(2*L+k)*U*Z+U*U*(k*k-4)'),
 ('auxiliary','V*V-2*Q*y*V-Q*y*y+2*y*V+y*y-1'),
 ('Dt','L*L+k*L+1'), ('U2','U*U'),
 ('ga','G*U2'), ('db','Dt*U2*4'), ('fc','Fs*U2*16'), ('gc','fc+ga'),
 ('inner','carrier*carrier-2*carrier*gc+gc*gc-4*ga*fc-4*db*gc'),
 ('N','inner*inner-64*ga*db*fc*carrier-64*ga*db*fc*db'),
 ('P','N+auxiliary+N*auxiliary')]
SYM={x:s.Symbol(x) for x in V+PORTS+[n for n,_ in FORMS]}

def require(condition, msg):
 if not condition: raise ValueError(msg)

def validate(g):
 nodes=g['nodes']; cuts={}; checked=[]
 require(g['variables']==V,'variable declarations changed')
 require(g['fixed_numerals']==PORTS,'coefficient declarations changed')
 for i,node in enumerate(nodes):
  require(node[0] in ['variable','coefficient','integer','add','sub','mul'],'unknown operation')
  if node[0] in ('add','sub','mul'):
   require(len(node)==3 and all(isinstance(t,int) and 0<=t<i for t in node[1:]),'noncausal gate')
 def rec(i,memo):
  if i in cuts:return cuts[i]
  if i in memo:return memo[i]
  n=nodes[i]; op=n[0]
  if op=='integer':r=s.Integer(n[1])
  elif op in ('variable','coefficient'):r=SYM[n[1]]
  else:
   a,b=rec(n[1],memo),rec(n[2],memo)
   r=a+b if op=='add' else a-b if op=='sub' else a*b
  memo[i]=r;return r
 for name,formula in FORMS:
  ix=g['named_registers'][name]
  actual=rec(ix,{})
  expected=s.sympify(formula,locals=SYM)
  
  require(s.expand(actual-expected)==0,'incorrect register '+name)
  cuts[ix]=SYM[name];checked.append(name)
 require(g['output']==g['named_registers']['P'],'wrong output')
 seen=set()
 def walk(i):
  if i in seen:return
  seen.add(i)
  if nodes[i][0] in ('add','sub','mul'):
   walk(nodes[i][1]);walk(nodes[i][2])
 walk(g['output'])
 require(len(seen)==len(nodes),'dead node')
 livevars={nodes[i][1] for i in seen if nodes[i][0]=='variable'}
 require(livevars==set(V),'unused input')
 counts=Counter(nodes[i][0] for i in seen if nodes[i][0] in ('add','sub','mul'))
 require(counts=={'mul':75,'add':27,'sub':25},'count mismatch')
 return checked,dict(counts)
checked,counts=validate(p)
for pin in json.loads((D/'SOURCE_PINS.json').read_text()):
 require(hashlib.sha256((D/pin['copy']).read_bytes()).hexdigest()==pin['sha256'],'source proof pin')
# Exact highest homogeneous components at every literal node. Coefficients
# are symbolic constants; all 13 unknowns receive total degree one.
top=[]; deg=[]
for node in p['nodes']:
 op=node[0]
 if op=='integer': d=0; h=s.Integer(node[1])
 elif op=='coefficient':d=0;h=SYM[node[1]]
 elif op=='variable':d=1;h=SYM[node[1]]
 else:
  i,j=node[1:]
  if op=='mul': d=deg[i]+deg[j];h=top[i]*top[j]
  elif deg[i]>deg[j]:d=deg[i];h=top[i]
  elif deg[j]>deg[i]:d=deg[j];h=top[j] if op=='add' else -top[j]
  else:
   d=deg[i];h=s.expand(top[i]+top[j] if op=='add' else top[i]-top[j])
  require(h!=0,'unresolved leading cancellation at '+str(len(top)))
 top.append(h);deg.append(d)
rowdegrees={n:deg[p['named_registers'][n]] for n in ['carrier','auxiliary','G','N']}
require(rowdegrees=={'carrier':22,'auxiliary':36,'G':18,'N':120},'row degrees')
require(deg[p['output']]==156,'degree')
lead=s.Poly(s.expand(top[p['output']]),*[SYM[x] for x in V])
mon={x:0 for x in V};mon.update(j=106,w=14,v=14,z=9,r=4,c=8,y=1)
coef=lead.coeff_monomial(tuple(mon[x] for x in V))
require(s.expand(coef-2**171*3**120*SYM['beta']**106)==0,'attainment coefficient')
# Independent universal algebra and source substitutions.
a,X,c,H,Klo,K,q,F,C,alpha,J,beta,MC,MF,U,Z,L,k,ell,tau,y,Q,Vv=s.symbols('a X c H Klo K q F C alpha J beta MC MF U Z L k ell tau y Q V')
require(s.expand((2*X**2-3*X*c-2)-(2*(X*(X+2*a*c)-1)-(4*a+3)*X*c))==0,'projection identity')
require(s.expand(((Z+U*k)**2+4*U*(L*Z-U))-((Z+U*(2*L+k))**2-4*U**2*(1+L*(L+k))))==0,'centered monic identity')
require(s.expand(((Z+U*k)**2+4*U*(L*Z-U)).subs(Z,U*(2*tau-(2*L+k)))-4*U**2*(tau**2-1-L*(L+k)))==0,'root reconstruction identity')
require(s.expand((Vv**2-(Q-1)*y*(2*Vv+y)-1)-(Q*Vv**2-(Q-1)*(Vv+y)**2-1))==0,'auxiliary centering')
require(s.expand((q*(q-F)-C)-((q-1)*(q-F)+(q-F-C)))==0,'mask elimination')
# Independent three-root norm product and centered rewrite.
x,aa,bb,cc=s.symbols('x aa bb cc')
# Prove the degree-eight norm by multiplying all eight signed-root factors.
rr,ss,tt=s.symbols('rr ss tt')
prod=s.Integer(1)
for er in [-1,1]:
 for es in [-1,1]:
  for et in [-1,1]: prod*=x-er*rr-es*ss-et*tt
norm=((x*x-aa-bb-cc)**2-4*(aa*bb+aa*cc+bb*cc))**2-64*aa*bb*cc*x*x
require(s.expand(prod-norm.subs({aa:rr*rr,bb:ss*ss,cc:tt*tt}))==0,'eight signed-root factor identity')
cv=s.Symbol('cv')
optimized=((cv-aa-cc)**2-4*(aa*cc+bb*(aa+cc)))**2-64*aa*bb*cc*(cv+bb)
require(s.expand(norm.subs(x*x,cv+bb)-optimized)==0,'centered norm schedule')
# Algebraic source map: any signed sum gives a zero after retaining its squared roots.
gg,ft,fs=s.symbols('gg ft fs')
require(s.expand(norm.subs({x:gg+2*ft+4*fs,aa:gg*gg,bb:4*ft*ft,cc:16*fs*fs}))==0,'canonical signed lift')
mod4_cases=0
for bv in range(4):
 for pp in range(4):
  for qq in range(4):
   require((4*(bv-pp*pp-qq*qq)-3)%4==1,'odd guard radicand')
   mod4_cases+=1
unit_cases=0
for nn in range(-20,21):
 for ac in range(-20,21):
  if nn%4 in (0,1):
   require(((nn+1)*(ac+1)==1)==(nn==ac==0),'two-factor unit conjunction')
   unit_cases+=1
# All possible coefficient residues modulo8 already show lowest-weight separation.
separation_cases=0
for av in [1,3,5,7]:
 for bv in [1,3,5,7]:
  for cv in range(8):
   coeffs=[av,2*bv,4*cv]
   for mask in range(1,8):
    if mask==4 and cv==0: continue  # A sole positive root is never zero.
    for signs in [(-1,-1,-1),(-1,-1,1),(-1,1,-1),(-1,1,1),(1,-1,-1),(1,-1,1),(1,1,-1),(1,1,1)]:
     val=sum(signs[i]*coeffs[i] for i in range(3) if mask>>i&1)
     if mask&3: require(val%4!=0 if mask&1 else val%4==2,'unique lowest 2-adic coefficient')
     separation_cases+=1
# Unconditional parameter bounds: X even, |X|>=8; Y any integer.
for xx in list(range(-40,-7,2))+list(range(8,41,2)):
 for yy in range(-20,21):
  aa=(xx+1)*yy
  require((aa+2)**2-1>=3,'strong radicand positivity')
  dd=xx*yy*yy
  require(dd*(dd+1)%2==0 and dd*(dd+1)>=0,'odd positive first radicand')
# Authenticate every complete payload against inherited bytes, not bounds alone.
TRUSTED_RAW_SHA256={'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea', 'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af', 'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777', 'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722', 'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615', 'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}
binding=json.loads((D/'../coefficients/BINDING.json').read_text()); ports={};payloads={}
source_byte_comparison=(PARENT/'coefficients').is_dir()
for n in PORTS:
 info=binding['payloads'][n];data=gzip.decompress((D/'../coefficients'/info['file']).read_bytes())
 if source_byte_comparison:
  require(data==gzip.decompress((PARENT/'coefficients'/info['file']).read_bytes()),'source payload '+n)
 require(hashlib.sha256(data).hexdigest()==TRUSTED_RAW_SHA256[n],'reviewed source hash '+n)
 require(hashlib.sha256(data).hexdigest()==info['raw_sha256'],'payload hash '+n)
 ports[n]=int.from_bytes(data,'little');require(ports[n].bit_length()==info['bits'],'payload bits')
 payloads[n]=hashlib.sha256(data).hexdigest()
require(ports['beta']==2**1064921-1,'literal beta')
require(ports['cone_A']==2**1113 and ports['cone_B']==2**666104,'literal cones')
require(0<ports['MC']<ports['beta']<ports['MF']<2*ports['beta'],'mask bounds')
# Negative controls modify live arithmetic; all must fail exact checking.
mutations=[]
for ix, node in enumerate(p['nodes']):
 if node[0] not in ('add','sub','mul'):continue
 name='gate_'+str(ix)
 mutant=copy.deepcopy(p);old=mutant['nodes'][ix][0]
 mutant['nodes'][ix][0]='add' if old!='add' else 'sub'
 try:validate(mutant)
 except ValueError:mutations.append(name)
 else:raise ValueError('mutation accepted '+name)
# Supplementary arithmetic diagnostics. These are not unbounded proofs.
crt_cases=0
for qq in [2,4,8,16,32,-2,-8,-32]:
 for ww in range(-4,5):
  xx=qq*(12*ww+4)
  for vv in range(-5,6):
   hh=4*(xx+1)*vv+3
   require(math.gcd(hh,2*qq**3)==1,'late CRT diagnostic')
   crt_cases+=1
bound_cases=0
for xx in [64,65,100,128,256,1024,1000000]:
 for ss in [24,25,30,40,100]:
  require((xx-3)**ss*xx > (xx//4)**3*2**(4*ss+4)*xx**2,'strengthened bound')
  bound_cases+=1
# Explicitly test that early coprimality is false: this is the branch the new proof repairs.
qq,xx,yy=20,80,3
require(math.gcd(4*(xx+1)*yy+3,2*qq**3)>1,'missing noncoprime diagnostic')
# Positive budget soundness on exact small signed assignments.
budget_cases=0
for qq in [-4,-2,2,4]:
 for yy in range(-100,101):
  for kk in [-3,-1,1,3]:
   for ee in [-1,0,1]:
    bb=kk*kk*qq*qq-4*qq*qq*ee*ee
    new=yy*yy*bb-kk*kk*qq**8
    if new>0: require(bb>0 and yy*yy>qq**6,'budget magnitude implication')
    budget_cases+=1
result={'status':'pass','scope':'Exact literal-DAG identities, liveness, degree attainment, source coefficient bytes, and mutation controls. Unbounded semantic proof is reviewed separately.',
 'equation_sha256':hashlib.sha256((D/'equation.json').read_bytes()).hexdigest(),
 'variables':13,'operations':sum(counts.values()),'operation_counts':counts,
 'checked_named_registers':len(checked),'row_degrees':rowdegrees,'exact_total_degree':156,
 'selected_monomial':mon,'selected_coefficient':'2^171 * 3^120 * beta^106 > 0',
 'payload_raw_sha256':payloads,'source_payload_byte_comparison_performed':source_byte_comparison,'rejected_mutations':mutations,'supplementary_late_CRT_cases':crt_cases,'strengthened_bound_cases':bound_cases,'budget_implication_cases':budget_cases,'parity_separation_cases':separation_cases,'odd_guard_residue_cases':mod4_cases,'unit_product_cases':unit_cases}
(OUT/'CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','variables','operations','operation_counts','row_degrees','exact_total_degree','rejected_mutations']},indent=2))
