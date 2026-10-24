#!/usr/bin/env python3
"""Independent fourteen-integer exact cut-register audit. Does not import the builder."""
import copy, gzip, hashlib, json, math, random
from collections import Counter
from pathlib import Path
import sympy as s
OUT=Path(__file__).resolve().parent
D=OUT.parent if (OUT.parent/'equation.json').is_file() else OUT.parents[1]/'lowdegree/fourteen'
ROOT=D.parents[1]
COEFF=D.parent/'coefficients'
PARENT=ROOT/'baseline/budget/ZFC_Diophantine_Budget_Interpolation/guard/provenance/centered17'
p=json.loads((D/'equation.json').read_text())
V=['j','C','z','h','r','v','w','T','c','n','y','p1','p2','p3']
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
# Independently written defining expressions, algebraically different at cuts.
FORMS=[
 ('J','1+6*j'), ('qm','J*beta'), ('q','1+qm'), ('W','4+12*w'),
 ('X','W*q'), ('Y','v*q'), ('F','C*K0+C*W-qm*z'),
 ('R','(q*q-q*F-C)*(q*q-1)+(MC+q*MF)*J'),
 ('E','Y*X'), ('a','Y+E'), ('H','3+4*a'), ('Delta','H+a*a'),
 ('k','1+R+h*E'), ('eta','c-k*Y'), ('L','k*Y*E'),
 ('I','c*c+2*r*c*c'), ('Dfminus1','I*I*Delta'), ('Df','1+Dfminus1'),
 ('Q','Dfminus1*Delta'), ('V','Df*c*T-Df*R-c'), ('M','2*q*q'), ('U','H*M'),
 ('Klo','2*(X*X-1)-3*c*X'),
 ('Z','H*v-H*q*q+M*Klo+U*n'),
 ('Derr','cone_A**2*F**2-2*cone_A*F*q+q*q+cone_B**2*C**2-2*cone_B*C*q+q*q'),
 ('budget','k*k*q*q-k*k*Derr-4*q*q*eta*eta'),
 ('pos','p1*p1+p2*p2+p3*p3+p3+1'),
 ('Aroot','k+2*L'), ('Broot','2*a*I+4*I'),
 ('Dtau','1+L*L+L*k'), ('E0','Z+U*Aroot+U*Broot'), ('U2','U*U'),
 ('Ninner','E0*E0-4*U2*Dtau-4*U2*Df'),
 ('N','Ninner*Ninner-64*U2*U2*Dtau*Df'),
 ('auxiliary','V*V-2*Q*y*V-Q*y*y+2*y*V+y*y-1'),
 ('guard','budget-pos'),
 ('P','N*N+guard*guard+auxiliary*auxiliary')]
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
 require(counts=={'mul':69,'add':30,'sub':20},'count mismatch')
 return checked,dict(counts)
checked,counts=validate(p)
# Exact generic norm identity; the current evaluator is direct, the comparison
# formula is the previously audited double-centered polynomial.
zz,uu,AA,BB,aa,bb,xx=s.symbols('zz uu AA BB aa bb xx')
DD=zz**2+2*BB*uu*zz+uu**2*(aa-bb)
EE=zz+uu*(AA+BB)
BF=AA*(zz**2+2*BB*uu*zz-bb*uu**2)-aa*uu*(zz+uu*BB)
Ngen=s.Poly(s.expand(DD**2+4*uu*EE*BF),zz,uu,AA,BB,aa,bb)
RAD_A=AA**2+aa;RAD_B=BB**2+bb
CANON=(EE**2-uu**2*(RAD_A+RAD_B))**2-4*uu**4*RAD_A*RAD_B
require(s.Poly(s.expand(CANON),zz,uu,AA,BB,aa,bb)==Ngen,'direct versus double-centered norm')
MONIC=s.Poly(s.expand(CANON.subs(zz,uu*(xx-AA-BB))/uu**4),xx)
require(MONIC.degree()==4 and MONIC.LC()==1,'quartic not monic')
weights=(7,6,11,7,10,6)
weighted_degree=max(sum(i*j for i,j in zip(m,weights)) for m,coef in Ngen.terms())
leadterms=[(m,coef) for m,coef in Ngen.terms() if sum(i*j for i,j in zip(m,weights))==weighted_degree]
require(weighted_degree==54 and leadterms==[((1,3,2,1,0,0),s.Integer(8))],'generic norm weighted leading term')
# Exact front-end homogeneous components, without propagating syntactic norm degrees.
top=[];deg=[]
for node in p['nodes'][:p['named_registers']['Broot']+1]:
 op=node[0]
 if op=='integer':d=0;hh=s.Integer(node[1])
 elif op=='coefficient':d=0;hh=SYM[node[1]]
 elif op=='variable':d=1;hh=SYM[node[1]]
 else:
  i,j=node[1:]
  if op=='mul':d=deg[i]+deg[j];hh=top[i]*top[j]
  elif deg[i]>deg[j]:d=deg[i];hh=top[i]
  elif deg[j]>deg[i]:d=deg[j];hh=top[j] if op=='add' else -top[j]
  else:d=deg[i];hh=s.expand(top[i]+top[j] if op=='add' else top[i]-top[j])
  require(hh!=0,'unresolved front leading cancellation')
 top.append(hh);deg.append(d)
def lt(n):return top[p['named_registers'][n]]
actual_weights=tuple(deg[p['named_registers'][n]] for n in ['Z','U','Aroot','Broot'])+(2*deg[p['named_registers']['k']],2*deg[p['named_registers']['I']])
require(actual_weights==weights,'actual front and defect degrees')
Ntop=8*lt('Z')*lt('U')**3*lt('Aroot')**2*lt('Broot')
Ptop=s.Poly(s.expand(Ntop**2),*[SYM[x] for x in V])
mon={x:0 for x in V};mon.update(j=56,w=18,v=22,h=4,r=2,c=4,n=2)
coef=Ptop.coeff_monomial(tuple(mon[x] for x in V))
require(s.expand(coef-2**130*3**74*SYM['beta']**56)==0,'attainment coefficient')
auxdegree=deg[p['named_registers']['Q']]+1+deg[p['named_registers']['V']]
require(auxdegree==42 and deg[p['named_registers']['budget']]==16,'other rows')
rowdegrees={'N':54,'auxiliary':42,'guard':16}
# The defects identify the direct radicands with the generic centered ports.
a,ell,k,II=s.symbols('a ell k II')
require(s.expand(((2*ell*k+k)**2+4-k*k)-4*(1+ell*(ell+1)*k*k))==0,'first centered defect')
require(s.expand((2*(a+2)*II)**2+4*(1-II**2)-4*(1+(a*a+4*a+3)*II**2))==0,'strong centered defect')
# Authenticate every complete payload against inherited bytes, not bounds alone.
TRUSTED_RAW_SHA256={'beta': '6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea', 'K0': '18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af', 'MC': '3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777', 'MF': '78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722', 'cone_A': '66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615', 'cone_B': '42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}
binding=json.loads((COEFF/'BINDING.json').read_text()); ports={};payloads={}
source_byte_comparison=(PARENT/'coefficients').is_dir()
for n in PORTS:
 info=binding['payloads'][n];data=gzip.decompress((COEFF/info['file']).read_bytes())
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
for name in ['Klo','N','Ninner','Dtau','E0','U2','Df','Dfminus1','Aroot','Broot','auxiliary','guard','P','F','R','Z']:
 mutant=copy.deepcopy(p);ix=p['named_registers'][name];old=mutant['nodes'][ix][0]
 mutant['nodes'][ix][0]='add' if old!='add' else 'sub'
 try:validate(mutant)
 except ValueError:mutations.append(name)
 else:raise ValueError('mutation accepted '+name)
# Supplementary CRT diagnostics, explicitly including zero and negative v.
crt_cases=0
for bb in [31,127,511]:
 for jj in range(-8,9):
  qq=bb*(6*jj+1)+1
  for ww in range(-4,5):
   xx=qq*(12*ww+4)
   for vv in range(-5,6):
    hh=4*(xx+1)*qq*vv+3
    require(qq and hh and math.gcd(hh,2*qq*qq)==1,'CRT diagnostic')
    crt_cases+=1
result={'status':'pass','scope':'Exact literal-DAG identities, liveness, degree attainment, source coefficient bytes, and mutation controls. Unbounded semantic proof is reviewed separately.',
 'equation_sha256':hashlib.sha256((D/'equation.json').read_bytes()).hexdigest(),
 'variables':14,'operations':sum(counts.values()),'operation_counts':counts,
 'checked_named_registers':len(checked),'row_degrees':rowdegrees,'exact_total_degree':108,
 'selected_monomial':mon,'selected_coefficient':'2^130 * 3^74 * beta^56 > 0',
 'payload_raw_sha256':payloads,'source_payload_byte_comparison_performed':source_byte_comparison,'rejected_mutations':mutations,'supplementary_CRT_cases':crt_cases}
(OUT/'CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','variables','operations','operation_counts','row_degrees','exact_total_degree','rejected_mutations']},indent=2))
