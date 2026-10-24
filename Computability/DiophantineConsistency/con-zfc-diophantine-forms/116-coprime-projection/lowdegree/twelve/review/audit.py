#!/usr/bin/env python3
"""Independent twelve-integer exact cut-register audit. Does not import the builder."""
import copy, gzip, hashlib, json, math, random
from collections import Counter
from pathlib import Path
import sympy as s
OUT=Path(__file__).resolve().parent
ROOT=OUT.parents[1]
D=OUT.parent if (OUT.parent/'equation.json').is_file() else ROOT/'twelve_experiment'
COEFF=D.parent/'coefficients' if (D.parent/'coefficients').is_dir() else D.parent/'lowdegree/coefficients'
ROOT=COEFF.parent.parent
PARENT=ROOT/'baseline/budget/ZFC_Diophantine_Budget_Interpolation/guard/provenance/centered17'
p=json.loads((D/'equation.json').read_text())
V=['j','C','z','h','r','v','w','T','c','n','p2','p3']
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
 ('pos','p2*p2+p3*p3+p3+1'),
 ('Aroot','k+2*L'), ('Broot','6*a*I+12*I'),
 ('Croot','18*Q*V-9*V'),
 ('Dtau','1+L*L+L*k'), ('Da','(Q-1)*(Q*V*V-1)'),
 ('Ztotal','Z+U*Aroot+U*Broot+U*Croot'), ('U2','U*U'),
 ('sroot','Ztotal*Ztotal'), ('uroot','4*U2*Dtau'),
 ('vroot','36*U2*Df'), ('wroot','324*U2*Da'),
 ('guard_radicand','budget-pos'), ('eroot','729*U2*guard_radicand'),
 ('p','uroot*vroot'), ('q4','wroot*eroot'),
 ('u','uroot+vroot'), ('v4','wroot+eroot'), ('s','sroot-u-v4'),
 ('k4','s*s-4*u*v4+4*p+4*q4'), ('l4','s+2*v4'), ('m4','s+2*u'),
 ('even','k4*k4+16*p*l4*l4-16*q4*m4*m4-64*q4*p'),
 ('odd','k4*l4+8*q4*m4'), ('P','even*even-64*p*odd*odd')]

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
 require(counts=={'mul':90,'add':35,'sub':23},'count mismatch')
 return checked,dict(counts)
checked,counts=validate(p)
# Exact generic eight-root norm, independently expanded in eight formal ports.
zz,uu,AA,BB,CC,aa,bb,cc,xx=s.symbols('zz uu AA BB CC aa bb cc xx')
generic_vars=(zz,uu,AA,BB,CC,aa,bb,cc)
p3=4*(AA+BB)
p2=4*(AA+BB)**2+4*AA*BB-2*(aa+bb)
p1=4*(AA+BB)*(2*AA*BB-aa-bb)
p0=(aa-bb)**2-4*(AA+BB)*(AA*bb+BB*aa)
pair=(s.Integer(1),s.Integer(0))
for coeff in (p3*uu,p2*uu**2,p1*uu**3,p0*uu**4):
 left,right=pair
 pair=(s.expand(left*zz-right*uu*cc+coeff),s.expand(-left*uu+right*zz+2*CC*right*uu))
left,right=pair
Ngen=s.Poly(s.expand(left**2-2*CC*left*right-cc*right**2),*generic_vars)
D1=uu**2*(AA**2+aa);D2=uu**2*(BB**2+bb);D3=uu**2*(CC**2+cc)
S=(zz+uu*(AA+BB+CC))**2
STANDARD=((S+D3-D1-D2)**2-4*(S*D3+D1*D2))**2-64*S*D1*D2*D3
require(s.Poly(s.expand(STANDARD),*generic_vars)==Ngen,'Horner versus standard eight-root norm')
MONIC=s.Poly(s.expand(Ngen.as_expr().subs(zz,uu*(xx-AA-BB-CC))/uu**8),xx)
require(MONIC.degree()==8 and MONIC.LC()==1,'eight-root norm not monic')
require(all(uu not in coeff.free_symbols for coeff in MONIC.all_coeffs()),'uncleared normalized coefficient')
weights=(7,6,11,7,41,10,6,38)
weighted_degree=max(sum(i*j for i,j in zip(m,weights)) for m,coef in Ngen.terms())
leadterms=[(m,coef) for m,coef in Ngen.terms() if sum(i*j for i,j in zip(m,weights))==weighted_degree]
require(weighted_degree==242,'norm degree upper bound')
require(leadterms==[((1,7,2,1,4,0,0,0),s.Integer(128))],'unique weighted leading term')
# Independently build F16 by shifting F8 in a quadratic extension.
xx,tt,RR1,RR2,RR3,RR4=s.symbols('xx tt RR1 RR2 RR3 RR4')
F8=((xx**2+RR3-RR1-RR2)**2-4*(xx**2*RR3+RR1*RR2))**2-64*xx**2*RR1*RR2*RR3
shift=s.Poly(s.expand(F8.subs(xx,xx+tt)),tt)
even_part=s.Integer(0);odd_part=s.Integer(0)
for (ex,),cf in shift.terms():
 if ex%2:odd_part+=cf*RR4**(ex//2)
 else:even_part+=cf*RR4**(ex//2)
F16=s.Poly(s.expand(even_part**2-RR4*odd_part**2),xx,RR1,RR2,RR3,RR4)
up=RR1+RR2;vp=RR3+RR4;pp=RR1*RR2;qq=RR3*RR4
ss=xx**2-up-vp;kk=ss**2-4*up*vp+4*(pp+qq);ll=ss+2*vp;mm=ss+2*up
EV=kk**2+16*(pp*ll**2-qq*(mm**2+4*pp));OD=kk*ll+8*qq*mm
DIRECT16=s.Poly(s.expand(EV**2-64*pp*OD**2),xx,RR1,RR2,RR3,RR4)
require(F16==DIRECT16,'all coefficients of direct four-root norm')
require(s.Poly(F16.as_expr(),xx).degree()==16 and s.Poly(F16.as_expr(),xx).LC()==1,'four-root monicity')
# Full sparse centered F16 expansion, using Z -> Z-U*xi, xi^2=729*G0.
from collections import defaultdict
import math
EP=defaultdict(int);OP=defaultdict(int)
for exp,cf in Ngen.terms():
 for j0 in range(exp[0]+1):
  ex=list(exp)+[j0//2];ex[0]-=j0;ex[1]+=j0
  coeff=int(cf)*math.comb(exp[0],j0)*((-1)**j0)*729**(j0//2)
  (OP if j0%2 else EP)[tuple(ex)]+=coeff
EP={ex:cf for ex,cf in EP.items() if cf};OP={ex:cf for ex,cf in OP.items() if cf}
FULL16=defaultdict(int)
for poly,mult,shiftguard in [(EP,1,False),(OP,-729,True)]:
 terms=list(poly.items())
 for i0,(ex,cf) in enumerate(terms):
  for j0 in range(i0,len(terms)):
   ey,cg=terms[j0];ez=tuple(a+b for a,b in zip(ex,ey))
   if shiftguard:ez=ez[:-1]+(ez[-1]+1,)
   FULL16[ez]+=mult*cf*cg*(1 if i0==j0 else 2)
FULL16={ex:cf for ex,cf in FULL16.items() if cf}
weights16=weights+(16,)
weighted16=max(sum(a*b for a,b in zip(ex,weights16)) for ex in FULL16)
leading16=[(ex,cf) for ex,cf in FULL16.items() if sum(a*b for a,b in zip(ex,weights16))==weighted16]
require(weighted16==500 and leading16==[((0,16,4,0,8,0,0,0,2),2**12*729**2)],'complete centered degree500 certificate')
# Exact leading components of the actual front end, before Horner cancellations.
top=[];deg=[]
for node in p['nodes'][:p['named_registers']['Croot']+1]:
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
frontnames=['Z','U','Aroot','Broot','Croot','aroot','broot','croot']
actual_weights=tuple(deg[p['named_registers'][n]] for n in frontnames[:5])+(2*deg[p['named_registers']['k']],2*deg[p['named_registers']['I']],2*deg[p['named_registers']['V']])
require(actual_weights==weights,'actual front and defect degrees')
def lt(name):return top[p['named_registers'][name]]
Gtop=lt('budget')
require(deg[p['named_registers']['budget']]==16,'guard radicand degree')
Ptop=s.Poly(s.expand(2**12*729**2*lt('U')**16*lt('Aroot')**4*lt('Croot')**8*Gtop**2),*[SYM[x] for x in V])
mon={x:0 for x in V};mon.update(j=228,w=76,v=84,h=8,z=8,r=32,c=64)
coef=Ptop.coeff_monomial(tuple(mon[x] for x in V))
require(s.expand(coef-2**488*3**332*SYM['beta']**228)==0,'actual selected degree500 coefficient')
require(Ptop.total_degree()==500,'actual top degree')
rowdegrees={'P':500,'guard_radicand':16}
# All three exact defects, including the integer auxiliary radicand.
a,ell,k,I,Q,Vv=s.symbols('a ell k I Q Vv')
require(s.expand((2*ell*k+k)**2+4-k*k-4*(1+ell*(ell+1)*k*k))==0,'first defect')
require(s.expand((6*(a+2)*I)**2+36*(1-I*I)-36*(1+(a*a+4*a+3)*I*I))==0,'strong defect')
Da=(Q-1)*(Q*Vv*Vv-1)
require(s.expand((9*(2*Q-1)*Vv)**2+81*(4-4*Q-Vv*Vv)-324*Da)==0,'auxiliary defect')
# The integer auxiliary square implies the rational adjacent-Pell equation.
e=s.Symbol('e')
require(s.factor((Q*Vv*Vv-(Q-1)*(e/(Q-1))**2-1)*(Q-1)-(Da-e*e))==0,'auxiliary restoration identity')
# Exhaustion of the finite residue classes is a universal modular certificate.
for yy in range(3):
 for kk in range(3):
  ellmod=2*yy*yy
  require((1+ellmod*(ellmod+1)*kk*kk)%3==1,'first radicand residue')
require((1+0)%3==1 and ((-1)*(-1))%3==1,'other radicand residues')
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
for name in ['Klo','P','Dtau','Da','Ztotal','sroot','uroot','vroot','wroot','eroot','guard_radicand','p','q4','u','v4','s','k4','l4','m4','even','odd','Df','Croot','F','R','Z']:
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
 'variables':12,'operations':sum(counts.values()),'operation_counts':counts,
 'checked_named_registers':len(checked),'row_degrees':rowdegrees,'exact_total_degree':500,
 'selected_monomial':mon,'selected_coefficient':'2^488 * 3^332 * beta^228 > 0',
 'direct_norm_terms':len(F16.terms()),'generic_centered_norm_terms':len(FULL16),'generic_norm_weighted_degree':weighted16,'generic_norm_weights':dict(zip(frontnames+['guard_radicand'],weights16)),'monic_norm_degree':16,'payload_raw_sha256':payloads,'source_payload_byte_comparison_performed':source_byte_comparison,'rejected_mutations':mutations,'supplementary_CRT_cases':crt_cases}
centered_certificate={'variables':frontnames+['guard_radicand'],'weights':list(weights16),'weighted_degree':weighted16,'term_count':len(FULL16),'unique_top_term':{'exponents':[0,16,4,0,8,0,0,0,2],'coefficient':2**12*729**2},'terms':[{'exponents':list(ex),'coefficient':cf} for ex,cf in sorted(FULL16.items())]}
centered_bytes=(json.dumps(centered_certificate,separators=(',',':'))+'\n').encode()
(OUT/'GENERIC_CENTERED_NORM_CERTIFICATE.json.gz').write_bytes(gzip.compress(centered_bytes,mtime=0))
result['centered_certificate_raw_sha256']=hashlib.sha256(centered_bytes).hexdigest()
(OUT/'DIRECT_NORM_CERTIFICATE.json').write_text(json.dumps({'variables':['total_center','radicand1','radicand2','radicand3','radicand4'],'term_count':len(F16.terms()),'terms':[{'exponents':list(ex),'coefficient':int(cf)} for ex,cf in F16.terms()]},indent=2)+'\n')
(OUT/'CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','variables','operations','operation_counts','row_degrees','exact_total_degree','rejected_mutations']},indent=2))
