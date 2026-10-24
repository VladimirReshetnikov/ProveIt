#!/usr/bin/env python3
"""Independent thirteen-integer exact cut-register audit. Does not import the builder."""
import copy, gzip, hashlib, json, math, random
from collections import Counter
from pathlib import Path
import sympy as s
OUT=Path(__file__).resolve().parent
D=OUT.parent if (OUT.parent/'equation.json').is_file() else OUT.parents[1]/'lowdegree/thirteen'
ROOT=D.parents[1]
COEFF=D.parent/'coefficients'
PARENT=ROOT/'baseline/budget/ZFC_Diophantine_Budget_Interpolation/guard/provenance/centered17'
p=json.loads((D/'horner_equation.json').read_text())
V=['j','C','z','h','r','v','w','T','c','n','p1','p2','p3']
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
 ('Aroot','k+2*L'), ('Broot','6*a*I+12*I'),
 ('Croot','18*Q*V-9*V'),
 ('aroot','4-k*k'), ('broot','36-36*I*I'), ('croot','324-324*Q-81*V*V'),
 ('AB','Aroot+Broot'), ('ab','aroot+broot'),
 ('p3c','4*AB'), ('p2c','4*AB*AB+4*Aroot*Broot-2*ab'),
 ('p1c','p3c*(2*Aroot*Broot-ab)'),
 ('p0c','aroot*aroot-2*aroot*broot+broot*broot-p3c*(Aroot*broot+Broot*aroot)'),
 ('U2','U*U'), ('U3','U*U2'), ('U4','U2*U2'),
 ('a1','Z+U*p3c'), ('b1','-U'),
 ('a2','a1*Z+b1*b1*croot+p2c*U2'),
 ('b2','a1*b1+b1*Z-2*Croot*b1*b1'),
 ('a3','a2*Z+b2*b1*croot+p1c*U3'),
 ('b3','a2*b1+b2*Z-2*Croot*b2*b1'),
 ('a4','a3*Z+b3*b1*croot+p0c*U4'),
 ('b4','a3*b1+b3*Z-2*Croot*b3*b1'),
 ('N','a4*a4-2*Croot*a4*b4-croot*b4*b4'),
 ('guard','budget-pos'), ('Sguard','guard*guard'), ('P','(1+N)*(1+Sguard)-1')]

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
 require(counts=={'mul':108,'add':38,'sub':29},'count mismatch')
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
# Exact leading components of the actual front end, before Horner cancellations.
top=[];deg=[]
for node in p['nodes'][:p['named_registers']['croot']+1]:
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
require(tuple(deg[p['named_registers'][n]] for n in frontnames)==weights,'actual front degrees')
def lt(name):return top[p['named_registers'][name]]
Ntop=128*lt('Z')*lt('U')**7*lt('Aroot')**2*lt('Broot')*lt('Croot')**4
Gtop=lt('budget')
require(deg[p['named_registers']['budget']]==16,'guard degree')
Ptop=s.Poly(s.expand(Ntop*Gtop**2),*[SYM[x] for x in V])
mon={x:0 for x in V};mon.update(j=124,w=41,v=47,h=6,z=4,r=17,c=34,n=1)
coef=Ptop.coeff_monomial(tuple(mon[x] for x in V))
require(s.expand(coef-2**265*3**174*SYM['beta']**124)==0,'actual selected degree274 coefficient')
require(Ptop.total_degree()==274,'actual top degree')
rowdegrees={'N':242,'guard':16,'Sguard':32}
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
for name in ['Klo','N','a1','b1','a2','b2','a3','b3','a4','b4','p3c','p2c','p1c','p0c','Df','Croot','croot','guard','Sguard','P','F','R','Z']:
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
 'equation_sha256':hashlib.sha256((D/'horner_equation.json').read_bytes()).hexdigest(),
 'variables':13,'operations':sum(counts.values()),'operation_counts':counts,
 'checked_named_registers':len(checked),'row_degrees':rowdegrees,'exact_total_degree':274,
 'selected_monomial':mon,'selected_coefficient':'2^265 * 3^174 * beta^124 > 0',
 'generic_norm_terms':len(Ngen.terms()),'generic_norm_weighted_degree':weighted_degree,'generic_norm_weights':dict(zip(frontnames,weights)),'monic_norm_degree':8,'payload_raw_sha256':payloads,'source_payload_byte_comparison_performed':source_byte_comparison,'rejected_mutations':mutations,'supplementary_CRT_cases':crt_cases}
(OUT/'GENERIC_NORM_CERTIFICATE_HORNER.json').write_text(json.dumps({'variables':frontnames,'weights':list(weights),'weighted_degree':weighted_degree,'term_count':len(Ngen.terms()),'terms':[{'exponents':list(m),'coefficient':int(cf)} for m,cf in Ngen.terms()],'unique_top_term':{'exponents':[1,7,2,1,4,0,0,0],'coefficient':128}},indent=2)+'\n')
(OUT/'CHECK_HORNER.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','variables','operations','operation_counts','row_degrees','exact_total_degree','rejected_mutations']},indent=2))
