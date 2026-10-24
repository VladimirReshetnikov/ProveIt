#!/usr/bin/env python3
"""Independent wave15 audit. Does not import or execute producer code.

Usage: python independent_audit.py [new-lowdegree-directory] [prior-lowdegree-directory]
The semantic proof is in INDEPENDENT_REVIEW.md; exact finite checks are here.
"""
import ast, collections, copy, gzip, hashlib, json, math, sys
from pathlib import Path
import sympy as S
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[1]
NEW=Path(sys.argv[1]) if len(sys.argv)>1 else BASE/'lowdegree'
OLD=Path(sys.argv[2]) if len(sys.argv)>2 else BASE/'prior/ZFC_Diophantine_Coprime_Projection/lowdegree'
VARS='j C z h r v w T c n f y p1 p2 p3'.split()
PORTS='beta K0 MC MF cone_A cone_B'.split()
# Independent expanded formulas, not imported from either build or specification.
DEFS=[
 ('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('W','4+12*w'),
 ('X','W*q'),('Y','v*q'),('F','K0*C+W*C-qm*z'),
 ('R','(q*q-q*F-C)*(q*q-1)+J*MC+J*q*MF'),
 ('E','Y*X'),('a','Y+E'),('H','3+4*a'),('Delta','H+a*a'),
 ('k','1+R+E*h'),('eta','c-k*Y'),('L','k*E*Y'),
 ('I','c*c+2*c*c*r'),('Q','Delta*f*f-Delta'),
 ('V','f*f*c*T-f*f*R-c'),('M','2*q*q'),('U','H*M'),
 ('Klo','2*X*X-3*c*X-2'),('Z','H*v-H*q*q+M*Klo+U*n'),
 ('Derr','cone_A*cone_A*F*F-2*cone_A*F*q+2*q*q+cone_B*cone_B*C*C-2*cone_B*C*q'),
 ('budget','k*k*q*q-k*k*Derr-4*q*q*eta*eta'),
 ('pos','1+p1*p1+p2*p2+p3*p3+p3'),
 ('carrier','Z*Z+4*U*L*Z+2*U*k*Z+U*U*k*k-4*U*U'),
 ('strong','f*f-1-Delta*I*I'),
 ('auxiliary','V*V-2*Q*y*V-Q*y*y+2*y*V+y*y-1'),
 ('guard','budget-pos'),
 ('P','carrier*carrier+strong*strong+auxiliary*auxiliary+guard*guard')]
NAMES=VARS+PORTS+[n for n,_ in DEFS]
SYM=dict(zip(NAMES,S.symbols(' '.join(NAMES))))
OPS={'add','sub','mul'}

def need(condition,message):
 if not condition: raise ValueError(message)
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def parse(expr,env):
 def r(t):
  if isinstance(t,ast.Name):return env[t.id]
  if isinstance(t,ast.Constant) and type(t.value) is int:return S.Integer(t.value)
  if isinstance(t,ast.UnaryOp) and isinstance(t.op,ast.USub):return -r(t.operand)
  if isinstance(t,ast.BinOp):
   a,b=r(t.left),r(t.right)
   if isinstance(t.op,ast.Add):return a+b
   if isinstance(t.op,ast.Sub):return a-b
   if isinstance(t.op,ast.Mult):return a*b
   if isinstance(t.op,ast.Pow) and b.is_Integer and b>=0:return a**b
  raise ValueError('non-polynomial formula')
 return r(ast.parse(expr,mode='eval').body)
def same(a,b,label):need(S.expand(a-b)==0,label)

def audit_graph(g,old=False):
 nodes=g['nodes'];reg=g['named_registers'];known={};seen=set()
 need(g['variables']==VARS and g['variable_count']==15,'declared variables')
 need(g['domain']=='unrestricted integers','domain')
 need(g['fixed_numerals']==PORTS,'fixed coefficient declaration')
 need(g['schema']=='integer-polynomial-dag-v1','schema')
 for i,node in enumerate(nodes):
  need(type(node) is list and node,'node format')
  op=node[0]
  if op in OPS:need(len(node)==3 and all(type(x) is int and 0<=x<i for x in node[1:]),'causal binary DAG')
  else:
   need(len(node)==2,'leaf arity')
   if op=='variable':need(node[1] in VARS,'variable leaf')
   elif op=='coefficient':need(node[1] in PORTS,'coefficient leaf')
   elif op=='integer':need(type(node[1]) is int,'integer literal')
   else:raise ValueError('unexpected node kind')
 need(set(reg)=={n for n,_ in DEFS},'complete register list')
 def traverse(i):
  if i in seen:return
  seen.add(i)
  if nodes[i][0] in OPS:
   traverse(nodes[i][1]);traverse(nodes[i][2])
 need(type(g['output']) is int and 0<=g['output']<len(nodes),'output bound')
 traverse(g['output'])
 need(len(seen)==len(nodes),'dead node')
 need({nodes[i][1] for i in seen if nodes[i][0]=='variable'}==set(VARS),'input liveness')
 need({nodes[i][1] for i in seen if nodes[i][0]=='coefficient'}==set(PORTS),'coefficient liveness')
 counts=collections.Counter(nodes[i][0] for i in seen if nodes[i][0] in OPS)
 need(dict(counts)==g['operation_counts'] and sum(counts.values())==g['operations'],'reported counts')
 for name,formula in DEFS:
  ix=reg[name];need(type(ix) is int and ix in seen,'register index')
  memo={}
  def expand(i):
   if i in known:return known[i]
   if i in memo:return memo[i]
   node=nodes[i];op=node[0]
   if op=='integer':ans=S.Integer(node[1])
   elif op in ('variable','coefficient'):ans=SYM[node[1]]
   else:
    a,b=expand(node[1]),expand(node[2])
    ans=a+b if op=='add' else a-b if op=='sub' else a*b
   memo[i]=ans;return ans
  if old and name=='carrier':formula='Z*Z+2*U*L*Z-U*U*k*L-U*U'
  same(expand(ix),parse(formula,SYM),'independent register '+name)
  known[ix]=SYM[name]
 need(g['output']==reg['P'],'output is P')
 return dict(counts)

def leading_audit(g):
 # Independent symbolic homogeneous leading propagation, with cancellation rejected.
 # All leaf coefficients have degree zero, all fifteen integer variables degree one.
 top=[];degrees=[]
 for i,node in enumerate(g['nodes']):
  op=node[0]
  if op=='integer':d=0;t=S.Integer(node[1])
  elif op=='coefficient':d=0;t=SYM[node[1]]
  elif op=='variable':d=1;t=SYM[node[1]]
  else:
   l,r=node[1:];dl,dr=degrees[l],degrees[r];a,b=top[l],top[r]
   if op=='mul':d=dl+dr;t=a*b
   elif dl>dr:d=dl;t=a
   elif dr>dl:d=dr;t=b if op=='add' else -b
   else:d=dl;t=S.expand(a+b if op=='add' else a-b)
  need(t!=0,'leading cancellation requires exact lower terms at '+str(i))
  top.append(t);degrees.append(d)
 rows={n:degrees[g['named_registers'][n]] for n in ['carrier','strong','auxiliary','guard']}
 need(rows=={'carrier':24,'strong':14,'auxiliary':18,'guard':16},'row degree certificates')
 need(degrees[g['output']]==48 and g['exact_degree']==48,'exact degree claim')
 q0=6*SYM['beta']*SYM['j'];X0=12*q0*SYM['w'];Y0=q0*SYM['v']
 U0=8*q0*q0*X0*Y0
 k0=top[g['named_registers']['k']];L0=X0*Y0*Y0*k0
 same(top[g['named_registers']['carrier']],4*U0*U0*L0*SYM['n'],'carrier leading form')
 same(top[g['output']],16*U0**4*L0**2*SYM['n']**2,'polynomial leading form')
 target={n:0 for n in VARS};target.update(j=26,w=8,v=10,h=2,n=2)
 poly=S.Poly(top[g['output']],*[SYM[n] for n in VARS])
 coeff=poly.coeff_monomial(tuple(target[n] for n in VARS))
 same(coeff,2**58*3**34*SYM['beta']**26,'exact selected coefficient')
 return rows,target

new=json.loads((NEW/'equation.json').read_text());old=json.loads((OLD/'equation.json').read_text())
counts=audit_graph(new);oldcounts=audit_graph(old,True)
need(counts=={'mul':61,'add':25,'sub':22},'108 binary gates')
need(oldcounts=={'mul':63,'add':24,'sub':23},'110 old binary gates')
rows,monomial=leading_audit(new)
spec=json.loads((NEW/'specification.json').read_text())
need(spec['variables']==VARS and spec['fixed_numerals']==PORTS,'spec declaration')
need(spec['domain']=='unrestricted integers' and spec['single_polynomial']=='P','spec domain/output')
need(spec['exact_degree']==48 and spec['row_degrees']==[24,14,18,16],'spec degrees')
need([n for n,_ in spec['polynomial_abbreviations']]==[n for n,_ in DEFS],'spec register order')
for (name,expression),(_,expected) in zip(spec['polynomial_abbreviations'],DEFS):
 same(parse(expression,SYM),parse(expected,SYM),'independent specification '+name)
# Exact universal identity and mutually inverse signed witness maps.
U,Z,L,k,ell,t,x,no,nn,g,v0=S.symbols('U Z L k ell t x no nn g v0')
Cnew=(Z+U*k)**2+4*U*(L*Z-U)
Cold=Z**2+2*U*L*Z-U**2*k*L-U**2
same(Cnew.subs(Z,2*Z-U*k),4*Cold,'direct affine carrier identity')
same(Cnew,U**2*((Z/U+2*L+k)**2-4*(1+L*(L+k))),'centered square identity')
same(Cnew.subs(Z,U*t)/U**2,t*t+2*(2*L+k)*t+k*k-4,'monic scalar row')
same((1+L*(L+k)).subs(L,ell*k),1+ell*(ell+1)*k*k,'Dtau positivity identity')
newn=2*no+g+v0-k;oldn=(nn-g-v0+k)/2
same(oldn.subs(nn,newn),no,'old to new to old coordinate')
same(newn.subs(no,oldn),nn,'new to old to new coordinate')
same(U*(newn+g+v0),2*U*(no+g+v0)-U*k,'Z under all-zero forward map')
# Constants: raw bytes, independent hashes, canonical encoding, actual congruences.
TRUSTED={
 'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
 'K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
 'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
 'MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
 'cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
 'cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}
binding=json.loads((NEW/'coefficients/BINDING.json').read_text())
need((NEW/'coefficients/BINDING.json').read_bytes()==(OLD/'coefficients/BINDING.json').read_bytes(),'identical coefficient binding')
values={}
for name in PORTS:
 info=binding['payloads'][name];raw=gzip.decompress((NEW/'coefficients'/info['file']).read_bytes())
 need(raw==gzip.decompress((OLD/'coefficients'/info['file']).read_bytes()),'prior payload bytes '+name)
 need(hashlib.sha256(raw).hexdigest()==TRUSTED[name]==info['raw_sha256'],'trusted payload '+name)
 val=int.from_bytes(raw,'little');values[name]=val
 need(val.bit_length()==info['bits'] and len(raw)==info['raw_bytes'],'payload size '+name)
 need(val>0 and raw[-1]!=0,'minimal positive encoding '+name)
need(values['beta']==2**1064921-1,'fixed beta recipe')
need(values['beta']%6==1,'unconditional beta parity/congruence')
need(values['cone_A']==2**1113 and values['cone_B']==2**666104,'fixed cones')
need(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'mask bounds')
# Authenticate inherited mathematical source files and retained old equation.
manifest=json.loads((OLD/'MANIFEST.json').read_text())['files']
prior_files=['equation.json','specification.json','PROOF.md','DEPENDENCIES.md','SOURCE_PINS.json']
for name in prior_files:need(digest(OLD/name)==manifest[name]['sha256'],'prior manifest '+name)
pins=json.loads((OLD/'SOURCE_PINS.json').read_text())
for record in pins['sources']:
 path=OLD/record['path'];need(digest(path)==record['sha256'] and path.stat().st_size==record['bytes'],'inherited source pin '+record['path'])
# Authenticate the new endpoint's declared direct dependency against retained files.
newpins=json.loads((NEW/'SOURCE_PINS.json').read_text())
need((NEW/newpins['source_root']).resolve()==OLD.resolve(),'new source root')
for name,sha in newpins['source_files_sha256'].items():
 need(digest(OLD/name)==sha,'new direct source pin '+name)
# Every single live arithmetic opcode mutation must be rejected by exact cuts.
mutations=[]
for i,node in enumerate(new['nodes']):
 if node[0] not in OPS:continue
 altered=copy.deepcopy(new);altered['nodes'][i][0]='sub' if node[0]=='add' else 'add'
 # Refresh count claims so rejection cannot be merely stale counter metadata.
 c=collections.Counter(n[0] for n in altered['nodes'] if n[0] in OPS)
 altered['operation_counts']=dict(c)
 try:audit_graph(altered)
 except ValueError:mutations.append(i)
 else:raise ValueError('live mutation escaped exact audit '+str(i))
need(len(mutations)==108,'all live mutation controls')
# Supplementary finite CRT diagnostics include negative q, negative/zero v and k.
# These are diagnostics only; the general argument is stated in the review.
crt_cases=0
for b in [7,31,127,511]:
 for j in range(-6,7):
  q=b*(6*j+1)+1
  for w in range(-3,4):
   X=q*(12*w+4)
   for v in range(-7,8):
    H=4*(X+1)*q*v+3;M=2*q*q
    need(q!=0 and H!=0 and math.gcd(H,M)==1,'finite CRT case')
    if v==0:need((v-q*q)%M!=0,'zero-v congruence excluded')
    crt_cases+=1
result={'status':'pass','equation_sha256':digest(NEW/'equation.json'),
 'specification_sha256':digest(NEW/'specification.json'),
 'reviewed_proof_sha256':digest(NEW/'PROOF.md'),
 'reviewed_tex_section_sha256':digest(NEW/'section.tex'),
 'direct_dependency_pins_checked':len(newpins['source_files_sha256']),
 'variables':15,'operations':sum(counts.values()),'operation_counts':counts,
 'row_degrees':rows,'exact_total_degree':48,'degree_witness_monomial':monomial,
 'degree_witness_coefficient':'2^58 * 3^34 * beta^26 > 0',
 'independent_register_checks':len(DEFS),'universal_map_identities':'exact symbolic identities passed',
 'every_zero_maps':'inverse signed-coordinate maps; integrality and degenerate cases reviewed in INDEPENDENT_REVIEW.md',
 'coefficient_raw_sha256':TRUSTED,'inherited_source_pins_checked':len(pins['sources']),
 'prior_equation_sha256':digest(OLD/'equation.json'),'prior_proof_sha256':digest(OLD/'PROOF.md'),
 'all_live_opcode_mutations_rejected':len(mutations),'supplementary_CRT_cases':crt_cases,
 'scope':'Independent literal arithmetic, source bytes, attained degree, and local ordinary all-zero equivalence. No new compiler theorem, formal-system certificate, or consistency proof.'}
(HERE/'INDEPENDENT_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
