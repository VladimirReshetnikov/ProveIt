#!/usr/bin/env python3
"""Independent local identities, complete DAG checks, degree and mutation audit.
Reads original audit formulas as inert AST literals; imports no builder.
"""
import ast,copy,gzip,hashlib,json,sys
from pathlib import Path
from collections import Counter
import sympy as S
ROOT=Path(__file__).resolve().parent
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
def need(x,msg):
 if not x:raise ValueError(msg)
def literal(path,name):
 for n in ast.parse(path.read_text()).body:
  if isinstance(n,ast.Assign) and len(n.targets)==1 and isinstance(n.targets[0],ast.Name) and n.targets[0].id==name:return ast.literal_eval(n.value)
 raise ValueError(name)
f14=literal(ROOT/'baseline/review/audit.py','FORMS');f13=literal(ROOT/'baseline/thirteen/review/audit.py','FORMS')
v14=literal(ROOT/'baseline/review/audit.py','V');v13=literal(ROOT/'baseline/thirteen/review/audit.py','V')
FORMS={};VARIABLES={};COUNTS={};DEGREES={};WITNESSES={}
for tag,old,vs,degree,count,mon,coef in [
 ('integer14_degree88_ops115',f14,v14,88,{'mul':67,'add':25,'sub':23},dict(j=56,w=8,v=8,z=5,r=2,c=4,f=4,y=1),'-2**87*3**64*beta**56'),
 ('integer13_degree156_ops125',f13,v13,156,{'mul':75,'add':26,'sub':24},dict(j=106,w=14,v=14,z=9,r=4,c=8,y=1),'2**171*3**120*beta**106')]:
 fs=[]
 for n,f in old:
  if n in ('strong','auxiliary'):f='('+f+')+1'
  if n=='P': f='(N+1)*auxiliary-1' if degree==156 else '(N+1)*strong*auxiliary-1'
  fs.append((n,f))
 FORMS[tag]=fs;VARIABLES[tag]=vs;COUNTS[tag]=count;DEGREES[tag]=degree;WITNESSES[tag]=(mon,coef)
tag='integer14_degree94_ops110';fs=[]
for n,f in f13:
 if n=='G':fs.extend([('Bg','budget-p1*p1-p2*p2'),('G','4*Bg-3')]);continue
 if n=='auxiliary':f='V*V-2*Q*y*V-Q*y*y+2*y*V+y*y'
 if n in ['Dt','U2','ga','db','fc','gc','inner','N','P']:continue
 fs.append((n,f))
fs.extend([('inner','s*s+s-Bg-Ds'),('N','inner*inner-4*Bg*Fs+3*Fs'),('P','carrier*N*auxiliary+carrier*auxiliary+N*auxiliary+auxiliary-1')])
FORMS[tag]=fs;VARIABLES[tag]=v13+['s'];COUNTS[tag]={'mul':63,'add':23,'sub':24};DEGREES[tag]=94
WITNESSES[tag]=(dict(j=55,w=9,v=10,z=6,r=4,c=8,y=1,n=1),'2**86*3**64*beta**55')
tag='integer14_degree86_ops112';fs=[]
for n,f in f14:
 if n in ['pos2','G','auxiliary','UG','N','P']:continue
 if n=='strong':f='f*f-Delta*I*I'
 fs.append((n,f))
fs.extend([('Bg','budget-p1*p1-p2*p2'),('G','4*Bg-3'),('delta','Q-1'),('Cy','Q*V*V-1'),('inner','delta*s*s+delta*s-delta*Bg+delta-Cy'),('N','inner*inner-G*delta*Cy'),('P','carrier*strong*N+carrier*strong+strong*N+strong-1')])
FORMS[tag]=fs;VARIABLES[tag]=[x for x in v14 if x not in ['y','p3']]+['p1','s'];COUNTS[tag]={'mul':64,'add':22,'sub':26};DEGREES[tag]=86
WITNESSES[tag]=(dict(j=51,w=9,v=10,z=5,f=4,r=2,c=4,n=1),'-2**79*3**60*beta**51')

def validate(tag,g):
 vs=VARIABLES[tag];forms=FORMS[tag];sy={x:S.Symbol(x) for x in set(vs+PORTS+[n for n,_ in forms])}
 nodes=g['nodes'];cuts={};seen=set();covered=set()
 need(g['variables']==vs,'variable declaration');need(g['fixed_numerals']==PORTS,'coefficient declaration')
 for i,n in enumerate(nodes):
  need(n[0] in ['integer','variable','coefficient','add','sub','mul'],'operation tag')
  if n[0] in ('add','sub','mul'):need(len(n)==3 and all(type(t)==int and 0<=t<i for t in n[1:]),'causal order')
 def rec(i,memo):
  if i in cuts:return cuts[i]
  if i in memo:return memo[i]
  n=nodes[i];op=n[0];covered.add(i)
  if op=='integer':r=S.Integer(n[1])
  elif op in ('variable','coefficient'):r=sy[n[1]]
  else:
   a,b=rec(n[1],memo),rec(n[2],memo);r=a+b if op=='add' else a-b if op=='sub' else a*b
  memo[i]=r;return r
 for name,f in forms:
  ix=g['named_registers'][name];actual=rec(ix,{});expected=S.sympify(f,locals=sy);diff=actual-expected
  if tag=='integer14_degree88_ops115' and name=='N':
   cc=sy['Z']**2+2*(2*sy['L']+sy['k'])*sy['U']*sy['Z']+sy['U']**2*(sy['k']**2-4)
   diff=diff.subs(sy['carrier'],cc).subs(sy['UG'],sy['U']**2*sy['G'])
  if tag=='integer14_degree94_ops110' and name=='N':diff=diff.subs(sy['G'],4*sy['Bg']-3)
  need(S.expand(diff)==0,'incorrect cut '+tag+' '+name+' '+str(S.expand(diff)))
  cuts[ix]=sy[name]
 def walk(i):
  if i in seen:return
  seen.add(i)
  if nodes[i][0] in ('add','sub','mul'):
   walk(nodes[i][1]);walk(nodes[i][2])
 need(g['output']==g['named_registers']['P'],'output binding');walk(g['output'])
 need(len(seen)==len(nodes),'liveness');need(covered==seen,'all-node cut coverage')
 need({nodes[i][1] for i in seen if nodes[i][0]=='variable'}==set(vs),'all variables')
 need({nodes[i][1] for i in seen if nodes[i][0]=='coefficient'}==set(PORTS),'all coefficients')
 counts=Counter(n[0] for n in nodes if n[0] in ('add','sub','mul'))
 need(counts==COUNTS[tag],'counts');need(g['operations']==sum(counts.values()),'declared count')
 return sy

def degree_check(tag,g,sy):
 tops=[];degs=[]
 for n in g['nodes']:
  op=n[0]
  if op=='integer':d=0;t=S.Integer(n[1])
  elif op=='coefficient':d=0;t=sy[n[1]]
  elif op=='variable':d=1;t=sy[n[1]]
  else:
   i,j=n[1:]
   if op=='mul':d=degs[i]+degs[j];t=tops[i]*tops[j]
   elif degs[i]>degs[j]:d=degs[i];t=tops[i]
   elif degs[j]>degs[i]:d=degs[j];t=tops[j] if op=='add' else -tops[j]
   else:d=degs[i];t=S.expand(tops[i]+tops[j] if op=='add' else tops[i]-tops[j])
  need(t!=0,'unresolved leading cancellation');degs.append(d);tops.append(t)
 need(degs[g['output']]==DEGREES[tag] and g['exact_degree']==DEGREES[tag],'exact degree')
 mon,cf=WITNESSES[tag];vs=VARIABLES[tag]
 lead=S.Poly(S.expand(tops[g['output']]),*[sy[x] for x in vs]);coefficient=lead.coeff_monomial(tuple(mon.get(x,0) for x in vs))
 need(S.expand(coefficient-S.sympify(cf,locals=sy))==0,'actual leading coefficient')
 # Check complete carrier top; inherited prose omitted the first summand.
 q0=6*sy['beta']*sy['j'];x0=12*q0*sy['w'];y0=sy['v'];r0=q0**4*sy['z']-12*q0**3*sy['w']*sy['C']
 u0=8*q0**3*x0*y0;l0=x0*y0*y0*r0;z0=u0*sy['n']+4*q0**3*x0*x0
 need(S.expand(tops[g['named_registers']['carrier']]-(u0*u0*r0*r0+4*u0*l0*z0))==0,'complete carrier top including known correction')
 return {'degree':DEGREES[tag],'monomial':mon,'coefficient':cf,'complete_top_terms':len(lead.terms())}

def identities():
 b,d,e,ss,g,u=S.symbols('b d e ss g u');G=4*b+1;x=2*ss+1;K=d*(ss*(ss+1)-b)-e;N=K*K-G*d*e
 need(S.expand(16*N-((d*(x*x+G)-4*e)**2-4*d*d*x*x*G))==0,'primitive identity')
 need(S.expand(K.subs({b:(g*g-1)/4,ss:(g+2*u-1)/2,e:d*u*u})-d*g*u)==0,'lift identity')
 vv,Q,yy=S.symbols('V Q y');need(S.expand((vv*vv-(Q-1)*yy*(2*vv+yy)-1)-(Q*vv*vv-(Q-1)*(vv+yy)**2-1))==0,'auxiliary restoration')
 B,C,A=S.symbols('B C A');need(S.expand((A+1)*(B+1)*(C+1)-1-((A+1)*(B+1)*(C+1)-1))==0,'unit substitution')
 # Exact old/new finalizer identities with changed named-unit semantics.
 n,r,t=S.symbols('n r t')
 need(S.expand((n+1)*(t+1)-1-((n+1)*S.Symbol('tu')-1).subs(S.Symbol('tu'),t+1))==0,'13 exact output')
 need(S.expand((n+1)*(r+1)*(t+1)-1-((n+1)*S.Symbol('ru')*S.Symbol('tu')-1).subs({S.Symbol('ru'):r+1,S.Symbol('tu'):t+1}))==0,'14 exact output')
 cases=0
 for a0 in range(8):
  for ii in range(8):
   D=a0*a0-1;Fs=1+D*ii*ii;need(Fs%4 in [0,1],'Fs residue')
   for ff in range(8):need((ff*ff-D*ii*ii-1)%4!=2,'strong exclusion')
   for kk in range(8):need((kk*kk-Fs)%4!=2,'norm exclusion');cases+=1
 unit=0
 for a in range(-6,7):
  for b in range(-6,7):
   for c in range(-6,7):
    if a!=-2 and b!=-2:need(((a+1)*(b+1)*(c+1)==1)==(a==b==c==0),'unit product');unit+=1
 # Signed lemma diagnostics include d negative, e zero, and Q=0 branch.
 lifts=0
 for dd in list(range(-5,0))+list(range(1,6)):
  for gg in range(-9,10,2):
   for uu in range(-5,6):
    bb=(gg*gg-1)//4;sss=(gg+2*uu-1)//2;ee=dd*uu*uu
    need((dd*(sss*(sss+1)-bb)-ee)**2-(4*bb+1)*dd*ee==0,'signed lift');lifts+=1
 return {'exact_identities':6,'residue_cases':cases,'unit_cases':unit,'signed_lifts':lifts}

def main():
 baseline_pin=json.loads((ROOT/'BASELINE_PINS.json').read_text())
 baseline_pin.update(json.loads((ROOT/'SOURCE_CLOSURE_PINS.json').read_text()))
 for name,h in baseline_pin.items():need(hashlib.sha256((ROOT/name).read_bytes()).hexdigest()==h,'baseline pin '+name)
 trusted=literal(ROOT/'baseline/thirteen/review/audit.py','TRUSTED_RAW_SHA256');binding=json.loads((ROOT/'baseline/coefficients/BINDING.json').read_text());bytes_=0
 for port in PORTS:
  r=binding['payloads'][port];raw=gzip.decompress((ROOT/'baseline/coefficients'/r['file']).read_bytes());bytes_+=len(raw)
  need(hashlib.sha256(raw).hexdigest()==trusted[port]==r['raw_sha256'],'raw coefficient '+port)
  n=int.from_bytes(raw,'little');need(n.bit_length()==r['bits'],'bit count')
  if port=='beta':need(n==2**1064921-1,'actual beta')
 rows=[]
 for tag in FORMS:
  p=json.loads((ROOT/(tag+'.json')).read_text());sy=validate(tag,p);degree=degree_check(tag,p,sy);rejected=[]
  for i,node in enumerate(p['nodes']):
   if node[0] not in ['add','sub','mul']:continue
   m=copy.deepcopy(p);m['nodes'][i][0]='sub' if node[0]=='add' else 'add'
   try:validate(tag,m)
   except ValueError:rejected.append(i)
   else:raise ValueError('accepted gate mutation '+tag+' '+str(i))
  rows.append({'name':tag,'variables':len(VARIABLES[tag]),'operations':sum(COUNTS[tag].values()),'counts':COUNTS[tag],**degree,'rejected_gate_mutations':len(rejected),'sha256':hashlib.sha256((ROOT/(tag+'.json')).read_bytes()).hexdigest()})
 result={'status':'PASS','python_optimized':not __debug__,'rows':rows,'coefficient_raw_bytes':bytes_,'source_pins':len(baseline_pin),'local_checks':identities(),'boundary':'Finite literal identities, full DAGs and metrics. Unbounded native/refutation theorem remains inherited ordinary dependency.'}
 path=ROOT/('CHECK_OPTIMIZED.json' if not __debug__ else 'CHECK.json');path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
if __name__=='__main__':main()
