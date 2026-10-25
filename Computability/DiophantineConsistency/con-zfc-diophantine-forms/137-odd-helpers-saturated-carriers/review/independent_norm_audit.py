#!/usr/bin/env python3
"""Fresh reviewer implementation: no builder/checker imports, no producer writes.
Uses exact SymPy integer polynomials at independently chosen register cuts,
full gate coverage and real corruptions, plus graded-lex leading arithmetic.
"""
import ast, copy, gzip, hashlib, json, math, sys
from collections import Counter
from pathlib import Path
import sympy as S
ROOT=Path(__file__).resolve().parents[1]
PORTS=['beta','K0','MC','MF','cone_A','cone_B']
OUT=ROOT/'review'
def need(q,m):
 if not q: raise ValueError(m)
def integer_forms(g):
 free=g['free_y']; center=g['center']=='simple'
 f=[('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('q2','q**2'),('W','4+12*w'),('X','W*q'),('Y','v' if free else 'v*q'),('E','Y*X'),('a','Y+E'),('H','3+4*a'),('Delta','(a+2)**2-1'),('A','2+a'),('F','C*K0+C*W-z*qm'),('R','(q*q-q*F-C)*(q2-1)+J*MC+J*q*MF'),('k','h*E+R+1'),('c2','c**2'),('Yk','k*Y'),('eta','c-Yk'),('Derr','cone_A**2*F**2+cone_B**2*C**2-2*q*(cone_A*F+cone_B*C)+2*q**2')]
 if free: f += [('q3','q**3'),('Yeta','Y*eta'),('kq3','k*q3'),('Budget','Y**2*k**2*(q**2-Derr)-4*q**2*Y**2*eta**2-k**2*q**8')]
 else: f += [('Budget','k**2*(q**2-Derr)-4*q**2*eta**2')]
 f += [('L','Y*Y*X*k'),('Dt','L**2+L*k+1'),('D4','4*(3*Budget-4)'),('Pg','s*Dt'),('P','Dt+4*(3*Budget-4)*Dt**2*s**2'),('Dm','Delta*c**2+1'),('BP','P*Dm'),('Ub','c**2*r'),('U','Ub*A'),('UBP','BP*U'),('strong','BP*Delta*U**2'),('Df','1+strong'),('Q','strong*Delta'),('delta','Q-1'),('b','4*UBP*T+c-R'),('V','b*Df-c'),('Cy','V**2*Q-1'),('K','3*X*c-2*X**2+2'),('qscale','q**3' if free else 'q**2'),('M','qscale*2'),('Dcar','H*M'),('M2','M**2'),('M4','M**4'),('Dcar2','Dcar**2'),('Dcar3','Dcar**3'),('S','H*M**5*r*s'),('S2','S**2'),('zc','T*Dcar+K*M+H*v-H*qscale'),('zc2','zc**2'),('Ac','zc**5+3*Dcar**2*zc**3-19*Dcar**3*zc**2-57*Dcar**5')]
 if center:f += [('lam','BP*A*U'),('shift','V*lam'),('Z','S*n+S*lam*V-Ac')]
 else:f += [('Z','n*S-Ac')]
 f += [('output','delta*Z**2-S2*BP*Df*Cy')]
 return f

def low_forms(g):
 return [('J','1+6*j'),('qm','J*beta'),('q','1+qm'),('W','4+12*w'),('X','W*q'),('Y','v'),('F','C*K0+C*W-z*qm'),('R','(q*q-q*F-C)*(q*q-1)+J*MC+J*q*MF'),('E','Y*X'),('a','Y+E'),('H','3+4*a'),('Delta','(a+2)**2-1'),('k','h*E+R+1'),('eta','c-Y*k'),('L','X*Y**2*k'),('I','(1+2*r)*c**2'),('Q','Delta*(f*f-1)'),('V','f*f*c*T-f*f*R-c'),('q3','q**3'),('M','2*q3'),('U','H*M'),('Klo','2*X**2-3*c*X-2'),('Z','U*n+M*Klo+H*Y-H*q3'),('Derr','cone_A**2*F**2+cone_B**2*C**2-2*q*(cone_A*F+cone_B*C)+2*q**2'),('budget','Y**2*k**2*(q**2-Derr)-4*q**2*Y**2*eta**2-k**2*q**8'),('pos2','1+p2*p2+p3*p3+p3'),('G','budget-pos2'),('carrier','Z**2+2*(2*L+k)*U*Z+U**2*(k**2-4)'),('strong','f**2-Delta*I**2-1'),('auxiliary','Q*V**2-(Q-1)*(V+y)**2-1'),('UG','U**2*G'),('N','(carrier-UG)**2-16*U**2*UG*(1+L*(L+k))'),('P','(N+1)*(strong+1)*(auxiliary+1)-1')]

def thirteen_forms(g):
 f=low_forms(g)
 f=[(n,e) for n,e in f if n not in ['Q','V','pos2','G','strong','UG','N','P']]
 i=next(i for i,(n,e) in enumerate(f) if n=='I')+1
 f[i:i]=[('Ds','Delta*I**2'),('Fs','1+Ds'),('Q','Delta*Ds'),('V','Fs*c*T-Fs*R-c')]
 f += [('G','4*budget-4*p1**2-4*p2**2-3'),('Dt','L**2+k*L+1'),('U2','U**2'),('ga','G*U2'),('db','4*Dt*U2'),('fc','16*Fs*U2'),('gc','fc+ga'),('inner','carrier**2-2*carrier*gc+gc**2-4*ga*fc-4*db*gc'),('N','inner**2-64*ga*db*fc*carrier-64*ga*db**2*fc'),('P','N+auxiliary+N*auxiliary')]
 return f

def validate(g,forms):
 ns=g['nodes']; nm=dict(g['named_registers']);nm['output']=g['output']; cuts={};seen=set();ledger=[]
 syms={n:S.Symbol(n) for n in set(g['variables']+PORTS+[n for n,_ in forms])}
 for i,r in enumerate(ns):
  need(r[0] in ['variable','coefficient','integer','add','sub','mul'],'operation')
  if r[0] in ('add','sub','mul'):need(len(r)==3 and all(type(t)==int and 0<=t<i for t in r[1:]),'topology')
  if r[0] in ('variable','coefficient'):cuts[i]=syms[r[1]]
 def rec(i,memo):
  if i in cuts:return cuts[i]
  seen.add(i)
  if i in memo:return memo[i]
  r=ns[i]
  if r[0]=='integer':v=S.Integer(r[1])
  elif r[0] in ('variable','coefficient'):v=syms[r[1]]
  else:
   a,b=rec(r[1],memo),rec(r[2],memo);v=a+b if r[0]=='add' else a-b if r[0]=='sub' else a*b
  memo[i]=v;return v
 for n,e in forms:
  if n not in nm:continue
  refs={x.id for x in ast.walk(ast.parse(e,mode='eval')) if isinstance(x,ast.Name)}
  ports={r[1]:i for i,r in enumerate(ns) if r[0] in ('variable','coefficient')}
  lookup=dict(ports);lookup.update(nm)
  cuts={lookup[x]:syms[x] for x in refs}
  actual=rec(nm[n],{});expected=S.sympify(e,locals=syms)
  need(S.expand(actual-expected)==0,'register '+n)
  cuts[nm[n]]=syms[n];ledger.append(n)
 ops={i for i,r in enumerate(ns) if r[0] in ('add','sub','mul')}
 need(ops<=seen,'unbound arithmetic gates: '+str(ops-seen))
 live=set(); todo=[g['output']]
 while todo:
  i=todo.pop()
  if i in live:continue
  live.add(i)
  if ns[i][0] in ('add','sub','mul'):todo.extend(ns[i][1:])
 need(len(live)==len(ns),'dead node')
 need([r[1] for r in ns if r[0]=='variable']==g['variables'],'variable ports')
 need([r[1] for r in ns if r[0]=='coefficient']==PORTS,'coefficient ports')
 counts=Counter(ns[i][0] for i in ops)
 need(dict(counts)==g['operation_counts'] and len(ops)==g['operations'],'count')
 return {'all_arithmetic_gates_bound':len(ops),'named_cuts':ledger,'counts':dict(counts)}

def leading(g):
 # Independent monomial order from producer: graded lex, j first.
 order=sorted(g['variables'],key=lambda n: (['j','w','v','s','r','c','z','T','h','C','n','f','y','p1','p2','p3'].index(n)))
 zero=(0,)*len(order); vals=[]; syms={n:S.Symbol(n) for n in PORTS};nm=g['named_registers'];cuts=[]
 def key(t):return (sum(t[0]),t[0])
 def mul(a,b):return (tuple(x+y for x,y in zip(a[0],b[0])),a[1]*b[1])
 def prod(names):
  out=(zero,S.Integer(1))
  for n in names:out=mul(out,vals[nm[n]])
  return out
 for i,r in enumerate(g['nodes']):
  if i==g['output'] and g.get('center')=='simple':
   v=prod(['S2','Q','U','U','BP','BP','V','V'])
   dg=lambda n:sum(vals[nm[n]][0])
   weights={'S':dg('S'),'d':dg('delta'),'lam':dg('lam'),'V':dg('V'),'W':max(dg('S')+1,dg('Ac')),'B':dg('BP'),'F':dg('Df'),'U':dg('U')}
   names=list(weights);ss,dd,ll,vv,ww,bb,ff,uu=S.symbols(' '.join(names))
   cut=dd*ww**2+2*dd*ss*ll*vv*ww+ss**2*((dd*(uu**2*bb**2-bb)-bb*ff)*vv**2+bb*ff)
   poly=S.Poly(S.expand(cut),ss,dd,ll,vv,ww,bb,ff,uu)
   terms=[(sum(e*weights[n] for e,n in zip(ex,names)),ex,coef) for ex,coef in poly.terms()]
   mx=max(d for d,ex,coef in terms);leaders=[(ex,coef) for d,ex,coef in terms if d==mx]
   need(mx==sum(v[0]) and leaders==[((2,1,0,2,0,2,0,2),1)],'unique weighted center leader')
   cuts.append('center output exact universal expansion and unique weighted maximum')
  elif r[0]=='integer':v=(zero,S.Integer(r[1]))
  elif r[0]=='coefficient':v=(zero,syms[r[1]])
  elif r[0]=='variable':
   ex=list(zero);ex[order.index(r[1])]=1;v=(tuple(ex),S.Integer(1))
  else:
   a,b=vals[r[1]],vals[r[2]]
   if r[0]=='mul':v=mul(a,b)
   elif key(a)>key(b):v=a
   elif key(b)>key(a):v=(b[0],b[1] if r[0]=='add' else -b[1])
   else:v=(a[0],S.expand(a[1]+b[1] if r[0]=='add' else a[1]-b[1]))
  need(v[1]!=0,'unresolved leading cancellation '+str(i));vals.append(v)
 ex,coeff=vals[g['output']];need(sum(ex)==g['exact_degree'],'exact degree')
 coeff=S.factor(coeff)
 powers=coeff.as_powers_dict(); num=int(coeff.subs(syms['beta'],1)); sign=1 if num>0 else -1; num=abs(num); fs={}
 for prime in [2,3]:
  e=0
  while num%prime==0:num//=prime;e+=1
  fs[str(prime)]=e
 need(num==1,'leading coefficient has no unexpected factor')
 coeff=f"{sign} * 2^{fs['2']} * 3^{fs['3']} * beta^{powers.get(syms['beta'],0)}"
 return {'order':order,'monomial':{n:e for n,e in zip(order,ex) if e},'coefficient':str(coeff),'degree':sum(ex),'all_gate_leaders_nonzero':len(vals),'cuts':cuts}

def universal():
 A,u,B,V,Sv,W,c,t,P=S.symbols('A u B V S W c t P');D=A*A-1;U=A*u;Df=1+D*U*U*B;Q=D*D*U*U*B;d=Q-1;lam=A*U*B
 out=d*(W+Sv*lam*V)**2-Sv**2*B*Df*(Q*V*V-1)
 cut=d*W*W+2*d*Sv*lam*V*W+Sv*Sv*((d*(U*U*B*B-B)-B*Df)*V*V+B*Df)
 need(S.expand(out-cut)==0,'center cancellation')
 Dm=1+D*c*c;BP=Dm*P;F=1+D*U*U*BP;Q=D*D*U*U*BP;VV=F*t-c;Cy=Q*VV*VV-1;Da=(Q-1)*Cy
 # Quotient-ring reductions, not sampled coprimality.
 LL=Q*t*(VV-c)+D*c*c
 need(S.expand(Da-A*A*Dm-F*(D*F*LL-D*Dm-A*A*LL))==0,'Da modulo Df')
 need(S.expand(Da-1-Q*((Q-1)*VV*VV-1))==0,'Da modulo BP')
 U,Z,L,k,G,p,rho,aa,gg=S.symbols('U Z L k G p rho aa gg')
 car=Z*Z+2*(2*L+k)*U*Z+U*U*(k*k-4);a=4*(1+L*(L+k))
 norm=(car-U*U*G)**2-4*U**4*G*a
 need(S.expand(norm-((Z+U*(2*L+k))**2-U**2*(a+G))**2+4*U**4*a*G)==0,'two-root norm')
 lift=norm.subs({Z:Z+U*p,G:p*p},simultaneous=True)
 need(S.expand(lift-car*(car+4*U*p*(Z+U*(2*L+k))+4*U*U*p*p))==0,'universal reverse lift')
 rel=(rho*rho-aa-gg)**2-4*aa*gg
 need(S.expand((rho*rho-aa+gg)**2-4*rho*rho*gg-rel)==0,'rational G extraction')
 need(S.expand((rho*rho+aa-gg)**2-4*rho*rho*aa-rel)==0,'rational A extraction')
 # Adjacent Pell descent exact preservation. Sign inequalities are in review.
 q,x,y=S.symbols('q x y');xp=(2*q-1)*x-2*(q-1)*y;yp=(2*q-1)*y-2*q*x
 need(S.expand(q*xp*xp-(q-1)*yp*yp-(q*x*x-(q-1)*y*y))==0,'denominator descent norm identity')
 # Integer residual exclusions, exhaustively all mod4 classes.
 for a in range(4):
  for f in range(4):
   for i in range(4):need((f*f-(a*a-1)*i*i-1)%4!=2,'strong -2 exclusion')
 for x in range(4):need(x*x%4!=2,'norm -2 exclusion')
 # Triple-root norm independently multiplied in a genuine polynomial ring.
 x,aa,bb,cc,rr,ss,tt=S.symbols('x aa bb cc rr ss tt');prod=S.Integer(1)
 import itertools
 for signs in itertools.product([-1,1],repeat=3):prod*=x-signs[0]*rr-signs[1]*ss-signs[2]*tt
 norm=((x*x-aa-bb-cc)**2-4*(aa*bb+aa*cc+bb*cc))**2-64*aa*bb*cc*x*x
 need(S.expand(prod-norm.subs({aa:rr**2,bb:ss**2,cc:tt**2}))==0,'triple signed product')
 car=S.Symbol('car');optimized=((car-aa-cc)**2-4*(aa*cc+bb*(aa+cc)))**2-64*aa*bb*cc*(car+bb)
 need(S.expand(norm.subs(x*x,car+bb)-optimized)==0,'triple optimized schedule')
 need(S.expand(norm.subs({x:rr+2*ss+4*tt,aa:rr**2,bb:4*ss**2,cc:16*tt**2}))==0,'triple complete signed lift')
 return {'triple_norm_and_signed_lift':True,'center_cancellation':True,'coprimality_remainders':True,'two_root_norm_and_complete_lift':True,'rational_extraction':True,'adjacent_Pell_norm_descent':True,'strong_mod4_classes':64}

def sources(folder):
 ps=json.loads((folder/'SOURCE_PINS.json').read_text());n=0
 if isinstance(ps,dict):it=((p,d['sha256'],d.get('bytes')) for p,d in ps['dependencies'].items())
 else:it=((d['copy'],d['sha256'],None) for d in ps)
 for p,h,size in it:
  raw=(folder/p).read_bytes();need(hashlib.sha256(raw).hexdigest()==h,'source '+p);need(size is None or len(raw)==size,'source size');n+=1
 coeffdir=(folder/'coefficients') if (folder/'coefficients').is_dir() else folder.parent/'coefficients'
 binding=json.loads((coeffdir/'BINDING.json').read_text()); vals={};payload={}
 for name in PORTS:
  b=binding['payloads'][name];raw=gzip.decompress((coeffdir/b['file']).read_bytes());need(hashlib.sha256(raw).hexdigest()==b['raw_sha256'],'coefficient hash');vals[name]=int.from_bytes(raw,'little');need(vals[name].bit_length()==b['bits'],'coefficient bits');payload[name]=hashlib.sha256(raw).hexdigest()
 need(vals['beta']==2**1064921-1 and vals['cone_A']==2**1113 and vals['cone_B']==2**666104,'literal coefficients')
 need(0<vals['MC']<vals['beta']<vals['MF']<2*vals['beta'],'already shifted MF')
 return {'source_pins':n,'payloads':payload}

def main():
 mode=sys.argv[1];folder=ROOT/('lowdegree/thirteen' if mode=='thirteen' else mode);result={'status':'PASS','mode':mode,'optimized':not __debug__,'universal':universal(),'source_binding':sources(folder),'equations':[]}
 paths=sorted(folder.glob('*_product11_*.json')) if mode=='integer' else [folder/'equation.json']
 for path in paths:
  g=json.loads(path.read_text());f=integer_forms(g) if mode=='integer' else thirteen_forms(g) if mode=='thirteen' else low_forms(g)
  row={'file':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'identity_check':validate(g,f),'leading':leading(g)}
  mutations=[]
  for i,r in enumerate(g['nodes']):
   if r[0] not in ('add','sub','mul'):continue
   damaged=copy.deepcopy(g);damaged['nodes'][i][0]={'add':'sub','sub':'add','mul':'add'}[r[0]]
   try:validate(damaged,f)
   except (ValueError,KeyError):mutations.append(i)
   else:raise ValueError('accepted real gate mutation '+str(i))
  row['rejected_live_gate_mutations']=mutations;result['equations'].append(row)
 name='INDEPENDENT_OPTIMIZED.json' if not __debug__ else 'INDEPENDENT_NORMAL.json'
 (OUT/('lowdegree/thirteen' if mode=='thirteen' else mode)/name).write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'status':'PASS','mode':mode,'optimized':not __debug__,'equations':[{k:r[k] for k in ['file','leading']} for r in result['equations']]},indent=2))
if __name__=='__main__':main()
