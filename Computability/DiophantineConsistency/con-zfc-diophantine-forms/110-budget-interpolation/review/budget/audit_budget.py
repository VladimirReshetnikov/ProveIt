#!/usr/bin/env python3
"""Independent algebra/metric audit. Imports no author builder or auditor.
Finite diagnostics are labeled; they do not prove the universal reduction.
"""
import ast, gzip, hashlib, itertools, json, math, sys, time
from collections import Counter
from pathlib import Path
from sympy import ZZ
from sympy.polys.rings import ring
ROOT=Path(__file__).resolve().parents[2]
OUT=Path(__file__).resolve().parent
P=1000000007
audited_files=[ROOT/'guard/PROOF.md',ROOT/'guard/budget12_aux_centered.json',ROOT/'guard/budget12_tau_centered.json',ROOT/'finalizers/ABSORPTION_PROOF.md',ROOT/'finalizers/absorbed15_degree176.json',ROOT/'finalizers/absorbed15_degree176_dag.json']
initial_hashes={str(fp.relative_to(ROOT)):hashlib.sha256(fp.read_bytes()).hexdigest() for fp in audited_files}
receipt={'status':'running','python_optimized':not __debug__,'checks':{},'negative_controls':{}}
def req(c,m):
    if not c: raise ValueError(m)
def equal(a,b,m):req(a==b,m)
def expr(s,env):
    def ev(n):
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.Constant) and isinstance(n.value,int):return n.value
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -ev(n.operand)
        if isinstance(n,ast.BinOp):
            a,b=ev(n.left),ev(n.right)
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
            if isinstance(n.op,ast.Pow):return a**b
        raise ValueError(ast.dump(n))
    return ev(ast.parse(s,mode='eval').body)
def Rmake(names):
    rr=ring(','.join(names),ZZ);return rr[0],dict(zip(names,rr[1:]))
def mq_mul(p,q,rad,zero):
    n=1<<len(rad);o=[zero for _ in range(n)]
    for i in range(n):
        for j in range(n):
            t=p[i]*q[j]
            for k,r in enumerate(rad):
                if (i&j)&(1<<k):t*=r
            o[i^j]+=t
    return o
# Independent full 32-sign product, with formal root variables.
r,x,*rr=ring('x,r1,r2,r3,r4,r5',ZZ)
f=x-sum(rr,r.zero)
for i in range(5):
    flipped=r.from_dict({m:c*(-1 if m[i+1]%2 else 1) for m,c in f.items()})
    f*=flipped
req(all(all(k%2==0 for k in m[1:]) for m in f),'sign product not invariant')
R,e=Rmake(['x','a','b','c','d','cn','delta']);x,a,b,c,d,cn,D=(e[n] for n in e)
expected=R.from_dict({(m[0],m[1]//2,m[2]//2,m[3]//2,m[4]//2,m[5]//2,16-m[5]//2):v for m,v in f.items()})
req(all(m[-1]>=0 for m in expected),'denominator not cleared')
receipt['checks']['generic_five_root_norm']={'method':'literal 32-sign product in formal root variables, followed by exact even-exponent reduction','monomials':len(expected)}
# Generic roots may be reordered. Verify each literal DAG at its seven-input norm cut.
guards=[]
for name in ['budget12_aux_centered','budget12_tau_centered']:
    p=json.loads((ROOT/'guard'/f'{name}.json').read_text());guards.append(p);nr=p['named_registers']
    cuts={nr[n]:e[q] for n,q in [('center','x'),('scaled_Df','a'),('scaled_Dtau','b'),('scaled_Dmain','c'),('scaled_Ag','d'),('scaled_Cy','cn'),('delta','delta')]}
    cache={}
    def get(i):
        if i in cuts:return cuts[i]
        if i in cache:return cache[i]
        n=p['nodes'][i]
        if n[0]=='integer':v=R(n[1])
        else:
            req(n[0] in ('add','sub','mul'),'unexpected uncut norm leaf')
            A,B=get(n[1]),get(n[2]);v=A+B if n[0]=='add' else A-B if n[0]=='sub' else A*B
        cache[i]=v;return v
    equal(get(p['output']),expected,name+' literal norm mismatch')
# All outer guard registers checked at exact direct-dependency cuts.
formulas={'J':'6*j+1','q':'beta*J+1','W':'12*w+4','X':'q*W','Y':'q*v','E':'X*Y','a':'E+Y','H':'4*a+3','Delta':'a*a+H','F':'(K0+W)*C-z*(q-1)','R':'(q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J','k':'R+1+h*E','eta':'c-Y*k','c2':'c*c','I':'(2*r+1)*c2','I2':'I*I','Bstrong':'Delta*I2','Df':'1+Bstrong','Q':'Delta*Bstrong','delta':'Q-1','V':'Df*(c*T-R)-c','Cy':'Q*V*V-1','ell0':'E*Y','L':'ell0*k','Dtau':'L*(L+k)+1','Dmain':'1+Delta*c2','b0':'X+a*c','coneU':'cone_A*F','coneZ':'cone_B*C','Derr':'(coneU-q)**2+(coneZ-q)**2','budget':'k*k*(q*q-Derr)-4*q*q*eta*eta','Ag':'budget-1-p2*p2-p3*(p3+1)','M':'2*q*q','U':'M*H','ML':'M','U2':'U*U','center':'s+U*V','scaled_Df':'U2*Df','scaled_Dtau':'U2*Dtau','scaled_Dmain':'ML*ML*Dmain','scaled_Ag':'U2*Ag','scaled_Cy':'U2*Cy'}
for p in guards:
    fs=formulas|{'s':'U*(n+L)+ML*b0+H*(v-q*q)' if 'tau_' in p['name'] else 'U*n+ML*b0+H*(v-q*q)'}
    names=list(dict.fromkeys(p['variables']+['beta','K0','MC','MF','cone_A','cone_B']+list(fs)))
    rr,ee=Rmake(names);cuts={};count=0
    for nm,idx in sorted(p['named_registers'].items(),key=lambda z:z[1]):
        if nm=='output':continue
        if nm in ('C','c'):continue
        cache={}
        def get(i):
            if i in cuts:return cuts[i]
            if i in cache:return cache[i]
            nd=p['nodes'][i]
            if nd[0] in ('variable','coefficient'):val=ee[nd[1]]
            elif nd[0]=='integer':val=rr(nd[1])
            else:
                A,B=get(nd[1]),get(nd[2]);val=A+B if nd[0]=='add' else A-B if nd[0]=='sub' else A*B
            cache[i]=val;return val
        want=expr(fs[nm],ee)
        equal(get(idx),want,p['name']+' register '+nm)
        if idx in cuts:ee[nm]=cuts[idx]
        else:cuts[idx]=ee[nm]
        count+=1
    receipt['checks'][p['name']+'_outer_register_cuts']=count
# Generic parity norm from all eight sign factors, permitting zero/negative radicands.
r,v=Rmake(['t','a','b','C','ra','rb','rc']);t,a,b,C,ra,rb,rc=(v[n] for n in v)
prod=r.one
for signs in itertools.product([-1,1],repeat=3):prod*=2*t+1+signs[0]*ra+2*signs[1]*rb+4*signs[2]*rc
A=4*a+1;B=4*b+1
actual=r.zero
for m,co in prod.items():
    req(all(m[i]%2==0 for i in (4,5,6)),'parity sign invariance')
    actual+=co*t**m[0]*a**m[1]*b**m[2]*C**m[3]*A**(m[4]//2)*B**(m[5]//2)*C**(m[6]//2)
U=t*(t+1)-a-B+4*C;M=U*U+4*(2*t+1)**2*C-A*B
N=M*M-16*(2*t+1)**2*U*U*C
equal(actual,256*N,'eight-sign parity norm')
receipt['checks']['generic_parity_norm']={'monomials':len(N),'zero_radicands_allowed':True}
# Absorption packet to literal DAG equality by recovering exact local register cuts.
ap=json.loads((ROOT/'finalizers/absorbed15_degree176.json').read_text());ad=json.loads((ROOT/'finalizers/absorbed15_degree176_dag.json').read_text())
forms=dict(ap['polynomial_abbreviations']);live={'norm15'}
def visit(n):
    if n not in forms:return
    for q in ast.walk(ast.parse(forms[n],mode='eval')):
        if isinstance(q,ast.Name) and q.id not in live:live.add(q.id);visit(q.id)
visit('norm15')
names=list(dict.fromkeys(ap['variables']+ap['fixed_numerals']+list(forms)));rr,env=Rmake(names)
cuts={};local_matches={}
for nm,formula in ap['polynomial_abbreviations']:
    if nm not in live:continue
    want=expr('Q-Delta*(f**2-1)' if nm=='r_strong' else formula,env)
    # Q=I**2 was checked earlier, so its shared node is an exact cut alias.
    # An alias has no gate and remains the aliased symbol.
    if isinstance(ast.parse(formula,mode='eval').body,ast.Name):env[nm]=want;continue
    vals=[];match=None
    def get(ref):
        if ref[0]=='leaf':return env[ref[1]]
        if ref[0]=='const':return rr(ref[1])
        return cuts[ref[1]] if ref[1] in cuts else vals[ref[1]]
    for i,(op,ar,br) in enumerate(ad['nodes']):
        A,B=get(ar),get(br);val=A+B if op=='add' else A-B if op=='sub' else A*B
        vals.append(val)
        if val==want:match=i;break
    req(match is not None,'absorption local DAG mismatch '+nm)
    cuts[match]=env[nm];local_matches[nm]=match
req(local_matches['norm15']==ad['output'][1],'absorption output mismatch')
receipt['checks']['absorption_exact_local_dag_cuts']=len(local_matches)
# Generic guard bounds and restoration identities.
r,v=Rmake(['q','a','b','k','eta','T','L','u','y','V','Q','D','c','Delta','f','i','F','C','K0','W','z','M','H','lc','b0','gamma','p1','vold','S'])
q,a,b,k,eta,T,L,u,y,V,Q,D,c,Delta,f,i,F,C,K0,W,z,M,H,lc,b0,gamma,p1,vold,S=(v[n] for n in v)
G=a*b-(q-a-b)**2;Z=eta*(k-eta)
equal(4*(q*q-3*G),(3*(a+b)-4*q)**2+3*(a-b)**2,'G bound identity')
equal(4*Z,k*k-(2*eta-k)**2,'Z bound identity')
equal((u-L)**2+(2*(u-L)-k)*L-1,u*u-L*(L+k)-1,'centered first source row')
equal(V*V-(Q-1)*(y-V)*(2*V+y-V)-1,Q*V*V-(Q-1)*y*y-1,'centered aux source row')
equal((q-1)*(q-F)+(q-F-C),q*(q-F)-C,'R restoration')
equal((K0+W)*C-((K0+W)*C-z*(q-1))-z*(q-1),r.zero,'source transport')
n=lc*gamma+f+u+p1+y-V-vold-S
carrier=M*H*(n+V+S)+M*lc*b0+H*M*vold
equal(carrier,M*lc*(b0+H*gamma)+M*H*(f+u+p1+y),'CRT carrier inverse')
# Exact Pell descent norm preservation (the absolute-value descent is in review).
Vp=(2*Q-1)*V-2*(Q-1)*y;yp=(2*Q-1)*y-2*Q*V
equal(Q*Vp*Vp-(Q-1)*yp*yp,Q*V*V-(Q-1)*y*y,'Pell descent norm')
receipt['checks']['generic_restoration_and_bound_identities']=8
# Guard degree upper bound by full cancellation in the inner four-component norm.
r,v=Rmake(['U','s','V','d','A','L','k','e','delta']);U,s,V,d,A,L,k,e,D=(v[n] for n in v)
weights=(6,7,19,14,26,11,5,28,22);off=(0,7,14,21)
def wt(p):return max((sum(x*y for x,y in zip(m,weights)) for m in p),default=-10000)
for centered in (False,True):
    x=U*V+s+(U*L if centered else 0);B=U*U*(L*L+L*k+1);cn=U*U*((D+1)*V*V-1)
    tt=[x*x+d+e,2*x,2*x,r(2)]
    jj=[D*(tt[0]-A-B)-cn]+[D*v for v in tt[1:]]
    kk=mq_mul(jj,jj,[d,e],r.zero);kk[0]-=4*(D*D*A*B+D*cn*(A+B))
    ff=mq_mul(kk,kk,[d,e],r.zero);ff=[v-64*D**3*A*B*cn*tt[i] for i,v in enumerate(ff)]
    degs=[wt(v)+off[i] for i,v in enumerate(ff)];req(all(z<degs[0] for z in degs[1:]),'strict scalar dominance')
    degree=4*degs[0];equal(degree,1000 if centered else 1024,'degree upper')
    receipt['checks']['guard_degree_'+str(degree)]={'inner_component_weights':degs,'upper_bound':degree}
# Coefficient payload authentication and source pin checks.
ports={};binding=json.loads((ROOT/'guard/coefficients/BINDING.json').read_text())
for nm,item in binding['payloads'].items():
    raw=gzip.decompress((ROOT/'guard/coefficients'/item['file']).read_bytes());equal(hashlib.sha256(raw).hexdigest(),item['raw_sha256'],'coefficient hash '+nm)
    ports[nm]=int.from_bytes(raw,'little')%P
    for sub in ('centered17','centered18'):
        equal(raw,gzip.decompress((ROOT/'guard/provenance'/sub/'coefficients'/item['file']).read_bytes()),'source coefficient '+sub+'/'+nm)
for pin in json.loads((ROOT/'guard/SOURCE_PINS.json').read_text())['sources']:
    raw=(ROOT/'guard'/pin['path']).read_bytes();equal(hashlib.sha256(raw).hexdigest(),pin['sha256'],'source pin '+pin['path']);equal(len(raw),pin['bytes'],'source bytes')
abinding=json.loads((ROOT/'finalizers'/ap['coefficient_binding']).read_text())
for nm,item in abinding['ports'].items():
    raw=gzip.decompress((ROOT/'finalizers'/ap['coefficient_binding']).parent.joinpath(item['file']).read_bytes())
    equal(hashlib.sha256(raw).hexdigest(),item['sha256_raw'],'absorption coefficient hash '+nm)
    equal(raw,gzip.decompress((ROOT/'guard/coefficients'/binding['payloads'][nm]['file']).read_bytes()),'same absorption exact coefficient '+nm)
    equal(int.from_bytes(raw,'little')%P,ports[nm],'same absorption coefficient '+nm)
receipt['checks']['source_pins_and_coefficients']='pass'
# Independent live-gate census and a DIFFERENT authentic-coefficient line from author.
def line_lead(p,kind,degree):
    slopes={nm:3*i*i+7*i+11 for i,nm in enumerate(p['variables'])}
    def evalat(t):
        env=ports|{nm:slopes[nm]*t%P for nm in p['variables']};vals=[]
        if kind=='guard':
            for nd in p['nodes']:
                op=nd[0]
                if op in ('variable','coefficient'):v=env[nd[1]]
                elif op=='integer':v=nd[1]
                else:
                    a,b=vals[nd[1]],vals[nd[2]];v=a+b if op=='add' else a-b if op=='sub' else a*b
                vals.append(v%P)
            return vals[p['output']]
        def get(ref):return env[ref[1]] if ref[0]=='leaf' else ref[1] if ref[0]=='const' else vals[ref[1]]
        for op,ar,br in p['nodes']:
            a,b=get(ar),get(br);vals.append((a+b if op=='add' else a-b if op=='sub' else a*b)%P)
        return get(p['output'])
    row=[evalat(t) for t in range(degree+1)]
    for _ in range(degree):row=[(b-a)%P for a,b in zip(row,row[1:])]
    lc=row[0]*pow(math.factorial(degree)%P,-1,P)%P;req(lc!=0,'actual coefficient lower bound')
    return {'prime':P,'slopes':slopes,'leading_coefficient':lc,'degree':degree,'method':'exact finite differences on independent line, with separately proved degree upper bound'}
for p in guards:
    nodes=p['nodes'];seen=set()
    degrees=[]
    for nd in nodes:
        degree=1 if nd[0]=='variable' else 0 if nd[0] in ('coefficient','integer') else degrees[nd[1]]+degrees[nd[2]] if nd[0]=='mul' else max(degrees[nd[1]],degrees[nd[2]])
        degrees.append(degree)
    for nm,upper in {'U':6,'V':19,'scaled_Dmain':14,'scaled_Df':26,'L':11,'k':5,'scaled_Ag':28,'delta':22}.items():
        equal(degrees[p['named_registers'][nm]],upper,'actual cut weight '+nm)
    if 'aux_' in p['name']:equal(degrees[p['named_registers']['s']],7,'unsheared s weight')
    def visit(i):
        if i in seen:return
        seen.add(i);nd=nodes[i]
        if nd[0] in ('add','sub','mul'):
            req(0<=nd[1]<i and 0<=nd[2]<i,'guard topology');visit(nd[1]);visit(nd[2])
        else:req(nd[0] in ('variable','coefficient','integer'),'guard syntax')
    visit(p['output']);equal(seen,set(range(len(nodes))),'guard liveness')
    counts=dict(Counter(nd[0] for nd in nodes if nd[0] in ('add','sub','mul')))
    equal(counts,p['operation_counts'],'guard counts');equal(sum(counts.values()),p['operations'],'guard operation total')
    equal({nd[1] for nd in nodes if nd[0]=='variable'},set(p['variables']),'guard variables')
    degree=1000 if 'tau_' in p['name'] else 1024
    receipt['checks'][p['name']+'_metrics']={'variables':12,'operations':sum(counts.values()),'counts':counts,'degree_certificate':line_lead(p,'guard',degree)}
# Absorption safe degree via independent max-plus AST evaluation.
class Deg:
    def __init__(self,d):self.d=d
    def co(self,x):return x if isinstance(x,Deg) else Deg(0)
    def __add__(self,x):return Deg(max(self.d,self.co(x).d))
    __radd__=__add__;__sub__=__add__;__rsub__=__add__
    def __mul__(self,x):return Deg(self.d+self.co(x).d)
    __rmul__=__mul__
    def __pow__(self,x):return Deg(self.d*x)
    def __neg__(self):return self
env={nm:Deg(1) for nm in ap['variables']}|{nm:Deg(0) for nm in ports}
for nm,fo in ap['polynomial_abbreviations']:env[nm]=expr(fo,env)
equal(env['norm15'].d,176,'absorption safe degree')
seen=set();leaves=set()
def avisit(ref):
    if ref[0]=='leaf':leaves.add(ref[1]);return
    if ref[0]=='const':req(isinstance(ref[1],int),'integer literal');return
    req(ref[0]=='node','absorption node syntax');i=ref[1]
    if i in seen:return
    seen.add(i);op,ar,br=ad['nodes'][i];req(op in ('add','sub','mul'),'absorption gate syntax')
    for child in (ar,br):
        req(child[0]!='node' or 0<=child[1]<i,'absorption topology');avisit(child)
avisit(ad['output']);equal(seen,set(range(len(ad['nodes']))),'absorption liveness')
equal(leaves,set(ap['variables']+ap['fixed_numerals']),'absorption leaf census')
counts=dict(Counter(nd[0] for nd in ad['nodes']));equal(sum(counts.values()),125,'absorption count')
receipt['checks']['absorption_metrics']={'variables':len(ad['variables']),'operations':125,'counts':counts,'degree_certificate':line_lead(ad,'absorption',176)}
# Deliberate countermodels to tempting but invalid relaxed lemmas, not source zeros.
# Irrational terminal cancellation, with the three larger roots still separated.
receipt['negative_controls']['terminal_inequality_necessary']={'roots_squared':[10000,400,25,2,2],'rational_signed_sum':125,'reason':'100+20+5+sqrt(2)-sqrt(2)=125, so three leading separations alone do not force rational terminal roots.'}
receipt['negative_controls']['unique_imaginary_guard_necessary']={'roots_squared':[10000,400,25,-2,-2],'rational_signed_sum':125,'reason':'Two imaginary roots can cancel; the positivity proof for every other radicand is essential.'}
# Verify both counterexamples by the independent norm polynomial.
for es in ([10000,400,25,2,2],[10000,400,25,-2,-2]):
    val=0
    vals=[125]+es+[1]
    for m,co in expected.items():val+=co*math.prod(v**n for v,n in zip(vals,m))
    equal(val,0,'terminal/imaginary countermodel')
# Dropping absorption penalty allows a square certificate with a nonzero retained residual.
q=a=b=k=eta=t=None
q,k,a,b,eta,t=4,4,2,2,2,2
G=a*b-(q-a-b)**2;Z=eta*(k-eta);B=G*Z-(t*t-G-Z+1)**2-1
req(4*B+1==25 and B-q*q*k*k<0,'absorption negative control')
receipt['negative_controls']['penalty_is_needed']={'q':q,'k':k,'G':G,'Z':Z,'B':B,'omitted_penalty_square':25,'residual_square_sum':1,'penalized_B':B-q*q*k*k}
# Zero auxiliary radicand is a genuine norm zero and must not be excluded early.
t,a,b,C=1,0,0,0;A=4*a+1;B=4*b+1;U=t*(t+1)-a-B+4*C;M=U*U+4*(2*t+1)**2*C-A*B
equal(M*M-16*(2*t+1)**2*U*U*C,0,'zero C parity norm')
receipt['negative_controls']['zero_auxiliary_is_real_case']={'A':1,'B':1,'C':0,'t':1}
equal(5*1**2-16*(1/2)**2,1,'non-adjacent rational Pell countermodel')
receipt['negative_controls']['adjacent_coefficient_needed']={'equation':'5*1^2-16*(1/2)^2=1','nonintegral_rational_root':'1/2'}
receipt['negative_controls']['main_residue_obstruction_needed']={'H':3,'M':2,'b0':0,'main_square':18,'other_squares':[2,4,1,1],'reason':'2*(3 sqrt(2))+6*(-sqrt(2)+2-1-1)=0 despite an irrational main root; the actual b0=2 modulo 3 forbids this pattern.'}
receipt['audited_sha256']={str(fp.relative_to(ROOT)):hashlib.sha256(fp.read_bytes()).hexdigest() for fp in audited_files}
equal(receipt['audited_sha256'],initial_hashes,'audited files changed during run')
receipt['status']='PASS'
receipt['boundary']='Exact local algebra, authentic fixed-coefficient degree certificates, and literal gate audits. Universal semantic deductions are reviewed in REVIEW.md; no new verification of inherited native compiler or syntactic refutation calibration.'
filename='RECEIPT_OPTIMIZED.json' if not __debug__ else 'RECEIPT_NORMAL.json'
(OUT/filename).write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
print(json.dumps(receipt,indent=2,sort_keys=True))
