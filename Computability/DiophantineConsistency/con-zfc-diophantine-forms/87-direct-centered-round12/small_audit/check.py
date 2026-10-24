#!/usr/bin/env python3
"""Independent restricted-data audit. Standard library only; no producer imports.
Finite tests are not proofs of semantic compiler/Pell interfaces. Analytic
upper-degree and zero-set arguments are reviewed in REPORT.md.
"""
import ast, collections, gzip, hashlib, json, pathlib, random
ROOT=pathlib.Path(__file__).resolve().parents[1]
OUT=pathlib.Path(__file__).resolve().parent
PRIMES=(1000000007,1000000009,998244353)

def require(ok,msg):
    if not ok: raise RuntimeError(msg)

def sha(data): return hashlib.sha256(data).hexdigest()

def parse(s):
    n=ast.parse(s,mode='eval').body
    def valid(x):
        if isinstance(x,ast.Name): return
        if isinstance(x,ast.Constant) and type(x.value) is int: return
        if isinstance(x,ast.UnaryOp) and isinstance(x.op,(ast.UAdd,ast.USub)): return valid(x.operand)
        if isinstance(x,ast.BinOp) and isinstance(x.op,(ast.Add,ast.Sub,ast.Mult,ast.Pow)):
            if isinstance(x.op,ast.Pow): require(isinstance(x.right,ast.Constant) and type(x.right.value) is int and 0<=x.right.value<=100,'nonliteral exponent')
            valid(x.left); valid(x.right); return
        raise RuntimeError('forbidden AST '+ast.dump(x))
    valid(n); return n

def names(n): return {x.id for x in ast.walk(n) if isinstance(x,ast.Name)}

def calc(n,env,constant=lambda x:x):
    if isinstance(n,ast.Name): return env[n.id]
    if isinstance(n,ast.Constant): return constant(n.value)
    if isinstance(n,ast.UnaryOp):
        r=calc(n.operand,env,constant); return -r if isinstance(n.op,ast.USub) else r
    a=calc(n.left,env,constant)
    if isinstance(n.op,ast.Pow): return a**n.right.value
    b=calc(n.right,env,constant)
    if isinstance(n.op,ast.Add): return a+b
    if isinstance(n.op,ast.Sub): return a-b
    return a*b

class Mod:
    p=PRIMES[0]
    def __init__(self,x): self.x=int(x)%self.p
    def __add__(self,y): return Mod(self.x+y.x)
    def __sub__(self,y): return Mod(self.x-y.x)
    def __mul__(self,y): return Mod(self.x*y.x)
    def __neg__(self): return Mod(-self.x)
    def __pow__(self,n): return Mod(pow(self.x,n,self.p))
    def __eq__(self,y): return isinstance(y,Mod) and self.x==y.x

class Uni:
    """Dense exact polynomial arithmetic over F_p, not degree propagation."""
    p=PRIMES[0]
    def __init__(self,a):
        if type(a) is int: a=[a]
        a=[x%self.p for x in a]
        while len(a)>1 and a[-1]==0: a.pop()
        self.a=a
    def __add__(self,b):
        a=self.a; b=b.a; c=[0]*max(len(a),len(b))
        for i,x in enumerate(a):c[i]+=x
        for i,x in enumerate(b):c[i]+=x
        return Uni(c)
    def __neg__(self):return Uni([-x for x in self.a])
    def __sub__(self,b):return self+-b
    def __mul__(self,b):
        c=[0]*(len(self.a)+len(b.a)-1)
        for i,x in enumerate(self.a):
            for j,y in enumerate(b.a):c[i+j]+=x*y
        return Uni(c)
    def __pow__(self,n):
        a=self;r=Uni(1)
        while n:
            if n&1:r=r*a
            n//=2
            if n:a=a*a
        return r
    def __eq__(self,y):return isinstance(y,Uni) and self.a==y.a
    @property
    def degree(self):return -1 if self.a==[0] else len(self.a)-1

class Sparse:
    """Exact Z[M,V,D,z,e,A,Q] algebra, for universal cancellation checks."""
    N=7
    def __init__(self,d=0):self.d={(0,)*self.N:d} if type(d) is int and d else ({} if type(d) is int else {m:c for m,c in d.items() if c})
    def __add__(self,b):
        d=self.d.copy()
        for m,c in b.d.items():d[m]=d.get(m,0)+c
        return Sparse(d)
    def __neg__(self):return Sparse({m:-c for m,c in self.d.items()})
    def __sub__(self,b):return self+-b
    def __mul__(self,b):
        d={}
        for m,c in self.d.items():
            for n,e in b.d.items():
                k=tuple(x+y for x,y in zip(m,n));d[k]=d.get(k,0)+c*e
        return Sparse(d)
    def __pow__(self,n):
        r=Sparse(1)
        for _ in range(n):r=r*self
        return r
    def __eq__(self,b):return self.d==b.d

def load_binding(folder,name):
    binding=json.loads((folder/name).read_text()); vals={}; rows={}
    for k,x in binding['ports'].items():
        path=folder/(x.get('path') or x['file']); enc=path.read_bytes();raw=gzip.decompress(enc)
        require(sha(raw)==(x.get('raw_sha256') or x['sha256_raw']),k+' raw hash')
        require(sha(enc)==(x.get('gzip_sha256') or x['sha256_gzip']),k+' compressed hash')
        v=int.from_bytes(raw,'little');require(v.bit_length()==x['bits'],k+' bit length');require(len(raw)==x['raw_bytes'],k+' byte length')
        require(v>0 and raw[-1]!=0,k+' nonminimal or nonpositive')
        vals[k]=v;rows[k]={'raw_sha256':sha(raw),'bits':v.bit_length(),'bytes':len(raw)}
    return vals,rows

LOW=ROOT/'low_degree';POS=ROOT/'positive'
lc,lh=load_binding(LOW,'BINDING.json');pc,ph=load_binding(POS/'native','ACTIVE_BINDING.json')
require(lc['beta']==(1<<1064921)-1,'integer beta');require(lc['cone_A']==1<<1113,'cone A');require(lc['cone_B']==1<<666104,'cone B')
require(pc['beta']==(1<<590069)-1,'positive beta');require(0<pc['MC']<pc['beta'] and pc['beta']<pc['MF']<2*pc['beta'],'positive mask bounds')
parent=json.loads((LOW/'inherited/degree12_24.json').read_text());pt=[parse(x) for x in parent['residuals']]
rng=random.Random(120024); low_results=[]
for path in sorted(LOW.glob('integer*.json')):
    p=json.loads(path.read_text()); ts=[parse(x) for x in p['residuals']];rs={k:parse(s) for k,s in p['restoration'].items()}
    require(p['domain']=='unrestricted integers','integer domain')
    require(len(p['variables'])==len(set(p['variables']))==p['variable_count'],'integer variables')
    require(len(ts)==p['equation_count'],'row count')
    leaves=set().union(*(names(t) for t in ts));require(leaves<=set(p['variables'])|set(p['fixed_numerals']),'free variable')
    require(set(p['variables'])<=leaves,'dead variable')
    ids=[i for i in range(12) if i not in p['deleted_source_rows']]
    count=0;degrees=[]
    for prime in PRIMES:
        Mod.p=Uni.p=prime
        constants={k:Mod(v) for k,v in lc.items()}
        for trial in range(100):
            raw={v:(0 if trial==0 else (-1 if trial==1 else (1 if trial==2 else rng.randrange(-50,51)))) for v in p['variables']}
            env=constants|{v:Mod(x) for v,x in raw.items()}
            restored=env|{k:calc(t,env,Mod) for k,t in rs.items()}
            old=restored.copy();old['tau']=restored['tau']+restored['E']*(restored['c']-restored['eta'])
            if p['auxiliary_root_shear']:old['y']=restored['f']*restored['o']+restored['y']
            oldrows=[calc(t,old,Mod) for t in pt];newrows=[calc(t,env,Mod) for t in ts]
            for idx in p['deleted_source_rows']:require(oldrows[idx]==Mod(0),f'{path.name}: deleted row {idx}')
            for row,value in zip(ids,newrows):
                expected=oldrows[row]
                if row==10 and p['auxiliary_root_shear']:
                    expected=expected+oldrows[9]*(old['y']**2-old['V']**2)
                require(value==expected,f'{path.name}: row {row} mismatch')
            count+=1
        env={k:Uni(v) for k,v in lc.items()}|{v:Uni([0,i+2]) for i,v in enumerate(p['variables'])}
        vals=[calc(t,env,Uni) for t in ts];out=sum_poly=[Uni(0)]
        total=Uni(0)
        for v in vals:total=total+v*v
        require(total.degree==p['exact_degree'],path.name+' actual tuple degree lower bound')
        require(all(v.degree<=bound for v,bound in zip(vals,p['residual_degree_bounds'])),path.name+' slice exceeds bound')
        degrees.append({'prime':prime,'residual_degrees':[v.degree for v in vals],'degree':total.degree,'leading_coefficient':total.a[-1]})
    low_results.append({'file':path.name,'sha256':sha(path.read_bytes()),'variables':len(p['variables']),'rows':len(ts),'signed_modular_assignments':count,'actual_tuple_slices':degrees})

p=json.loads((POS/'p11_degree211.json').read_text());source=p['source'];decl=set(p['witnesses'])|set(p['fixed_numerals']);seen=set(decl);by={};ops=collections.Counter()
for row in source:
    require(isinstance(row,list) and len(row)==4,'circuit row');out,op,a,b=row
    require(out not in seen and op in ('+','-','*'),'SSA operation')
    for x in (a,b):require(type(x) is int or isinstance(x,str) and x in seen,'future or unknown reference')
    seen.add(out);by[out]=row;ops[op]+=1
live=set()
def mark(x):
    if type(x) is int or x in live:return
    live.add(x)
    if x in by:mark(by[x][2]);mark(by[x][3])
mark(p['output'])
require(set(by)<=live,'dead arithmetic gate');require(decl<=live,'dead positive leaf');require(len(source)==113==p['operations'],'operation total');require(dict(ops)==p['operation_breakdown'],'operation breakdown')
require(len(set(p['witnesses']))==11 and p['domain']=='strictly positive integers','positive domain')

def run(env,const):
    env=env.copy()
    for out,op,a,b in source:
        a=env[a] if isinstance(a,str) else const(a);b=env[b] if isinstance(b,str) else const(b)
        env[out]=a+b if op=='+' else (a-b if op=='-' else a*b)
    return env

# A direct transcription from the mathematics, not from the gate generator.
formula='''J=3*j+1
q=beta*J+1
C=q-F-alpha
E=X*Y
k=eta+zeta
c=k*Y+eta
a=E+Y
Aparam=a+2
H=4*a+3
Delta=a*a+H
ell=E*k*Y
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
M=q**3*(q-1)
Bt=(q*K0+X)*C-q*F
Dtau=ell*(ell+k)+1
I=i*c*c
Df=1+Delta*I*I
Q=Delta*(Df-1)
delta=Q-1
Told=T+q+alpha
b=c*Told-R
V=Df*b-c
Dcenter=Aparam*I
L=k*Told+F
W=1+(q-1)*L
Zbar=M*(ell+k+n+L+V+Dcenter)+(q-1)*Y-q**3*W*Bt
r0=k-R-1
S=4*q*Y
U=q*S
Dstar=U*(X+a*c)+H*(U*gamma+S*X-r0)
A1=Dstar*Dstar-U*U*(1+Delta*c*c)
A=M*M*Dtau
Bf=M*M*Df
Cnum=M*M*(Q*V*V-1)
Tn=delta*delta*A*Bf
Rn=delta*Cnum
Jn=delta*(Zbar*Zbar-A-Bf)-Cnum
Ncenter=Jn*Jn-4*(Tn+Rn*(A+Bf))
N8=Ncenter*Ncenter-64*Tn*Rn*Zbar*Zbar
P11=N8+A1+N8*A1'''
forms=[(s.split('=',1)[0],parse(s.split('=',1)[1])) for s in formula.splitlines()]
pos_slices=[]
for prime in PRIMES:
    Mod.p=Uni.p=prime
    for trial in range(200):
        env={k:Mod(v) for k,v in pc.items()}|{v:Mod(rng.randrange(-50,51)) for v in p['witnesses']}
        actual=run(env,Mod);expected=env.copy()
        for k,t in forms:expected[k]=calc(t,expected,Mod)
        for k in expected.keys()&actual.keys():require(expected[k]==actual[k],'positive literal mismatch '+k)
    env={k:Uni(v) for k,v in pc.items()}|{v:Uni([0,i+2]) for i,v in enumerate(p['witnesses'])}
    result=run(env,Uni)
    require(result['N8'].degree==198 and result['A1'].degree==13 and result['P11'].degree==211,'positive actual coefficient slice degrees')
    pos_slices.append({'prime':prime,'degree':result['P11'].degree,'norm_degree':result['N8'].degree,'carrier_degree':result['A1'].degree,'leading_coefficient':result['P11'].a[-1]})

# Universal cancellation identity: exact sparse integer arithmetic.
variables=[]
for i in range(7):
    m=[0]*7;m[i]=1;variables.append(Sparse({tuple(m):1}))
M,V,D,z,e,A,Q=variables;one=Sparse(1);delta=Q-one;B=M*M*(D*D-e);C=M*M*(Q*V*V-one);Z=z+M*(V+D)
T=delta*delta*A*B;R=delta*C;J=delta*(Z*Z-A-B)-C
H=z*z+Sparse(2)*M*D*z+M*M*e-A
require(J==delta*(H+Sparse(2)*M*V*(z+M*D))-M*M*(V*V-one),'center identity')
N=J*J-Sparse(4)*(T+R*(A+B));N8=N*N-Sparse(64)*T*R*Z*Z
weights=(4,18,7,8,10,16,18)
def wt(m):return sum(x*y for x,y in zip(m,weights))
def top(f):
    d=max(map(wt,f.d));return d,{m:c for m,c in f.d.items() if wt(m)==d}
nd,nt=top(N);pd,ptop=top(N8)
require(nd==99 and nt=={(3,2,1,1,0,0,2):8},'norm center universal head')
require(pd==198 and ptop=={(6,4,2,2,0,0,4):64,(6,4,2,0,0,1,4):-64},'norm universal head')

# All eight conjugates: work in Z[x,a,b,c] with root symbols, no radicals.
oldn=Sparse.N;Sparse.N=4
vs=[]
for i in range(4):
 m=[0]*4;m[i]=1;vs.append(Sparse({tuple(m):1}))
x,a,b,c=vs;prod=Sparse(1)
for sa in (-1,1):
 for sb in (-1,1):
  for sc in (-1,1):prod=prod*(x+Sparse(sa)*a+Sparse(sb)*b+Sparse(sc)*c)
identity=((x*x-a*a-b*b-c*c)**2-Sparse(4)*(a*a*b*b+a*a*c*c+b*b*c*c))**2-Sparse(64)*a*a*b*b*c*c*x*x
require(prod==identity,'eight conjugate identity');Sparse.N=oldn

report={'status':'PASS','scope':'Independent data, algebra, coefficient hashes, finite signed transcription checks, actual-coefficient degree lower bounds. Universal upper-degree and existence arguments are separately reviewed; this is not a formal semantic certificate.','integer_coefficients':lh,'positive_coefficients':ph,'integer_packets':low_results,'positive':{'file':'p11_degree211.json','sha256':sha((POS/'p11_degree211.json').read_bytes()),'variables':11,'operations':len(source),'operation_breakdown':dict(ops),'signed_modular_assignments':600,'actual_tuple_slices':pos_slices,'universal_center_terms':len(N.d),'universal_norm_terms':len(N8.d),'universal_center_weighted_degree':nd,'universal_norm_weighted_degree':pd,'eight_conjugate_identity':True}}
(OUT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({'status':report['status'],'integer_packets':len(low_results),'integer_modular_assignments':sum(x['signed_modular_assignments'] for x in low_results),'positive_modular_assignments':600,'positive_operations':len(source),'positive_degree':211},indent=2))

# Additional materialized twelve-positive endpoint, supplied after initial audit.
p12=json.loads((POS/'p12_degree70.json').read_text());source=p12['source'];decl=set(p12['witnesses'])|set(p12['fixed_numerals']);seen=set(decl);by={};ops=collections.Counter()
for row in source:
    require(isinstance(row,list) and len(row)==4,'p12 row');out,op,a,b=row
    require(out not in seen and op in ('+','-','*'),'p12 SSA')
    for x in (a,b):require(type(x) is int or isinstance(x,str) and x in seen,'p12 undefined leaf')
    seen.add(out);by[out]=row;ops[op]+=1
live=set();mark(p12['output'])
require(set(by)<=live and decl<=live,'p12 dead nodes');require(len(source)==100==p12['operations'],'p12 total');require(dict(ops)==p12['operation_breakdown'],'p12 breakdown')
require(len(set(p12['witnesses']))==12 and p12['domain']=='strictly positive integers','p12 domain')
formula12='''J=6*j+1
q=beta*J+1
C=q-F-alpha
E=X*Y
k=eta+zeta
c=k*Y+eta
a=E+Y
H=4*a+3
Delta=a*a+H
ell=E*k*Y
R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
U=q*q*Y
r0=k-R-1
W=1+(q-1)*k
M=q**3*(q-1)
Bt=(q*K0+X)*C-q*F
Dstar=U*(X+a*c)+H*(U*gamma+q*E-r0)
root0=M*(ell+k+r)+(q-1)*Y-q**3*W*Bt
A0=root0*root0-M*M*(ell*(ell+k)+1)
A1=Dstar*Dstar-U*U*(1+Delta*c*c)
f=t+1
rho=f*f-1
Q=Delta*rho
d=c**4
V=f*f*(c*T-R)-c
aux_a=(1-Q)*n*n+2*(1-Q)*V*n+V*V-1
aux_b=2*(1-Q)*(n+V)
normA=d*aux_a+(1-Q)*Q
N=normA*normA-d*aux_b*aux_b*Q
P12=(1+A0)*(1+A1)*(1+N)-1'''
forms12=[(s.split('=',1)[0],parse(s.split('=',1)[1])) for s in formula12.splitlines()]
slices12=[]
for prime in PRIMES:
    Mod.p=Uni.p=prime
    for trial in range(200):
        env={k:Mod(v) for k,v in pc.items()}|{v:Mod(rng.randrange(-50,51)) for v in p12['witnesses']}
        actual=run(env,Mod);expected=env.copy()
        for k,t in forms12:expected[k]=calc(t,expected,Mod)
        for k in expected.keys()&actual.keys():require(expected[k]==actual[k],'p12 literal mismatch '+k)
    env={k:Uni(v) for k,v in pc.items()}|{v:Uni([0,i+2]) for i,v in enumerate(p12['witnesses'])}
    result=run(env,Uni);ds=[result[k].degree for k in ['A0','A1','N','P12']]
    require(ds==[15,13,42,70],'p12 actual-tuple slice degrees')
    slices12.append({'prime':prime,'degrees':ds,'leading_coefficient':result['P12'].a[-1]})
Sparse.N=4;vs=[]
for i in range(4):
 m=[0]*4;m[i]=1;vs.append(Sparse({tuple(m):1}))
d,n,V,i=vs;one=Sparse(1);Q=d*i*i
h=lambda x:(one-Q)*x*x+Sparse(2)*(one-Q)*V*x+V*V-one
b=Sparse(2)*(one-Q)*(n+V);normA=d*h(n)+(one-Q)*Q
require(normA*normA-d*b*b*Q==d*d*h(n-i)*h(n+i),'ordinary norm merger universal identity')
report['positive12']={'file':'p12_degree70.json','sha256':sha((POS/'p12_degree70.json').read_bytes()),'variables':12,'operations':len(source),'operation_breakdown':dict(ops),'signed_modular_assignments':600,'actual_tuple_slices':slices12,'universal_merger_identity':True,'novelty':'Materialization of incoming manuscript, not a new construction'}
(OUT/'CHECKS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({'positive12_status':'PASS','positive12_operations':len(source),'positive12_degree':70},indent=2))
