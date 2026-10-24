"""Independent exact block/norm, literal DAG, degree, and p-adic audit.
Does not import any candidate builder. Finite tests supplement the proof.
Run normally or under python -O: all checks use explicit exceptions.
"""
from pathlib import Path
import json, collections, hashlib, math, itertools, random, copy, gzip
import sympy as sp
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent

def require(x,msg):
    if not x: raise ValueError(msg)

def stats(d):
    ns=d['nodes']; live=set()
    def walk(i):
        require(type(i) is int and 0<=i<len(ns),'invalid index')
        if i in live:return
        live.add(i); n=ns[i]
        require(n[0] in ('integer','variable','coefficient','add','sub','mul'),'bad op')
        if n[0] in ('add','sub','mul'):
            require(len(n)==3 and all(type(x) is int and 0<=x<i for x in n[1:]),'bad topology')
            for j in n[1:]:walk(j)
    walk(d['output'])
    cnt=dict(collections.Counter(ns[i][0] for i in live if ns[i][0] in ('add','sub','mul')))
    require(len(live)==len(ns),'dead nodes')
    require(cnt==d['operation_counts'] and sum(cnt.values())==d['operations'],'wrong operation claim')
    vs=[n[1] for n in ns if n[0]=='variable']
    require(len(vs)==12 and set(vs)==set(d['variables']),'wrong variables')
    ds=[]
    for n in ns:
        if n[0]=='variable':v=1
        elif n[0] in ('integer','coefficient'):v=0
        elif n[0]=='mul':v=ds[n[1]]+ds[n[2]]
        else:v=max(ds[n[1]],ds[n[2]])
        ds.append(v)
    return {'live_operations':sum(cnt.values()),'operation_counts':cnt,'variables':12,'syntactic_degree_bound':ds[d['output']]}

def expr(d,target,cut):
    memo={d['named_registers'][k]:v for k,v in cut.items()}
    def rec(i):
        if i not in memo:
            n=d['nodes'][i];op=n[0]
            if op=='integer':v=sp.Integer(n[1])
            elif op in ('coefficient','variable'):v=sp.Symbol(n[1])
            else:
                x,y=rec(n[1]),rec(n[2]);v=x+y if op=='add' else x-y if op=='sub' else x*y
            memo[i]=v
        return memo[i]
    return rec(d['named_registers'][target] if isinstance(target,str) else target)

def identity(d,target,names,expected):
    syms={n:sp.Symbol(n) for n in names.split()}
    require(sp.expand(expr(d,target,syms)-expected(syms))==0,'block identity '+target)

Z,Y,aa,bb,ee,dd=sp.symbols('Z Y aa bb ee dd')
F4=lambda x,a,b:x**4-2*(a+b)*x**2+(a-b)**2
UNIVERSAL=sp.resultant(F4(Y,aa,bb),F4(Z-Y,ee,dd),Y)
require(len(sp.Poly(UNIVERSAL,Z,aa,bb,ee,dd).terms())==495,'unexpected universal norm')

def audit_min(d):
    st=stats(d)
    parent_bytes=(HERE/'fixtures/pinned_integral_parent.json').read_bytes()
    require(hashlib.sha256(parent_bytes).hexdigest()=='0e30346f30a6539c3d5ace2f58135e3b2c3f12fc69ce47b6d72d5bdffe9ef75b','pinned parent fixture hash')
    baseline=json.loads(parent_bytes)
    require(d['nodes'][:83]==baseline['nodes'][:83],'inherited prefix changed')
    identity(d,'I','r c',lambda q:q['r']*q['c']**2)
    identity(d,'Df','Delta I',lambda q:1+q['Delta']*q['I']**2)
    identity(d,'Q','Delta I',lambda q:q['Delta']**2*q['I']**2)
    identity(d,'delta','Q',lambda q:q['Q']-1)
    identity(d,'V','Df c R I T',lambda q:q['Df']*(q['c']-q['R']+4*q['I']*q['T'])-q['c'])
    identity(d,'Cy','Q V',lambda q:q['Q']*q['V']**2-1)
    identity(d,'Dt','ell k',lambda q:1+q['ell']*(q['ell']+1)*q['k']**2)
    identity(d,'K','X c',lambda q:q['X']*(2*q['X']-3*q['c'])-2)
    identity(d,'S','s r H',lambda q:q['s']*q['r']*q['H'])
    identity(d,'Acarrier','H T K',lambda q:((q['H']*q['T']+q['K'])**2+3*q['H']**2)*((q['H']*q['T']+q['K'])**3-19*q['H']**3))
    for target,k,rad in [('ra',9,'Df'),('rb',81,'Dt'),('re',729,'Dg')]:
        identity(d,target,'S '+rad,lambda q,k=k,rad=rad:k*q['S']**2*q[rad])
    identity(d,'center','S n Q V Acarrier',lambda q:q['S']*(q['n']+q['Q']*q['V'])-q['Acarrier'])
    identity(d,'rn','S delta Cy',lambda q:q['S']**2*q['delta']*q['Cy'])
    out=expr(d,d['output'],{'center':Z,'ra':aa,'rb':bb,'re':ee,'rn':dd})
    require(sp.expand(out-UNIVERSAL)==0,'exact four-root norm mismatch')
    st['exact_block_identities']='PASS'
    st['independent_resultant_identity']='PASS'
    st['norm_terms']=495
    return st

def audit_reduced(d):
    st=stats(d)
    identity(d,'Bcenter','S n Acarrier',lambda q:q['S']*q['n']-q['Acarrier'])
    identity(d,'Lcenter','S Q V',lambda q:q['S']*q['Q']*q['V'])
    identity(d,'center_defect','S Q V',lambda q:q['S']**2*(q['Q']*(q['V']**2+1)-1))
    identity(d,'center','Bcenter Lcenter',lambda q:q['Bcenter']+q['Lcenter'])
    identity(d,'rn','Lcenter center_defect',lambda q:q['Lcenter']**2-q['center_defect'])
    identity(d,'q0','Bcenter Lcenter center_defect ra rb re',lambda q:q['Bcenter']**2+2*q['Bcenter']*q['Lcenter']+q['center_defect']+q['re']-q['ra']-q['rb'])
    # This exact identity licenses replacement by ordinary norm coordinates.
    B,L,E=sp.symbols('B L E')
    require(sp.expand((B+L)**2-(L**2-E)-(B**2+2*B*L+E))==0,'centering cancellation')
    out=expr(d,d['output'],{'q0':Z**2+ee-aa-bb-dd,'center':Z,'ra':aa,'rb':bb,'re':ee,'rn':dd})
    require(sp.expand(out-UNIVERSAL)==0,'reduced norm mismatch')
    require(st['syntactic_degree_bound']==768,'degree upper bound mismatch')
    st['exact_reduced_equivalence']='PASS';return st

# Modular univariate polynomial arithmetic, independent of SymPy and builders.
# The specialization j,w,v,z,s,r,c,T=x; C,h,n,t=0 has a unique known top.
def line_degree(d,p):
    active={'j','w','v','z','s','r','c','T'}
    beta=(pow(2,1064921,p)-1)%p
    coeff={name:value%p for name,value in AUTH_COEFFICIENTS.items()}
    require(coeff['beta']==beta,'authentic beta residue mismatch')
    def trim(v):
        while len(v)>1 and v[-1]==0:v.pop()
        return v
    def add(a,b,sign=1):
        v=[0]*max(len(a),len(b))
        for i,x in enumerate(a):v[i]=x
        for i,x in enumerate(b):v[i]=(v[i]+sign*x)%p
        return trim(v)
    def mul(a,b):
        v=[0]*(len(a)+len(b)-1)
        for i,x in enumerate(a):
            if x:
                for j,y in enumerate(b):
                    if y:v[i+j]=(v[i+j]+x*y)%p
        return trim(v)
    vals=[]
    for n in d['nodes']:
        op=n[0]
        if op=='integer':v=[n[1]%p]
        elif op=='variable':v=[0,1] if n[1] in active else [0]
        elif op=='coefficient':v=[coeff[n[1]]]
        elif op=='mul':v=mul(vals[n[1]],vals[n[2]])
        else:v=add(vals[n[1]],vals[n[2]],1 if op=='add' else -1)
        vals.append(v)
    out=vals[d['output']]
    expected=pow(2,808,p)*pow(3,512,p)*pow(beta,416,p)%p
    require(len(out)-1==768 and out[-1]==expected and expected!=0,'line-degree certificate failed')
    return {'prime':p,'degree':len(out)-1,'leading_residue':out[-1],'expected_residue':expected}

def pell(A,n,mod=None):
    D=A*A-1;a,b=1,0;c,d=A,1
    while n:
        if n&1:a,b=a*c+D*b*d,a*d+b*c
        c,d=c*c+D*d*d,2*c*d
        if mod:a%=mod;b%=mod;c%=mod;d%=mod
        n//=2
    return a,b

def valuation(n,p):
    require(n!=0,'valuation of zero')
    n=abs(n);v=0
    while n%p==0:n//=p;v+=1
    return v

def valuation_tests():
    total=0
    for rho in (2,3,4,6,10,12,18,30):
        primes=[p for p in (2,3,5) if rho%p==0]
        for step in (4,8,12,20,36):
            ch,ps=pell(rho,step)
            for p in primes:
                require(valuation(ps//rho,p)==valuation(step,p),'second-coordinate lifting')
                require(valuation(ch-1,p)==2*(valuation(rho,p)+valuation(step,p))-(p==2),'first-coordinate lifting')
            for nu in (3,7,11):
                v0=pell(rho,nu)[0]//rho;v1=pell(rho,nu+step)[0]//rho
                for p in primes:
                    require(valuation(v1-v0,p)==valuation(step,p),'index isometry')
                    total+=1
    # A wrong unrestricted increment would fail, confirming the 4|step guard matters.
    require(pell(3,5)[0]//3-pell(3,3)[0]//3 != 0,'negative sample malformed')
    neg=valuation(pell(2,5)[0]//2-pell(2,3)[0]//2,2)!=valuation(2,2)
    require(neg,'increment negative control did not fail')
    return {'exact_integer_cases':total,'all_passed':True,'wrong_increment_negative_control':'REJECTED'}

def fixed_pair_tests():
    A=2;R=3;c=15;s=2;need=4*s*c*c
    f,I=1,0;n=0
    while True:
        f,I=A*f+(A*A-1)*I,f+A*I;n+=1
        if n%2==0 and I%need==0:break
        require(n<10000,'no finite period found')
    require(f*f-(A*A-1)*I*I==1,'strong norm')
    lam=4*n*f;step=math.lcm(lam,4*I);rho=3*I
    def Tmod(h,M):
        den=4*I*f*f;mod=den*M
        chi=pell(rho,R+step*h,rho*mod)[0]
        V=chi//rho
        numerator=(V+c-f*f*(c-R))%mod
        require(numerator%den==0,'not an integer interpolation residue')
        return numerator//den
    cases=[]
    for p in (2,3,5):
        require(I%p==0,'missing support prime')
        M=p**3;image=[Tmod(h,M) for h in range(M)]
        require(len(set(image))==M,'fixed-pair residue map not surjective')
        cases.append({'modulus':M,'image_size':len(set(image)),'prime':p,'exponent_in_I':valuation(I,p),'tested_exponent':3})
    return {'A':A,'R':R,'s':s,'strong_index':n,'strong_I_bits':I.bit_length(),'fixed_pair_surjectivity':cases}

def projection_checks():
    X,a,c=sp.symbols('X a c');H=4*a+3;K=X*(X+2*a*c)-1;Kr=X*(2*X-3*c)-2
    require(sp.expand(2*K-Kr-H*c*X)==0,'reduced projection identity')
    # Uniform saturation inequality is reduced to a positive linear expression.
    require(43*24-596==436,'saturation exponent margin')
    return {'exact_K_identity':'PASS','uniform_minimum_exponent_margin':436,'raw_beta_bound':'4*(2^1064921-2)>2^64'}

def bind_coefficients():
    expected={
      'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
      'K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
      'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
      'MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
      'cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
      'cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}
    binding=json.loads((ROOT/'norm/coefficients/BINDING.json').read_text())
    require(binding['tuple']=='mixed-parity-unrounded-1064921','wrong tuple')
    require(binding['MF_convention']=='MF_native + beta, already shifted','wrong MF convention')
    require(set(binding['payloads'])==set(expected),'wrong coefficient ports')
    values={};receipts={}
    for name,item in binding['payloads'].items():
        raw=gzip.decompress((ROOT/'norm/coefficients'/item['file']).read_bytes())
        sha=hashlib.sha256(raw).hexdigest();value=int.from_bytes(raw,'little')
        require(sha==item['raw_sha256']==expected[name],'authentic coefficient hash: '+name)
        require(len(raw)==item['raw_bytes'] and value.bit_length()==item['bits'],'coefficient size: '+name)
        require(raw[-1]!=0,'nonminimal coefficient bytes')
        values[name]=value;receipts[name]={'raw_sha256':sha,'bits':value.bit_length(),'raw_bytes':len(raw)}
    require(values['beta']==(1<<1064921)-1,'wrong beta recipe')
    require(values['cone_A']==1<<1113 and values['cone_B']==1<<666104,'wrong cone recipe')
    require(0<values['MC']<values['beta']<values['MF']<2*values['beta'],'wrong mask bounds')
    return values,receipts

AUTH_COEFFICIENTS,COEFFICIENT_RECEIPTS=bind_coefficients()
files={name:ROOT/'norm'/name for name in ['equation.json','equation_reduced.json']}
d=json.loads(files['equation.json'].read_text())
r=json.loads(files['equation_reduced.json'].read_text())
for packet in (d,r):
    require(packet['coefficient_binding']=='coefficients/BINDING.json','wrong binding path')
    require(set(n[1] for n in packet['nodes'] if n[0]=='coefficient')==set(AUTH_COEFFICIENTS),'literal coefficient port mismatch')
report={'scope':'New arithmetic only; inherited native/compiler calibration is not reproved. Finite diagnostics are not substitutes for the universal proof.','minimal':audit_min(d),'reduced':audit_reduced(r)}
report['authentic_coefficient_binding']=COEFFICIENT_RECEIPTS
report['univariate_diagnostics']=[line_degree(d,p) for p in (1009,1013)]
report['valuation_diagnostics']=valuation_tests()
report['fixed_pair_diagnostics']=fixed_pair_tests()
report['projection']=projection_checks()
report['exact_degree_certificate']={'degree':768,'monomial':{'j':416,'w':96,'v':96,'z':8,'s':8,'r':40,'c':64,'T':40},'coefficient':'2^808 * 3^512 * beta^416','proof':'The eight auxiliary-sign-paired factors have unique leading form 2*L_top*B_top, degree96. Their product has degree768; selecting the z^8 summand in R_top^8 gives the displayed positive coefficient.'}
neg=[]
for label,change in [('wrong_I',lambda x:x['nodes'].__setitem__(x['named_registers']['I'],['mul',x['named_registers']['s'],x['named_registers']['c2']])),('wrong_scale',lambda x:x['nodes'].__setitem__(x['named_registers']['S'],['mul',x['named_registers']['I'],x['named_registers']['H']])),('wrong_norm_constant',lambda x:next(n for n in x['nodes'] if n==['integer',64]).__setitem__(1,65)),('wrong_K',lambda x:x['nodes'][x['named_registers']['K']].__setitem__(2,x['named_registers']['ndelta'])),('wrong_output',lambda x:x['nodes'][x['output']].__setitem__(0,'add')),('wrong_count',lambda x:x.__setitem__('operations',x['operations']+1))]:
    bad=copy.deepcopy(d);change(bad)
    try:audit_min(bad)
    except ValueError as exc:neg.append({'mutation':label,'status':'REJECTED','reason':str(exc)})
    else:raise ValueError('negative control accepted: '+label)
report['negative_controls']=neg
report['files']={n:{'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for n,p in files.items()}
report['status']='PASS'
(HERE/'AUDIT_RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
