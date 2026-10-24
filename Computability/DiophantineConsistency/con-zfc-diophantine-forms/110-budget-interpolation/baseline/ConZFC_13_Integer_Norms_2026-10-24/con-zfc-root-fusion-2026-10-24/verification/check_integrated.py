#!/usr/bin/env python3
"""Independent arithmetic audit of the root-fusion deliverable.

This program does not import build_equations.py.  It independently rebuilds
the six actual integer coefficients, evaluates the front end in different
algebraic forms, and uses a formal conjugate product for modular diagnostics.
The identities and degree certificates are exact integer-polynomial checks;
the finite modular comparisons are only transcription diagnostics.
"""
from pathlib import Path
from collections import Counter, defaultdict
import argparse, gzip, hashlib, json, random, time
from exact_polynomial import Ring

HERE = Path(__file__).resolve().parent
PORTS = ('beta','K0','MC','MF','cone_A','cone_B')
EXPECTED_HASHES = {
 'beta':'6a029139964239dc65d716ccc186b40d9c5923ada0a4116cbb418d84534096ea',
 'K0':'18c40dd3b52b2882ee8346d098942ae487b54d0d040d9cd88f826b050794d1af',
 'MC':'3fc17cf73716c7528a91d45dc2bfffa8b76fb86d6d14f5451cf32c125a588777',
 'MF':'78a7befe6b09c6f59bb325aec1ef35caa72bc6a7d2d01fa39071b9c6e8d92722',
 'cone_A':'66463b4c98a7cd43faffe6cc0462f7f4fa65b7fd9bc57cba38789e585d59c615',
 'cone_B':'42be64ea01465eb227e9c993dba41affc2d9244aed8ec8f33d3268bda7c6b401'}

def require(ok, msg):
    if not ok: raise ValueError(msg)

def coefficients(root):
    folder=root/'coefficients'
    binding=json.loads((folder/'BINDING.json').read_text())
    values={}
    for name in PORTS:
        rec=binding['payloads'][name]
        raw=gzip.decompress((folder/rec['file']).read_bytes())
        digest=hashlib.sha256(raw).hexdigest()
        require(digest==rec['raw_sha256']==EXPECTED_HASHES[name], 'fixed numeral digest: '+name)
        number=int.from_bytes(raw,'little')
        require(number.bit_length()==rec['bits'], 'bit length: '+name)
        require(len(raw)==rec['raw_bytes']==(number.bit_length()+7)//8, 'minimal numeral: '+name)
        values[name]=number
    recipe=folder/'recipe'
    require(hashlib.sha256((recipe/'k215.tm').read_bytes()).hexdigest()==
      'fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090',
      'literal machine digest')
    tiles=json.loads((recipe/'wang943_tiles.json').read_text())
    require(len(tiles)==943 and all(len(t)==4 for t in tiles), 'tile shape')
    # Independently encode the native tuple from the literal tile list.
    bit_weights=[1 << (10+2*j) for j in range(44)]
    rows={}
    for i,tile in enumerate(tiles):
        active=[10*side+j for side,label in enumerate(tile)
                for j in range(10) if (label+512)&(1<<j)]
        rows[i]=1+sum(bit_weights[j] for j in active+list(range(40,44)))
    for side,offset in enumerate((1020,1000,980,960)):
        for j in range(10): rows[offset+2*j]=bit_weights[10*side+j]
    for j,anchor in enumerate((1095,1096,2195,3296)):
        rows[anchor]=bit_weights[40+j]
    rows[1063]=rows[1064]=0
    require(len(rows)==989, 'native support')
    convolution=defaultdict(int)
    for e in (40,41,1100,2200): convolution[e]+=1
    for e,value in rows.items():
        convolution[4393-e]+=value
        convolution[5495-e]+=value
    d=121*8801
    B=1<<d
    beta=B-1
    K0=sum(value << (121*e) for e,value in convolution.items())+(B<<121)
    MC=beta-sum(1 << (121*e) for e in rows if e!=1)-(2 << (121*1063))
    mu=1022+sum(bit_weights)
    MF=4+(mu << (121*4393))+(mu << (121*5495))
    MF+=sum(1 << (121*(1000+2*j)) for j in range(10))
    MF+=sum(1 << (121*(1021+2*j)) for j in range(10))
    MF+=(1 << (121*2195))+(1 << (121*3296))
    MF+=sum(((1<<119)-1) << (121*e) for e in range(8792,8799))
    MF+=((1<<27)-1) << (121*8799)
    expected=dict(beta=beta,K0=K0,MC=MC,MF=MF+beta,
                  cone_A=1<<1113,cone_B=1<<666104)
    require(values==expected, 'full actual integer coefficient reconstruction')
    return values, {'complete_integer_reconstruction':True,
                    'fixed_digest_checks':len(PORTS),
                    'literal_machine_digest':True,
                    'tile_count':len(tiles),'native_support':len(rows)}

def optional_bounds(root, base):
    path=root/'equations/ROOT_BOUND_RECIPE.json'
    if not path.exists(): return {}, None
    recipe=json.loads(path.read_text())
    records=json.loads((root/'coefficients/DERIVED_BINDING.json').read_text())
    needed=set()
    def visit(i):
        if i in needed:return
        needed.add(i)
        n=recipe['nodes'][i]
        if n[0] in ('add','sub','mul'):visit(n[1]);visit(n[2])
    for i in recipe['outputs']:visit(i)
    bound={}; degree={}; support={}
    for i,node in enumerate(recipe['nodes']):
        if i not in needed:continue
        op=node[0]
        if op=='integer':bound[i]=abs(node[1]);degree[i]=0;support[i]=set()
        elif op=='coefficient':bound[i]=abs(base[node[1]]);degree[i]=0;support[i]=set()
        elif op=='variable':bound[i]=1;degree[i]=1;support[i]={node[1]}
        else:
            a,b=node[1:]
            bound[i]=bound[a]*bound[b] if op=='mul' else bound[a]+bound[b]
            degree[i]=degree[a]+degree[b] if op=='mul' else max(degree[a],degree[b])
            support[i]=support[a]|support[b]
    require([degree[i] for i in recipe['outputs']]==[14,18,34,44], 'root majorant degrees')
    require(not ({'n','T'} & set.union(*(support[i] for i in recipe['outputs']))),
            'noncircular root majorant support')
    values={}
    for j,i in enumerate(recipe['outputs']):
        name='root_bound_L'+str(j)
        rec=records[name]
        raw=gzip.decompress((root/'coefficients'/rec['file']).read_bytes())
        require(hashlib.sha256(raw).hexdigest()==rec['raw_sha256'], 'derived bound digest')
        L=int.from_bytes(raw,'little')
        exponent=(bound[i].bit_length()+1)//2
        require(L==1<<exponent and L*L>bound[i], 'exact dyadic square-root majorant')
        values[name]=L
    return values,{'exact_l1_majorants':True,'degrees':[14,18,34,44],
                   'independent_of':['n','T']}

class Fp:
    """Tiny field element, used only for independent finite diagnostics."""
    def __init__(self,value,p):self.value,self.p=value%p,p
    def coerce(self,x):return x if isinstance(x,Fp) else Fp(x,self.p)
    def __add__(self,x):return Fp(self.value+self.coerce(x).value,self.p)
    __radd__=__add__
    def __neg__(self):return Fp(-self.value,self.p)
    def __sub__(self,x):return self+(-self.coerce(x))
    def __rsub__(self,x):return self.coerce(x)+(-self)
    def __mul__(self,x):return Fp(self.value*self.coerce(x).value,self.p)
    __rmul__=__mul__
    def __pow__(self,n):return Fp(pow(self.value,n,self.p),self.p)

def independent_front(inputs, coefficients, prime):
    x={name:Fp(value,prime) for name,value in inputs.items()}
    p={name:Fp(value,prime) for name,value in coefficients.items()}
    J=1+6*x['j'];q=1+J*p['beta'];W=4*(3*x['w']+1)
    X=W*q;Y=q**3*(1+2*x['v']);a=(X+1)*Y;E=a-Y
    H=4*a+3;Delta=(a+1)*(a+3)
    C=x['C'];F=p['K0']*C+W*C-x['z']*q+x['z'];alpha=q-C-F
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(p['MC']+q*p['MF'])*J
    k=1+R+x['h']*E;c=x['c'];eta=c-Y*k;zeta=(Y+1)*k-c
    I=c*c*(1+2*x['r']);I2=I*I;Bstrong=Delta*I2
    F0=(a+2)*I;Df=F0*F0-I2+1;Q=(Delta*I)**2;delta=Q-1
    V=Df*c*x['T']-Df*R-c;Cy=(delta+1)*V*V-1;Aaux=delta*Cy
    ell0=X*Y*Y;L=ell0*k;Dtau=L*L+L*k+1;Dmain=1+Delta*c*c
    b0=a*c+X;U=p['cone_A']*F;Zc=p['cone_B']*C
    G=U*Zc-(U+Zc-q)**2;Peta=eta*zeta
    Pair=G*Peta-(G+Peta-1-x['t']**2)**2
    Ag=Pair-(1+x['p2']**2+x['p3']**2+x['p3'])
    return {name:value.value for name,value in locals().copy().items() if isinstance(value,Fp)}

def formal_conjugate_norm(center, radicands, prime):
    """Literal product in F_p[r_i]/(r_i^2-A_i), reverse conjugation order."""
    def multiply(left,right):
        out={}
        for m,v in left.items():
            for n,w in right.items():
                common=m&n
                coefficient=v*w
                while common:
                    bit=common&-common
                    coefficient*=radicands[bit.bit_length()-1]
                    common-=bit
                mask=m^n
                out[mask]=(out.get(mask,0)+coefficient)%prime
        return {m:v for m,v in out.items() if v}
    product={0:center%prime}
    for i in range(len(radicands)):product[1<<i]=prime-1
    for i in reversed(range(len(radicands))):
        conjugate={m:(-v if m&(1<<i) else v)%prime for m,v in product.items()}
        product=multiply(product,conjugate)
    require(all(m==0 for m in product), 'formal field norm elimination')
    return product.get(0,0)

def evaluate_dag(packet, inputs, ports, prime):
    values=[]
    for node in packet['nodes']:
        op=node[0]
        if op=='integer':v=node[1]
        elif op=='variable':v=inputs[node[1]]
        elif op=='coefficient':v=ports[node[1]]
        elif op=='add':v=values[node[1]]+values[node[2]]
        elif op=='sub':v=values[node[1]]-values[node[2]]
        elif op=='mul':v=values[node[1]]*values[node[2]]
        else:raise ValueError('unknown DAG operation')
        values.append(v%prime)
    return values

def audit_packet(packet, ports, trials=24):
    nodes=packet['nodes'];variables=packet['variables']
    used=set();counts=Counter()
    for i,node in enumerate(nodes):
        op=node[0]
        if op in ('add','sub','mul'):
            require(len(node)==3 and all(isinstance(j,int) and 0<=j<i for j in node[1:]), 'acyclic literal DAG')
            counts[op]+=1
        else:
            require(op in ('integer','coefficient','variable') and len(node)==2, 'DAG leaf')
            if op=='variable':used.add(node[1])
    live=set()
    def visit(i):
        if i in live:return
        live.add(i)
        if nodes[i][0] in ('add','sub','mul'):
            visit(nodes[i][1]);visit(nodes[i][2])
    visit(packet['output'])
    require(len(live)==len(nodes), 'no dead arithmetic registers')
    require(used==set(variables) and len(used)==packet['variable_count'], 'all variables live')
    require(dict(counts)==packet['operation_counts'] and sum(counts.values())==packet['operations'], 'literal binary operation counts')
    rng=random.Random(0xC0A5C)
    primes=(1000000007,1000000009,1000000033)
    passed=0;register_checks=0
    while passed<trials:
        prime=primes[passed%len(primes)]
        inputs={name:rng.randrange(-40,41) for name in variables}
        # Include c=0 explicitly: the auxiliary rational radicand is then 1.
        if passed==0:inputs['c']=0
        r=independent_front(inputs,ports,prime)
        if r['delta']==0:continue
        values=evaluate_dag(packet,inputs,ports,prime)
        for name,value in r.items():
            if name in packet['named_registers']:
                require(values[packet['named_registers'][name]]==value, 'front register '+packet['name']+':'+name)
                register_checks+=1
        d=r['delta'];dy=r['Cy']*pow(d,prime-2,prime)%prime;H2=r['H']**2%prime
        center=(r['H']*inputs['n']+r['b0'])%prime
        if packet['name']=='norm13_degree3744':
            support=('j','C','z','h','r','v','w','c','t','p2','p3')
            rho=1+sum(inputs[name]**2 for name in support)
            accumulated=1;weights=[1]
            for i,e in enumerate((4,5,9,11)):
                accumulated=accumulated*(1+ports['root_bound_L'+str(i)]*pow(rho,e,prime))%prime
                weights.append(r['H']*accumulated%prime)
            raw=[r['Dmain'],r['Df'],r['Dtau'],r['Ag'],r['Aaux']]
            radicands=[A*w*w%prime for A,w in zip(raw,weights)]
            expected=formal_conjugate_norm(center,radicands,prime)
        elif len(variables)==13:
            if '1392' in packet['name']:
                center=(center+r['H']*r['V'])%prime
            radicands=[r['Dmain'],H2*r['Df']%prime,H2*r['Dtau']%prime,
                       H2*r['Ag']%prime,H2*dy%prime]
            expected=pow(d,16,prime)*formal_conjugate_norm(center,radicands,prime)%prime
        elif len(variables)==14:
            if '696' in packet['name']:
                center=(r['H']*(inputs['n']+2*r['V']+2*r['L']+r['k']+2*r['F0'])+2*r['b0'])%prime
                radicands=[4*r['Dmain']%prime,4*H2*r['Dtau']%prime,
                           4*H2*r['Df']%prime,4*H2*dy%prime]
            else:
                radicands=[r['Dmain'],H2*r['Dtau']%prime,H2*r['Df']%prime,H2*dy%prime]
            N=pow(d,8,prime)*formal_conjugate_norm(center,radicands,prime)%prime
            S=(r['Ag']-inputs['p1']**2)**2%prime
            expected=((1+N)*(1+S)-1)%prime
        elif len(variables)==15:
            center=(inputs['n']+2*r['V']+2*r['L']+r['k']+2*r['F0'])%prime
            radicands=[4*r['Dtau']%prime,4*r['Df']%prime,4*dy%prime]
            N=pow(d,4,prime)*formal_conjugate_norm(center,radicands,prime)%prime
            main=(r['b0']+inputs['gamma']*r['H'])**2-r['Dmain']
            S=(main**2+(r['Ag']-inputs['p1']**2)**2)%prime
            expected=((1+N)*(1+S)-1)%prime
        else:raise ValueError('unexpected frontier equation')
        require(values[packet['output']]==expected, 'independent formal-product diagnostic '+packet['name'])
        passed+=1
    return {'name':packet['name'],'variables':len(variables),'operations':sum(counts.values()),
            'finite_modular_diagnostics':passed,'primes':list(primes),
            'independent_front_register_checks':register_checks,
            'includes_c_zero':True,'exact_topology_liveness_and_counts':True}

def local_identities():
    names=['q','F','C','z','K0','W','MC','MF','J','a','c','r','ell','k','y','V','delta','G','Z','t','p1','p2','p3','B']
    ring=Ring(names);v={name:ring.var(name) for name in names}
    q,C,z,K0,W,MC,MF,J=[v[n] for n in ('q','C','z','K0','W','MC','MF','J')]
    F=(K0+W)*C-z*(q-1);alpha=q-F-C
    checks={}
    checks['transport']=(K0+W)*C-F-z*(q-1)
    checks['R_rewrite']=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J-((q*(q-F)-C)*(q*q-1)+(MC+q*MF)*J)
    a,c,r=[v[n] for n in ('a','c','r')];Delta=(a+1)*(a+3)
    I=(2*r+1)*c*c;Df=1+Delta*I*I;F0=(a+2)*I
    checks['strong_center']=Df-(F0*F0-I*I+1)
    checks['normalized_strong']=(Delta*I)**2-Delta*(Df-1)
    ell,k=v['ell'],v['k'];L=ell*k
    checks['first_center']=ell*(ell+1)*k*k+1-(L*L+L*k+1)
    d,y,V=v['delta'],v['y'],v['V'];Cy=(d+1)*V*V-1
    checks['auxiliary_clearing']=(d*y)**2-d*Cy-d*(d*y*y-Cy)
    checks['auxiliary_pell']=(d+1)*V*V-d*y*y-1+(d*y*y-Cy)
    G,Z,t,p1,p2,p3=[v[n] for n in ('G','Z','t','p1','p2','p3')]
    Pair=G*Z-(t*t-G-Z+1)**2;Ag=Pair-1-p2*p2-p3*(p3+1)
    checks['joint_guard']=Ag-p1*p1-(Pair-(1+p1*p1+p2*p2+p3*(p3+1)))
    B=v['B']
    checks['auxiliary_shear']=(B+y)**2-(B-c)**2-(c+y)*(2*B+y-c)
    require(all(not p.terms for p in checks.values()), 'exact local polynomial identities')
    return list(checks)

def cleared_three(x,A,B,Cn,d):
    J=d*(x*x-A-B)-Cn
    T=d*d*A*B;R=d*Cn
    K=J*J-4*(T+R*(A+B))
    return K*K-64*T*R*x*x

def independent_norm_coefficients(k):
    # Reuse only the formal square-root polynomial ring from audit.py, not
    # any optimized norm function or builder.  Form the defining product.
    from audit import Poly
    product=Poly.variable(0)
    for j in range(k):product=product-Poly.radical(j)
    for j in reversed(range(k)):product=product*product.conjugate(j)
    require(all(m[-1]==0 for m in product.terms), 'exact formal radical elimination')
    return {m[:k+1]:c for m,c in product.terms.items()}

def cleared_four(x,Dm,A,B,Cn,d):
    q0=d*(x*x+Dm-A-B)-Cn;q1=-2*d*x
    T=d*d*A*B;R=d*Cn
    t0=q0*q0+Dm*q1*q1-4*(T+R*(A+B));t1=2*q0*q1
    f0=t0*t0+Dm*t1*t1-64*T*R*(x*x+Dm)
    f1=2*t0*t1+128*T*R*x
    return f0*f0-Dm*f1*f1

def exact_generic_clearing():
    results={}
    from five_square_norm import cleared_norm5
    for count,function in ((3,cleared_three),(4,cleared_four),(5,cleared_norm5)):
        names=['x']+['a'+str(i) for i in range(count-1)]+['cn','delta']
        ring=Ring(names)
        actual=function(*(ring.var(n) for n in names))
        original=independent_norm_coefficients(count)
        exponent=2**(count-1)
        expected={tuple(m[:-1])+(m[-1],exponent-m[-1]):c for m,c in original.items()}
        require(actual.terms==expected, 'exact generic cleared norm '+str(count))
        results[str(count)]={'conjugates':2**count,'monomials':len(expected),
                            'clearing_exponent':exponent}
    return results

def sheared_degree_certificate():
    names=['n','H','b0','V','Dm','Df','Dt','Ag','delta']
    ring=Ring(names)
    n,H,b0,V,Dm,Df,Dt,Ag,d=[ring.var(s) for s in names]
    center=H*(n+V)+b0
    A=H*H*Df;B=H*H*Dt;e=H*H*Ag;Cn=H*H*((d+1)*V*V-1)
    # Four components mean 1, sqrt(Dm), sqrt(e), sqrt(Dm*e).
    J=[d*(center*center+Dm+e-A-B)-Cn,2*d*center,2*d*center,2*d]
    def multiply(left,right):
        out=[ring.scalar(0) for _ in range(4)]
        for i in range(4):
            for j in range(4):
                term=left[i]*right[j]
                if i&j&1:term=term*Dm
                if i&j&2:term=term*e
                out[i^j]=out[i^j]+term
        return out
    K=multiply(J,J)
    K[0]=K[0]-4*(d*d*A*B+d*Cn*(A+B))
    x2=[center*center+Dm+e,2*center,2*center,ring.scalar(2)]
    f=multiply(K,K)
    f=[v-64*d**3*A*B*Cn*x2[i] for i,v in enumerate(f)]
    weights=[1,6,7,23,14,18,34,44,30];offsets=[0,7,28,35]
    degrees=[[p.weighted_degree(weights)+offsets[i] for i,p in enumerate(parts)]
             for parts in (J,K,f)]
    require(degrees==[[86,66,87,65],[174,152,173,153],[348,326,347,327]],
            'sheared exact biquadratic component degrees')
    require(f[0].homogeneous(weights,348)=={(0,8,0,4,0,0,0,2,4):16},
            'sheared complete leading scalar')
    # Its leading term is scalar. All other components have smaller weighted
    # degree, so each of the last two conjugate norms squares this top part.
    lead=Ring(['j','w','v','h','r','c','z','C','beta'])
    j,w,v,h,r,c,z,C,beta=[lead.var(s) for s in lead.names]
    q0=6*beta*j;a0=24*w*v*q0**4;i0=2*r
    R0=q0**4*z-12*q0**3*w*C;eta0=-48*h*w*v*v*q0**7
    top=2**80*a0**128*i0**64*c**128*R0**16*eta0**32
    monomial=(800,160,192,32,64,128,16,0,800)
    require(top.terms.get(monomial)==2**1456*3**960, 'sheared selected nonzero coefficient')
    require(top.weighted_degree((1,1,1,1,1,1,1,1,0))==1392,
            'sheared exact degree')
    return {'degree':1392,'component_degrees':degrees,
            'cleared_F8_top':'16*H^8*V^4*Ag^2*delta^4',
            'full_norm_top':'2^80*a0^128*i0^64*c^128*R0^16*eta0^32',
            'selected_monomial':'j^800*w^160*v^192*h^32*r^64*c^128*z^16',
            'selected_coefficient':'2^1456*3^960*beta^800',
            'front_leading_monomials':len(top.terms)}

def centered_four_degree_certificate(cut):
    # H^8 times the exactly expanded centered F8 cut, with its free n
    # replaced by n+2*b0/H+2*sqrt(Dmain)/H, is an integral quadratic-
    # extension polynomial. Every exponent of n is at most 8, so the
    # indicated H^8 clears this substitution term by term. The substituted
    # free expression has weight 1; thus all 1,854 cut terms have weight
    # at most 304 after adding 8*deg(H)=48. The degree-304 term is the
    # image of the already checked unique degree-256 homogeneous term.
    require(max(m[0] for m in cut.terms)<=8, 'centered F8 carrier exponent')
    ring=Ring(['a','c','n'])
    a,c,n=[ring.var(s) for s in ring.names]
    H=4*a;b0=a*c;Dm=a*a*c*c
    require(not ((H*n+2*b0)**2-4*Dm-H*H*n*(n+c)).terms,
            'centered four-root leading main conjugate cancellation')
    lead=Ring(['j','w','v','h','r','c','z','C','n','beta'])
    j,w,v,h,r,c,z,C,n,beta=[lead.var(s) for s in lead.names]
    q0=6*beta*j;X0=12*w*q0;Y0=2*v*q0**3
    a0=X0*Y0;i0=2*r;R0=q0**4*z-12*q0**3*w*C
    Q0=a0**4*i0**2*c**4;H0=4*a0
    V0=-a0**2*i0**2*c**4*R0
    L0=h*X0**2*Y0**3;F0=a0*i0*c*c;eta0=-h*X0*Y0**2
    norm_top=2**28*Q0**8*H0**16*V0**8*L0**4*F0**2*n*(n+c)
    require(norm_top.weighted_degree((1,1,1,1,1,1,1,1,1,0))==608,
            'centered four-root norm degree')
    final_top=norm_top*eta0**8
    monomial=(396,82,94,12,34,68,8,0,2,396)
    require(final_top.terms.get(monomial)==2**748*3**478,
            'centered four-root selected nonzero coefficient')
    require(final_top.weighted_degree((1,1,1,1,1,1,1,1,1,0))==696,
            'centered four-root final degree')
    return {'norm_degree':608,'final_degree':696,'final_guard_degree':88,
            'cleared_F8_degree_before_last_conjugation':304,
            'norm_leading_form':'2^28*Q0^8*H0^16*V0^8*L0^4*F0^2*n*(n+c)',
            'selected_monomial':'j^396*w^82*v^94*h^12*r^34*c^68*z^8*n^2',
            'selected_coefficient':'2^748*3^478*beta^396',
            'front_leading_monomials':len(final_top.terms)}

def degree_certificates():
    # Full exact formal cut verifies all cancellations in the centered F8.
    ring=Ring(['n','L','k','F0','I','V','delta'])
    n,L,k,F0,I,V,d=[ring.var(s) for s in ring.names]
    x=n+2*V+2*L+k+2*F0
    N=cleared_three(x,4*(L*L+L*k+1),4*(F0*F0-I*I+1),4*((d+1)*V*V-1),d)
    weights=(1,17,7,9,3,23,30)
    require(N.weighted_degree(weights)==256, '15-variable formal cut degree')
    expected={(1,2,0,1,0,4,4):1<<14}
    require(N.homogeneous(weights,256)==expected, '15-variable complete leading form')
    # Use the independently checked integer coefficient dictionary for F32.
    original=json.loads((HERE/'five_square_norm_expanded.json').read_text())
    terms={tuple(m[:5]+[m[5],16-m[5]]):coefficient for m,coefficient in original['terms']}
    weights13=(7,14,30,46,56,88,30)
    top=max(sum(a*b for a,b in zip(m,weights13)) for m in terms)
    leaders={m:c for m,c in terms.items() if sum(a*b for a,b in zip(m,weights13))==top}
    require(top==1408 and leaders=={(0,0,0,0,0,16,0):1}, '13-variable unique cleared-norm leading term')
    # Direct leading-front cut: all symbols are independent, beta has weight 0.
    lead=Ring(['j','w','v','r','c','z','C','beta'])
    j,w,v,r,c,z,C,beta=[lead.var(s) for s in lead.names]
    q0=6*beta*j;a0=24*w*v*q0**4;i0=2*r
    R0=q0**4*z-12*q0**3*w*C
    cn_top=16*a0**10*i0**6*c**12*R0**2
    require(cn_top.weighted_degree((1,1,1,1,1,1,1,0))==88, 'auxiliary numerator top degree')
    top13=cn_top**16
    monomial=(768,160,160,96,192,32,0,768)
    require(top13.terms.get(monomial)==2**1408*3**928, '13-variable selected nonzero coefficient')
    norm4=independent_norm_coefficients(4)
    cleared4={tuple(m[:-1])+(m[-1],8-m[-1]):c for m,c in norm4.items()}
    weights14=(7,14,46,30,88,30)
    max14=max(sum(a*b for a,b in zip(m,weights14)) for m in cleared4)
    lead14={m:c for m,c in cleared4.items() if sum(a*b for a,b in zip(m,weights14))==max14}
    require(max14==704 and lead14=={(0,0,0,0,8,0):1},
            '14-variable unique cleared-norm leading term')
    return {'norm15':{'formal_monomials':len(N.terms),'weights':list(weights),
                     'degree':256,'leading_form':'2^14*n*F0*L^2*V^4*delta^4',
                     'final_guard_degree':88,'final_degree':344},
            'norm14':{'unique_norm_leading_term':'(H^2*Cy)^8','norm_degree':704,
                      'final_guard_degree':88,'final_degree':792},
            'norm14_centered':centered_four_degree_certificate(N),
            'norm13':{'unique_norm_leading_term':'(H^2*Cy)^16','degree':1408,
                      'front_leading_monomials':len(top13.terms),
                      'selected_monomial':'j^768*w^160*v^160*r^96*c^192*z^32',
                      'selected_coefficient':'2^1408*3^928*beta^768'},
            'norm13_sheared':sheared_degree_certificate()}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root',type=Path,default=HERE.parent)
    parser.add_argument('--output',type=Path,default=HERE/'INTEGRATED_AUDIT.json')
    args=parser.parse_args();start=time.monotonic();root=args.root.resolve()
    base,coefficient_receipt=coefficients(root)
    derived,bound_receipt=optional_bounds(root,base)
    ports={**base,**derived}
    packets=[json.loads(path.read_text()) for path in sorted((root/'equations').glob('norm*.json'))]
    # The CRT carrier has its own independent front end in check_crt.py.
    # verify_release.py runs both families as one read-only release audit.
    packets=[packet for packet in packets if not packet.get('crt_carrier')]
    require(packets, 'no equation packets found')
    results=[audit_packet(packet,ports) for packet in packets]
    receipt={'status':'PASS','coefficient_checks':coefficient_receipt,
             'optional_weighted_root_bounds':bound_receipt,
             'exact_local_identities':local_identities(),
             'exact_generic_cleared_norms':exact_generic_clearing(),
             'exact_degree_certificates':degree_certificates(),
             'equations':results,
             'scope':'Base-family exact arithmetic audit. Run verify_release.py for all six norms, including the separately audited CRT carrier. This is not a formal proof of the inherited number-theoretic kernel.',
             'seconds':round(time.monotonic()-start,3)}
    args.output.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
