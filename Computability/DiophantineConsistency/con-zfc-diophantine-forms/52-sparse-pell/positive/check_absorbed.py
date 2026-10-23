"""Independent full-polynomial, radical-product, binding and bound diagnostics."""
import hashlib, gzip, json, math, random
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent
VARIABLES=['J','F','alpha','z','i','T','s','w','eta','zeta','t']
PORTS=['beta','K0','MC','MF']
rng=random.Random(719583)

def evaluate(obj,values,p):
    vals=values.copy()
    for name,op,a,b in obj['source']:
        a=vals[a] if isinstance(a,str) else a
        b=vals[b] if isinstance(b,str) else b
        vals[name]=(a+b if op=='+' else a-b if op=='-' else a*b)%p
    return vals

def norm_direct(values,carrier,modulus,p):
    J,F,alpha,z,i,T,s,w,eta,zeta,t=[values[x] for x in VARIABLES]
    beta,K0,MC,MF=[values[x] for x in PORTS]
    q=beta*J+1; X=w*q; Y=(s if modulus=='none' else s+3*q)*q**3; E=X*Y; k=eta+zeta
    c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H; ell=E*k*Y
    A=1+ell*(ell+k); G=1+Delta*c*c; b0=X+a*c
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    I=i*c*c; D=1+Delta*I*I; Q=(Delta*I)**2; d=Q-1; v=c*T; b=c+R*D
    e=Q*(D*v*v+b*b)-1; Ba=2*Q*v*b
    K=I*T+(carrier!='lean')
    delta=ell if carrier=='lean' else a*c-ell+(2*c if carrier=='full' else 0)
    if modulus=='none':
        S=H;L=1+H*K;W=b0+H*(t+b+delta)
    else:
        B=Y if modulus=='Y' else E; S=B*H; L=B*(1+H*K)
        W=B*b0+H*(B*(t+b+delta)+k-R-1)
    rad=[A%p,G%p,D%p]
    def scalar(x): return [x%p]+[0]*7
    def multiply(x,y):
        out=[0]*8
        for l in range(8):
            for r in range(8):
                term=x[l]*y[r]
                for bit in range(3):
                    if l&r&(1<<bit): term*=rad[bit]
                out[l^r]=(out[l^r]+term)%p
        return out
    total=scalar(1)
    for sg in [-1,1]:
        for sa in [-1,1]:
            for sf in [-1,1]:
                x=scalar(W);x[1]=-S*sa%p;x[2]=-L*sg%p
                f=[d*r%p for r in multiply(x,x)]
                f[0]=(f[0]-S*S*e)%p;f[4]=(f[4]+sf*S*S*Ba)%p
                total=multiply(total,f)
    if any(total[1:]): raise AssertionError('Formal radical coefficient survived')
    return total[0]

def polynomial_degree(obj,coefficients,seed,p):
    rr=random.Random(seed)
    values={x:np.array([rr.randrange(1,30),rr.randrange(1,30)],dtype=np.int64) for x in obj['witnesses']}
    values.update({x:np.array([coefficients[x]%p],dtype=np.int64) for x in PORTS})
    def trim(x):
        x=x%p; nz=np.flatnonzero(x)
        return x[:int(nz[-1])+1] if len(nz) else np.array([0],dtype=np.int64)
    for name,op,a,b in obj['source']:
        a=values[a] if isinstance(a,str) else np.array([a],dtype=np.int64)
        b=values[b] if isinstance(b,str) else np.array([b],dtype=np.int64)
        if op=='*': out=np.convolve(a,b)
        else:
            out=np.zeros(max(len(a),len(b)),dtype=np.int64)
            out[:len(a)]+=a;out[:len(b)]+=b if op=='+' else -b
        values[name]=trim(out)
    out=values[obj['output']]
    if len(out)-1!=obj['exact_degree']: raise AssertionError(('degree',len(out)-1,obj['exact_degree']))
    return {'degree':len(out)-1,'leading_residue':int(out[-1]),'prime':p,'seed':seed}

def main():
    binding=json.loads((ROOT/'COEFFICIENT_BINDING.json').read_text())
    coeff={};payloads=[]
    for rec in binding['ports']:
        raw=(ROOT/rec['file']).read_bytes();zipped=(ROOT/rec['gzip_file']).read_bytes()
        if hashlib.sha256(raw).hexdigest()!=rec['sha256']: raise AssertionError('raw payload hash')
        if hashlib.sha256(zipped).hexdigest()!=rec['gzip_sha256']: raise AssertionError('gzip payload hash')
        if gzip.decompress(zipped)!=raw: raise AssertionError('gzip contents')
        alias=next(k for k,v in binding['port_aliases'].items() if v==rec['port'])
        coeff[alias]=int.from_bytes(raw,'little');payloads.append({'port':alias,'sha256':rec['sha256']})
    degree=[];products=0;guards=0;structure=[]
    for path in sorted(ROOT.glob('positive*_*_product.json')):
        obj=json.loads(path.read_text());seen=set(obj['witnesses']+PORTS)
        for name,op,a,b in obj['source']:
            if name in seen or op not in ['+','-','*']: raise AssertionError('malformed DAG')
            if any(isinstance(v,str) and v not in seen for v in [a,b]): raise AssertionError('forward reference')
            seen.add(name)
        if len(obj['source'])!=obj['operations']:raise AssertionError('wrong operation count')
        structure.append({'file':path.name,'operations':obj['operations']})
        for trial in range(120):
            vals={x:rng.randrange(-8,9) for x in obj['witnesses']+PORTS};p=1000003
            ev=evaluate(obj,vals,p);n=norm_direct(vals,obj['carrier'],obj['absorption_modulus'],p)
            if ev['N']!=n: raise AssertionError('radical norm mismatch')
            if ev[obj['output']]!=(ev.get('Nk',1)*ev['Nt']*(1+n)-1)%p:raise AssertionError('finalizer mismatch')
            products+=1
            ev4=evaluate(obj,vals,4)
            if ev4['N'] not in [0,1]:raise AssertionError('mod-four norm guard')
            guards+=1
        for p,seed in [(p,s) for p in [1000003,1000033,1000037] for s in [7,23,71]]:
            degree.append({'file':path.name,'fixed_tuple':True,**polynomial_degree(obj,coeff,seed,p)})
    shifted_checks=0
    for arity,modulus in [(11,'Y'),(12,'none')]:
        base=json.loads((ROOT/f'positive{arity}_{modulus}_lean_system.json').read_text())
        shifted=json.loads((ROOT/f'positive{arity}_{modulus}_lean_shifted_system.json').read_text())
        for trial in range(60):
            vals={x:rng.randrange(2,101) for x in base['witnesses']+PORTS}
            newer=vals.copy();newer['z']-=1
            a=evaluate(base,vals,1000003);b=evaluate(shifted,newer,1000003)
            if (a['Nt']-1)%1000003!=(b['transport']-b['transport_right'])%1000003:raise AssertionError('transport shift')
            if (a['norm_left'],a['norm_right'])!=(b['norm_left'],b['norm_right']):raise AssertionError('shift changed norm')
            shifted_checks+=1
    bounds=0
    for q in [16,17,31,256]:
        for w in [1,2,1000,10**20]:
            for s in [1,2,200]:
                X=w*q;Y=(s+3*q)*q**3;E=X*Y;R=q**4-3
                for eta,zeta in [(1,1),(1,99),(10**20,1)]:
                    k=eta+zeta;c=k*Y+eta;a=E+Y;H=4*a+3;Delta=a*a+H;ell=E*k*Y
                    A=1+ell*(ell+k);G=1+Delta*c*c;b0=X+a*c
                    for i in [1,2,10**10]:
                        I=i*c*c;D=1+Delta*I*I;Q=(Delta*I)**2;d=Q-1;b=c+R*D
                        ceilf=math.isqrt(D)+1
                        if not (b+c*ceilf)*8*E*c<d*I:raise AssertionError('no-h separator bound')
                        if not b0+math.isqrt(G)>k*H:raise AssertionError('lean carrier bound')
                        if not 9*A>(3*ell+k)**2:raise AssertionError('tau gap bound')
                        if not 0<A*(A-1)<Q:raise AssertionError('modulus exceptional bound')
                        if math.gcd(Y,H)>3:raise AssertionError('small gcd')
                        bounds+=1
    result={'all_pass':True,'payloads':payloads,'structure':structure,'full_univariate_replays':degree,
        'independent_formal_radical_products':products,'mod_four_guards':guards,'positive_transport_shift_identities':shifted_checks,'no_index_equation_bound_cases':bounds,
        'scope':'Finite arithmetic diagnostics corroborate the supplied proof; they do not certify inherited compiler semantics.'}
    (ROOT/'CHECK_RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
