if not __debug__: raise SystemExit('Optimized Python is not permitted: assertions are audit checks.')
"""Independently authored audit. Circuit files are inert JSON; no emitter imported/run."""
from pathlib import Path
import json, hashlib, random, math
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent
RNG=random.Random(472281051)

def interpret(c,inputs,mod=None):
    env=dict(inputs)
    for name,op,left,right in c['source']:
        left=env[left] if isinstance(left,str) else left
        right=env[right] if isinstance(right,str) else right
        value=left+right if op=='+' else left-right if op=='-' else left*right
        env[name]=value if mod is None else value%mod
    return env

def check_structure(c):
    known=set(c['witnesses'])|set(c['fixed_numerals'])
    assert len(c['witnesses'])==len(set(c['witnesses']))
    for name,op,l,r in c['source']:
        assert name not in known and op in '+-*'
        assert all(type(x)==int or x in known for x in (l,r))
        known.add(name)
    live={c['output']} if 'output' in c else {x for pair in c.get('comparisons',c.get('outputs')) for x in pair if isinstance(x,str)}
    for name,op,l,r in reversed(c['source']):
        if name in live:live.update(x for x in (l,r) if isinstance(x,str))
    assert set(known)<=live
    ops=len(c['source']); mul=sum(op=='*' for _,op,_,_ in c['source'])
    assert c['ledger']=={'operations':ops,'multiplications':mul,'additions_subtractions':ops-mul}
    return ops,mul,ops-mul

# Algebra Q[sqrt(A),sqrt(G)] represented as nested quadratic pairs.
def algmul(a,b,A,G,p):
    def pm(x,y):return ((x[0]*y[0]+A*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
    x,y=pm(a[:2],b[:2]),pm(a[2:],b[2:]);z,w=pm(a[:2],b[2:]),pm(a[2:],b[:2])
    return [(x[0]+G*y[0])%p,(x[1]+G*y[1])%p,(z[0]+w[0])%p,(z[1]+w[1])%p]
def determinant(matrix,p):
    a=[row[:] for row in matrix];ans=1
    for col in range(len(a)):
        pivot=next((r for r in range(col,len(a)) if a[r][col]%p),None)
        if pivot is None:return 0
        if pivot!=col:a[pivot],a[col]=a[col],a[pivot];ans=-ans
        lead=a[col][col]%p;ans=ans*lead%p;iv=pow(lead,-1,p)
        for r in range(col+1,len(a)):
            scale=a[r][col]*iv%p
            for s in range(col+1,len(a)):a[r][s]=(a[r][s]-scale*a[col][s])%p
    return ans%p

def detnorm(value,A,G,p):
    cols=[algmul(value,[int(j==k) for j in range(4)],A,G,p) for k in range(4)]
    return determinant([[cols[j][i] for j in range(4)] for i in range(4)],p)

def source_values(c,inputs):
    # Reconstruct input substitutions independently; do not trust internal gate values.
    if c.get('domain')=='strictly positive integers':return dict(inputs)
    v=dict(inputs)
    for port in c['positive_ports']:
        aa,bb,cc=(inputs[port+'_positive_'+suffix] for suffix in 'abc')
        v[port]=1+aa*aa+bb*bb+cc*(cc+1)
    v.update(i=2*inputs['i_integer']+1,s=2*inputs['s_integer']+1,w=inputs['w_integer']**2)
    if 'Jrep' in v:
        v['J']=v['Jrep'];v['z']=v['transport_quotient'];v['T']=v['auxiliary_quotient'];v['beta']=v['Bm1'];v['K0']=v['Kconstant']
    return v

def direct(c,inputs,p):
    v=source_values(c,inputs)
    J,F,al,z,h,i,T,s,w,et,ze,t=[v[x] for x in ['J','F','alpha','z','h','i','T','s','w','eta','zeta','t']]
    q=v['beta']*J+1;X=w*q;Y=s*q**3;E=X*Y;k=et+ze;cc=k*Y+et;a=E+Y;H=4*a+3;De=a*a+H
    ell=E*k*Y;A=1+ell*(ell+k);G=1+De*cc*cc;b0=X+a*cc
    R=((q-1)*(q-F)+al)*(q*q-1)+(v['MC']+q*v['MF'])*J
    Nk=k-h*E-R;Nt=(v['K0']+w)*(q-F-al)+q-F-z*(q-1)
    nv=len(c['witnesses']);I=i*cc*cc;D=1+De*I*I;Q=De*De*I*I;d=Q-1;vv=cc*T;b=cc+R*D;e=Q*(D*vv*vv+b*b)-1;B=2*Q*vv*b
    if nv==12:
        M=k*(I*I+T*T);L=H*M+1;W=b0+H*t
        # Evaluate inner F_H in Q[g]/(g²-G), then take its 2x2 determinant.
        def pm(x,y):return ((x[0]*y[0]+G*x[1]*y[1])%p,(x[0]*y[1]+x[1]*y[0])%p)
        z2=pm((W,-L),(W,-L));C=((d*(z2[0]+H*H*M*M*A)-H*H*e)%p,d*z2[1]%p)
        C2=pm(C,C);Ut=((C2[0]+H**4*D*B*B-4*d*d*H*H*M*M*A*z2[0])%p,(C2[1]-4*d*d*H*H*M*M*A*z2[1])%p)
        Ft=pm(Ut,Ut);Ft=((Ft[0]-4*H**4*D*B*B*C2[0])%p,(Ft[1]-4*H**4*D*B*B*C2[1])%p)
        norm=(Ft[0]*Ft[0]-G*Ft[1]*Ft[1])%p
        return (Nk*Nt*(1+norm)-1)%p,norm
    Nmain=(b0+H*v['gamma'])**2-De*cc*cc if nv>24 else None
    if nv==24:
        W=vv*vv+D+2*b;P=H*W;K=P+1
        multiplier=c.get('weight_multiplier',3)
        # Read the single literal multiplier only to permit audit of named variants.
        for name,op,l,r in c['source']:
            if name=='u':
                assert op=='*' and isinstance(l,int);multiplier=l
        u=multiplier*P;Z=H*t+K*b0
        lin=[Z,-u,-K,0];z2=algmul(lin,lin,A,G,p)
        C=[d*x%p for x in z2];C[0]=(C[0]-H*H*e)%p
        value=algmul(C,C,A,G,p);value[0]=(value[0]-H**4*B*B*D)%p
        norm=detnorm(value,A,G,p)
        return (Nk*Nt*(1+norm)-1)%p,norm
    if nv==25:
        M=I*I+T*T;C=d*(t*t+M*M*A)-e
        aa=C*C+B*B*D-4*d*d*t*t*M*M*A;bb=2*C*B
        norm=(aa*aa-D*bb*bb)%p
        return (Nmain*Nk*Nt*(1+norm)-1)%p,norm
    assert nv==26
    f=v['f'];Q=De*(f*f-1);d=Q-1;V=cc*(T*f-1)-R*f*f;e=Q*V*V-1
    norm=((d*(t*t+A)-e)**2-4*d*d*t*t*A)%p
    Ns=1+I*I-De*(f*f-1) if c.get('ordinary_strong') else f*f-De*I*I
    return (Nmain*Nk*Nt*Ns*(1+norm)-1)%p,norm

def ptr(a):
    while len(a)>1 and not a[-1]:a.pop()
    return a

def padd(a,b,p,sgn):
    z=[0]*max(len(a),len(b))
    for j,v in enumerate(a):z[j]=v
    for j,v in enumerate(b):z[j]=(z[j]+sgn*v)%p
    return ptr(z)

def pmul(a,b,p):
    # Carry-free integer convolution; limb width is proved sufficient per product.
    bits=(min(len(a),len(b))*(p-1)**2).bit_length()+1
    width=(bits+7)//8;size=len(a)+len(b)-1
    x=int.from_bytes(b''.join(v.to_bytes(width,'little') for v in a),'little')
    y=int.from_bytes(b''.join(v.to_bytes(width,'little') for v in b),'little')
    raw=(x*y).to_bytes(size*width,'little')
    return ptr([int.from_bytes(raw[j*width:(j+1)*width],'little')%p for j in range(size)])

def line_degree(c,p,seed):
    rr=random.Random(seed);env={v:[rr.randrange(p),rr.randrange(1,p)] for v in c['witnesses']}
    env.update({v:[rr.randrange(2,20)] for v in c['fixed_numerals']})
    for name,op,l,r in c['source']:
        l=env[l] if isinstance(l,str) else [l%p];r=env[r] if isinstance(r,str) else [r%p]
        env[name]=pmul(l,r,p) if op=='*' else padd(l,r,p,1 if op=='+' else -1)
    names=[c['output']] if 'output' in c else [p[0] for p in c.get('comparisons',c.get('outputs'))]
    return [{'register':x,'degree':len(env[x])-1,'leading_coefficient_mod_p':env[x][-1]} for x in names]

def run():
    paths=sorted((ROOT/'positive').glob('positive12_*.json'))+sorted((ROOT/'integers').glob('integer*_degree*.json'))
    results=[]
    for path in paths:
        c=json.loads(path.read_text());ledger=check_structure(c)
        for n in range(250):
            inputs={v:RNG.randrange(-4,5) for v in c['witnesses']}
            inputs.update({v:RNG.randrange(2,17) for v in c['fixed_numerals']})
            env=interpret(c,inputs,1000003);expected,norm=direct(c,inputs,1000003)
            if 'output' in c:assert env[c['output']]==expected,(path,n)
            else:
                nr='N' if len(c['witnesses'])==12 else 'Norm' if len(c['witnesses'])==24 else 'norm13' if len(c['witnesses'])==25 else 'res'
                assert env[nr]==norm,(path,n)
            # Distinct small-modulus check covers every sign and zero boundary.
            en4=interpret(c,inputs,4);nname='N' if len(c['witnesses'])==12 else 'Norm' if len(c['witnesses'])==24 else 'norm13' if len(c['witnesses'])==25 else 'res'
            assert en4[nname] in [0,1]
        degrees=[{'prime':p,'specialization':line_degree(c,p,9281+j)} for j,p in enumerate([65521,65519])]
        target=c.get('exact_degrees',[c.get('exact_degree')])
        if 'outputs' in c:
            expected_degrees={24:[12,4,2224],25:[32,12,4,872],26:[32,12,4,38,128]}
            target=expected_degrees[len(c['witnesses'])]
            reference_name={24:'integer24_sharp_pair_norm165_degree2240.json',25:'integer25_small_weight131_degree920.json',26:'integer26_ordinary_two_root123_degree214.json'}[len(c['witnesses'])]
            reference=json.loads((ROOT/'integers'/reference_name).read_text())
            mapping={row[0]:row for row in reference['source']}
            assert all(row==mapping[row[0]] for row in c['source'])
            assert c['witnesses']==reference['witnesses'] and c['fixed_numerals']==reference['fixed_numerals']
        for test in degrees:assert [r['degree'] for r in test['specialization']]==target,(path,test,target)
        results.append({'file':str(path.relative_to(ROOT)),'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'variables':len(c['witnesses']),'ledger':{'operations':ledger[0],'multiplications':ledger[1],'additions_subtractions':ledger[2]},'all_gates_and_ports_live':True,'independent_formula_evaluations':250,'square_mod4_evaluations':250,'degree_lower_bound_diagnostics':degrees})
        print(path.name,'PASS',flush=True)
    report={'status':'PASS','scope':'New independent JSON interpretation, quotient-algebra determinant norms, DAG/liveness and finite-field degree diagnostics. Not kernel certification or an unbounded compiler proof. Uniform upper bounds and exact-degree proofs are in companion notes.','circuits':results}
    (HERE/'pell_independent_checks.json').write_text(json.dumps(report,indent=2)+'\n')
if __name__=='__main__':run()
