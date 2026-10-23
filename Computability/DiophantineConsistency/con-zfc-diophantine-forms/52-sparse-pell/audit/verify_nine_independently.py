#!/usr/bin/env python3
"""Independent finite audit; imports no builders or supplied executable code.
Checks target isolation, primary-versus-direct formula modular evaluation,
full domain translations, and exact leading terms in cancellation-resolved DAGs.
"""
from pathlib import Path
from collections import defaultdict, Counter
from itertools import combinations_with_replacement, product
from math import isqrt
import ast, gzip, hashlib, json, random
ROOT=Path(__file__).resolve().parents[1]


def scalar_expr(expr, env):
    def go(n):
        if isinstance(n,ast.Constant) and type(n.value) is int:return n.value
        if isinstance(n,ast.Name):return env[n.id]
        if isinstance(n,ast.UnaryOp) and isinstance(n.op,ast.USub):return -go(n.operand)
        if isinstance(n,ast.BinOp):
            a,b=go(n.left),go(n.right)
            if isinstance(n.op,ast.Add):return a+b
            if isinstance(n.op,ast.Sub):return a-b
            if isinstance(n.op,ast.Mult):return a*b
            if isinstance(n.op,ast.Pow) and 0<=b<=8:return a**b
        raise ValueError(ast.dump(n))
    return go(ast.parse(expr,mode='eval').body)


def recipe_value(recipe, ports, p=None):
    ans=0
    for t in recipe:
        v=t['coefficient']
        for z,e in zip(ports,t['powers']):v*=pow(z,e,p) if p else z**e
        ans+=v
    return ans%p if p else ans


def dag_value(obj, vv, ports, p):
    fixed={r['name']:recipe_value(r['terms'],ports,p) for r in obj['coefficient_recipes']}
    fixed['radix_scale']=pow(2,obj['radix_scale_exponent'],p)
    out=[]
    for ix,n in enumerate(obj['nodes']):
        k=n['kind']
        if k=='variable':z=vv[n['name']]
        elif k=='fixed':z=fixed[n['name']]
        elif k=='literal':z=n['value']
        else:
            assert 0<=n['left']<ix and 0<=n['right']<ix
            a,b=out[n['left']],out[n['right']]
            if k=='add':z=a+b
            elif k=='sub':z=a-b
            elif k=='mul':z=a*b
            else:raise ValueError(k)
        out.append(z%p)
    return out[obj['output']],{k:out[ix] for k,ix in obj['named_nodes'].items()}


def flags(obj):
    # Explicit metadata is preferred; initial release predates these optional keys.
    crt=obj.get('crt_reparameterized',obj.get('crt',False))
    scale=obj.get('radicand_scale',obj.get('square_scale',4))
    return crt,scale


def direct_value(obj, target, raw, ports, p):
    crt,scale=flags(obj)
    v=dict(raw)
    if obj['domain']=='positive integers':
        for k in ['phi','n']+(['j'] if crt else []):v[k]-=1
    else:
        for k in ['b','g','h','s','w','i']+([] if crt else ['j']):v[k]+=1
    b,g,h,s,w,phi,i,j,n=[v[k]%p for k in obj['variables']]
    B=pow(2,obj['radix_scale_exponent'],p)*b*b%p
    W=max(target['weights']);Hmax=max(r['target_exponent'] for r in target['rows']);K=target.get('Kcode',Hmax+2*W)
    env=dict(zip(target['ports'],ports));DC=0
    for row in target['rows']:
        for term in row['terms']:
            DC=(DC+scalar_expr(term['weighted_coefficient'],env)*pow(B,term['encoding_exponent'],p))%p
    ell=sum(pow(B,w,p) for w in target['weights'])%p
    N0=pow(B,W+1,p);N1=4*pow(B,K+1,p)%p;N=N0*N1%p
    mask=(N0-1-(b-1)*ell)%p
    targets=sum(pow(B,row['target_exponent'],p) for row in target['rows'])%p
    Tc=(mask+(B-2)*targets*N0)%p
    geom=sum(pow(B,k,p) for k in range(K+1))%p
    Jc=(2*(pow(B,obj.get('padding_exponent',0),p)+g)**2*DC+B*geom)%p
    Sc=(g+Jc*N0)%p
    R=(N-1)*((Sc+Tc+1)*N+Tc+1)%p
    cap=32*b*pow(B,W,p)%p
    U=N*N*w%p;Y=N*N*s%p;M0=R*Y%p
    P=2*M0*M0*U%p;K=(R+1+h*(P-1))%p
    A=M0*(U+1)%p;B1=(2*R+1)%p;W1=b*w%p;C=(B1+W1+phi)%p
    J=(4*A-5)%p;Q=(3*W1*C-2*(W1*W1-1))%p
    D=((A*A-1)*C*C+1)%p;E=i*J*D*C*C%p;F=((A*A-1)*E*E+1)%p
    G=(A+F*(C*D+1-A))%p
    H=(C+F*(B1+j*C) if crt else B1+j*C)%p
    I=((G*G-1)*H*H+1)%p
    a0=((P*P-1)*K*K+1)%p;a1=D*F*I%p
    m=((K*K-4*(C-K*Y)**2)*cap-8*g*K*K)%p
    if crt:u=J;vv=Q;Md=Q
    else:u=J*F%p;vv=(Q*F+J*(H-C))%p;Md=(Q+H)%p
    V0=P*K%p
    if scale==4:V1=(2*D-1)*(i*J*D*C)*G*H%p
    elif scale==64:V1=(i*J*C)*(8*D*D-4*D-1)*G*H%p
    else:raise ValueError(('Unsupported explicit radicand scale',scale))
    Om=u*m%p
    Th=((u*n+vv-Om*(V0+V1)) if obj.get('offset_free',False) else (u*(n+Md)+vv-Om*(2*Md+V0+V1)))%p
    ans=((Th*Th-Om*Om*(a0+scale*a1))**2-4*scale*pow(Om,4,p)*a0*a1)%p
    return ans,dict(B=B,Dcode=DC,N=N,R=R,Gcap=cap,P=P,K=K,A=A,C=C,J=J,Q=Q,D=D,E=E,F=F,G=G,H=H,I=I,a0=a0,a1=a1,u=u,v=vv,m=m,V0=V0,V1=V1,Mdiv=Md,Omega=Om,Theta=Th)


def polyadd(a,b,sgn=1):
    c=dict(a)
    for e,v in b.items():c[e]=c.get(e,0)+sgn*v
    return {e:v for e,v in c.items() if v}


def polymul(a,b):
    c=defaultdict(int)
    for e,v in a.items():
        for f,w in b.items():c[e+f]+=v*w
    return {e:v for e,v in c.items() if v}


def exact_degree(obj,ports):
    fixed={r['name']:recipe_value(r['terms'],ports) for r in obj['coefficient_recipes']}
    out=[]
    for ix,n in enumerate(obj['nodes']):
        k=n['kind']
        if k=='variable':z=(1,{0:1})
        elif k=='fixed' and n['name']=='radix_scale':z=(0,{1:1})
        elif k in ['fixed','literal']:
            value=fixed[n['name']] if k=='fixed' else n['value']
            z=(0,{0:value}) if value else (-1,{})
        else:
            da,ca=out[n['left']];db,cb=out[n['right']]
            if k=='mul':z=(da+db,polymul(ca,cb)) if ca and cb else (-1,{})
            else:
                if da>db:z=(da,ca)
                elif db>da:z=(db,cb if k=='add' else {e:-v for e,v in cb.items()})
                else:
                    lc=polyadd(ca,cb,1 if k=='add' else -1)
                    assert lc or da<=0,('Unresolved positive-degree cancellation',ix,n,da)
                    z=(da,lc) if lc else (-1,{})
        out.append(z)
    return out[obj['output']],{k:out[ix] for k,ix in obj['named_nodes'].items()}


def target_audit(t):
    ws=t['weights'];assert len(ws)==31 and len(set(ws))==31 and min(ws)>=0
    terms=[];padding=t.get('padding_exponent',0)
    assert 0<=padding<max(ws)
    for length in range(3):
        for inds in combinations_with_replacement(range(31),length):
            alpha=tuple(inds.count(i) for i in range(31));terms.append(((2-length)*padding+sum(ws[i] for i in inds),alpha))
    assert len(terms)==528
    bycode=defaultdict(list)
    for w,a in terms:bycode[w].append(a)
    targets={r['target_exponent']:ix for ix,r in enumerate(t['rows'])};assert len(targets)==22
    occupied=set();cross_checks=0;top=[]
    for ri,row in enumerate(t['rows']):
        for z in row['terms']:
            a=tuple(z['alpha']);w=(2-sum(a))*padding+sum(x*y for x,y in zip(a,ws));e=z['encoding_exponent']
            assert bycode[w]==[a]
            assert e==row['target_exponent']-w and e>=0 and e not in occupied
            occupied.add(e);top.append((e,z['weighted_coefficient']))
            for code,alpha in terms:
                if e+code in targets:assert targets[e+code]==ri and alpha==a
                cross_checks+=1
    e,c=max(top);assert e==t['Dmax'] and c=='2'
    assert t['Kcode']>=e+2*max(ws) and t['Kcode']>t['target_maximum']
    return dict(expansion_monomials=528,encoded_terms=len(occupied),cross_checks=cross_checks,Dmax=e)


def norm(a,b,V,W,u,v,M,m,n):
    O=u*m;T=u*(n+M)+v-O*(2*M+V+W)
    return (T*T-O*O*(a+b))**2-4*O**4*a*b


def norm_free(a,b,V,W,u,v,m,n):
    O=u*m;T=u*n+v-O*(V+W)
    return (T*T-O*O*(a+b))**2-4*O**4*a*b


def abstract_audit():
    free_checks=free_roots=0
    for a,b in product(range(1,13),repeat=2):
        V,W=isqrt(a)+1,isqrt(b)+1
        for u in range(1,4):
            for v in range(1,u*(V+W)):
                for m in range(-2,4):
                    if m>0 and a==b:continue
                    for n in range(40):
                        value=norm_free(a,b,V,W,u,v,m,n);free_checks+=1
                        if value==0:
                            assert m>0 and isqrt(a)**2==a and isqrt(b)**2==b and v%u==0
                            free_roots+=1
    checks=roots=0
    for a,b in product(range(1,13),repeat=2):
        V,W=isqrt(a)+1,isqrt(b)+1
        for u,M in product(range(1,4),range(2,5)):
            for v in range(1,u*M):
                for m in range(-2,4):
                    if m>0 and a==b:continue
                    for n in range(40):
                        value=norm(a,b,V,W,u,v,M,m,n);checks+=1
                        if value==0:
                            assert m>0 and isqrt(a)**2==a and isqrt(b)**2==b and v%u==0
                            roots+=1
    fixtures=0
    for r,s,u,q,m in product(range(1,7),range(1,7),range(1,4),range(1,4),range(1,4)):
        if r==s:continue
        M=q+1;V=r+1;W=s+1;n=m*(2*M+V+W+r+s)-M-q
        assert n>=0 and norm(r*r,s*s,V,W,u,u*q,M,m,n)==0
        free_n=m*(V+W+r+s)-q
        assert free_n>=0 and norm_free(r*r,s*s,V,W,u,u*q,m,free_n)==0;fixtures+=1
    assert norm(2,2,2,2,2,2,2,1,5)==0
    assert norm(1,4,-2,-3,1,1,2,-1,1)==0
    assert norm_free(2,2,2,2,2,2,1,3)==0
    assert norm_free(1,4,-2,4,1,1,-1,0)==0
    return dict(offset_free_soundness_cases=free_checks,offset_free_zeros_found=free_roots,shifted_corollary_soundness_cases=checks,zeros_found=roots,completeness_fixtures=fixtures,essential_hypothesis_counterexamples=2)


def crt_and_majorants():
    checks=0
    for A,C,i,jp,B1 in product(range(2,9),range(2,8),range(1,4),range(4),range(1,2)):
        J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
        assert F%J==1 and F%C==1
        H=C+F*(B1+jp*C);oldj=1+(F-1)//C*B1+F*jp
        assert oldj>=1 and H==B1+oldj*C
        z=(H-C)//F;assert z==B1+jp*C and (z-B1)//C==jp
        L=i*J*D*C;k=i*J*C
        assert ((2*D-1)*L)**2-4*D*F==L*L-4*D>0
        T=k*(8*D*D-4*D-1)
        assert T*T-64*D*F==(8*D+1)*k*k-64*D>0
        checks+=1
    return checks


def main():
    if not __debug__:raise RuntimeError('Assertions required')
    binding=json.loads((ROOT/'coefficients/COEFFICIENT_BINDING.json').read_text());ports=[]
    for r in binding['ports']:
        raw=gzip.decompress((ROOT/'coefficients'/r['gzip_file']).read_bytes())
        assert hashlib.sha256(raw).hexdigest()==r['sha256']
        value=int.from_bytes(raw,'little');assert value.bit_length()==r['bits'];ports.append(value)
    rng=random.Random(770038);results=[];target_results={}
    for path in sorted((ROOT/'nine/generated').glob('nine_*_positive.json')):
        obj=json.loads(path.read_text());targetpath=ROOT/obj['target_file'];data=json.loads(targetpath.read_text())
        assert hashlib.sha256(targetpath.read_bytes()).hexdigest()==obj['target_sha256']
        target_results[obj['target_file']]=target_audit(data)
        certpath=path.with_name(path.stem+'_degree_certificate.json');cert=json.loads(certpath.read_text())
        nat=json.loads(path.with_name(path.name.replace('_positive','_natural')).read_text())
        assert set(n['name'] for n in obj['nodes'] if n['kind']=='variable')==set(obj['variables']) and len(obj['variables'])==9
        actual_fixed=[recipe_value(r['terms'],ports) for r in obj['coefficient_recipes']]
        mexp=obj['coefficient_bound_exponent'];assert all(abs(c)<(1<<mexp) for c in actual_fixed)
        bounds=[sum(abs(t['coefficient'])*(1<<sum(e*b for e,b in zip(t['powers'],obj['port_bit_lengths']))) for t in r['terms']) for r in obj['coefficient_recipes']]
        assert max(bounds).bit_length()==mexp and obj['radix_scale_exponent']==mexp+12
        for item in [obj,cert,nat]:
            assert Counter(n['kind'] for n in item['nodes'] if 'left' in n)==item['operation_counts']
            assert sum(item['operation_counts'].values())==item['total_operations']
        calls=0
        for p in [1000000007,1000000009,2147483647]:
            reduced=[x%p for x in ports]
            for repeat in range(12):
                v={n:rng.randrange(1,70) for n in obj['variables']}
                actual,named=dag_value(obj,v,reduced,p);direct,expected=direct_value(obj,data,v,reduced,p)
                assert actual==direct,(path.name,'output',actual,direct)
                for k,want in expected.items():
                    if k in named:assert named[k]==want,(path.name,k,named[k],want)
                assert actual==dag_value(cert,v,reduced,p)[0]
                shifted={k:x-1 for k,x in v.items()}
                assert actual==dag_value(nat,shifted,reduced,p)[0]
                calls+=1
        (deg,lc),named=exact_degree(cert,ports)
        assert deg==obj['degree']==cert['degree']
        claimed=obj['diagonal_leading_coefficient']
        assert lc=={claimed['radix_scale_power']:2**claimed['power_of_two']},(path.name,lc,claimed)
        assert named['Dcode']==(2*data['Dmax'],{data['Dmax']:2})
        results.append(dict(file=str(path.relative_to(ROOT)),sha256=hashlib.sha256(path.read_bytes()).hexdigest(),degree=deg,operations=obj['total_operations'],actual_tuple_direct_modular_replays=calls,leading_coefficient=claimed,crt=flags(obj)[0],radicand_scale=flags(obj)[1],offset_free=obj.get('offset_free',False)))
    report=dict(status='PASS',circuit_results=results,target_results=target_results,abstract_theorem_tests=abstract_audit(),crt_and_majorant_cases=crt_and_majorants(),scope='Independent finite checks and exact degree proof by leading-term induction. No builder imports. Does not kernel-check the semantic compiler or Jones ratio theorem.')
    (ROOT/'audit/INDEPENDENT_NINE_VERIFICATION.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
if __name__=='__main__':main()
