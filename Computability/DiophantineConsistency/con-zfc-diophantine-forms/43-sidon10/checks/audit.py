#!/usr/bin/env python3
"""Independent exact audit of the B2 block compiler and ten-integer circuit.

Reads delivered JSON rather than importing its builder. The coefficient
extraction check is a complete symbolic identity in all 31 source unknowns
and all four coefficient ports, not evaluation at selected sample points.
"""
from collections import defaultdict
from itertools import combinations_with_replacement, product
from pathlib import Path
from math import factorial
import gzip, hashlib, json, random, sys

HERE=Path(__file__).resolve().parent
TARGET=Path(sys.argv[1]).resolve() if len(sys.argv)>1 else HERE.parent

def add(a,b):
    c=a.copy()
    for ex,v in b.items():
        c[ex]=c.get(ex,0)+v
        if not c[ex]:del c[ex]
    return c

def mul(a,b):
    c=defaultdict(int)
    for ex,v in a.items():
        for ey,w in b.items():c[tuple(x+y for x,y in zip(ex,ey))]+=v*w
    return {ex:v for ex,v in c.items() if v}

def shifted_equations(source):
    r=len(source['variables']); k=len(source['constants']); zero=(0,)*(r+k)
    out=[]
    for equation in source['equations']:
        pol={}
        for term in equation['terms']:
            prod={zero:term['coefficient']}
            for i,e in enumerate(term['powers']):
                if not e:continue
                ex=list(zero);ex[i]=1
                factor={tuple(ex):1}
                if i<r:factor[zero]=1
                for _ in range(e):prod=mul(prod,factor)
            pol=add(pol,prod)
        out.append(pol)
    return out

def verify_sources(body,records,source):
    pos=body['source']['positions']; H=max(pos); step=body['source']['stride']
    assert len(pos)==32 and pos[0]==0 and all(x>0 for x in pos[1:])
    pair_sums={}
    for i,j in combinations_with_replacement(range(32),2):
        s=pos[i]+pos[j]; assert s not in pair_sums
        pair_sums[s]=(i,j)
    assert len(pair_sums)==528 and step==2*H+1
    shifted=shifted_equations(source)
    assert len(shifted)==22
    r=31;zero=(0,)*r
    # Verify the complete weighted source records, including each fixed leaf.
    for block in records['blocks']:
        expected={}
        for ex,c in shifted[block['source_equation']-1].items():
            alpha=ex[:r]
            fac=factorial(2-sum(alpha))
            for e in alpha:fac*=factorial(e)
            expected[ex]=c*fac
        received={}
        for row in block['records']:
            ref=row['coefficient']
            if 'fixed' in ref:
                assert row['recipe']==records['recipes'][ref['fixed']]
            else:
                assert row['recipe']==[{'powers':[0]*4,'coefficient':ref['literal']}]
            for term in row['recipe']:
                ex=tuple(row['alpha'])+tuple(term['powers'])
                received[ex]=term['coefficient']
        assert expected==received
    assert records['blocks'][-1]['source_equation']==5
    assert shifted[4].get((0,)*35)==1
    # Check *every possible contribution* to every target digit symbolically.
    targets={j*step+2*H:j for j in range(22)}
    extracted=[{} for _ in range(22)]
    contributions=0
    for qsum,(i,j) in pair_sums.items():
        alpha=[0]*r
        for a in [i,j]:
            if a:alpha[a-1]+=1
        cmult=1 if i==j else 2
        for k,block in enumerate(records['blocks']):
            for row in block['records']:
                dexp=k*step+2*H-sum(a*w for a,w in zip(row['alpha'],pos[1:]))
                assert dexp>=0
                where=targets.get(dexp+qsum)
                if where is None:continue
                for term in row['recipe']:
                    ex=tuple(alpha)+tuple(term['powers'])
                    extracted[where]=add(extracted[where],{ex:cmult*term['coefficient']})
                    contributions+=1
    for k,block in enumerate(records['blocks']):
        assert extracted[k]=={ex:2*c for ex,c in shifted[block['source_equation']-1].items()}
    return dict(distinct_pair_sums=528,source_quadratics=22,
                weighted_records=sum(len(b['records']) for b in records['blocks']),
                target_coefficient_symbolic_identities=22,
                nonzero_target_contributions=contributions,
                top_unweighted_constant=1,
                range_separation='D blocks [j*stride,j*stride+2H] disjoint; target differences exceed2H.')

def fixed_values(records,data):
    binding=json.loads((data/'coefficients_binding.json').read_text())
    ports={}; rows=[]
    for row in binding['files']:
        name=row['name']; payload=(data/(name+'.bin.gz')).read_bytes()
        raw=gzip.decompress(payload)
        assert hashlib.sha256(raw).hexdigest()==row['sha256']
        assert hashlib.sha256(payload).hexdigest()==row['gzip_sha256']
        v=int.from_bytes(raw,'little');assert v.bit_length()==row['bit_length']
        ports[{'K':'K0','MF_source':'MF'}.get(name,name)]=v
        rows.append({'name':name,'sha256':row['sha256'],'bits':v.bit_length()})
    # Compute exact fixed coefficients independently, caching powers only.
    pows=[[pow(ports[p],e) for e in range(3)] for p in records['ports']]
    def value(recipe):
        total=0
        for term in recipe:
            c=term['coefficient']
            for j,e in enumerate(term['powers']):c*=pows[j][e]
            total+=c
        return total
    fixed={name:value(recipe) for name,recipe in records['recipes'].items()}
    bound=(1<<2134927)
    all_coefficients=[value(row['recipe']) for b in records['blocks'] for row in b['records']]
    assert max(abs(c) for c in all_coefficients)<bound
    beta=1<<2134940
    assert beta>8192*max(abs(c) for c in all_coefficients)
    fixed['beta_source']=beta
    return fixed,dict(ports=rows,max_weighted_coefficient_bits=max(abs(c).bit_length() for c in all_coefficients),
                      bound_exponent=2134927,beta_exponent=2134940,
                      beta_exceeds_8192_times_maximum=True)

def eval_dag(body,fixed,v,p):
    vals=[]
    for n in body['nodes']:
        kind=n['kind']
        if kind=='literal':x=n['value']
        elif kind=='fixed':x=fixed[n['name']]
        elif kind=='variable':x=v[n['name']]
        else:
            a,b=vals[n['left']],vals[n['right']]
            x=a+b if kind=='add' else a-b if kind=='sub' else a*b
        vals.append(x%p)
    return vals[body['output']],{name:vals[i] for name,i in body['named_nodes'].items()}

def geom(B,n,p):
    # Direct modular division except at B=1, with a separate case B=0.
    if B==1:return n%p
    return (pow(B,n,p)-1)*pow(B-1,-1,p)%p

def literal(body,records,fixed,v,p):
    red=lambda x:x%p
    pos=body['source']['positions'];H=max(pos);step=2*H+1;Q=21*step+4*H
    b=red(1+3*v['f']);base=red(fixed['beta_source']*b*b)
    top=pow(base,H,p);ell=sum(pow(base,e,p) for e in pos[1:])%p
    named={}
    blockvalues=[]
    for j,block in enumerate(records['blocks']):
        value=0
        for row in block['records']:
            ref=row['coefficient'];coef=ref['literal'] if 'literal'in ref else fixed[ref['fixed']]
            exponent=2*H-sum(a*w for a,w in zip(row['alpha'],pos[1:]))
            value+=coef*pow(base,exponent,p)
        value%=p;blockvalues.append(value);named['Dblock'+str(j)]=value
    Dcode=sum(value*pow(base,j*step,p) for j,value in enumerate(blockvalues))%p
    target=sum(pow(base,j*step+2*H,p) for j in range(22))%p
    N0=pow(base,H+1,p);N1=red(4*pow(base,Q+1,p));N=red(N0*N1)
    Mcode=red(N0-1-(b-1)*ell);Tcode=red(Mcode+(base-2)*target*N0)
    Jcode=red(2*(1+v['g'])**2*Dcode+base*geom(base,Q+1,p))
    Scode=red(v['g']+Jcode*N0);Rcode=red((Scode+Tcode+1)*N+Tcode+1)
    X=red((N-1)*Rcode);Y=red(N*N);cap=red(b*top)
    L=red(v['l']*Y);U=red(2*L*X);V=red(4*v['g']*v['w']*Y);W=red(b*v['w'])
    A=red(U*(V+1));B=red(2*X+1);C=red(B+(A-2)*v['h']);Pn=red(U*U*V)
    K=red(X+1+v['k']*(Pn-2));S=red(2*A-5);T=red(3*W*C-2*(W*W-1))
    R2=red((Pn*Pn-4)*K*K+4)
    Delta=red(8*cap**3*v['g']*K*K-v['g']**2*(32*(C-K*L)**2*cap**3+v['g']**2*K*K))
    O=red(v['f']**2*v['l']**2*Delta);xi=red(v['z']*v['x'])
    D=red((A*A-4)*C*C+4);E=red(C*C*D*xi);F=red(4*(A*A-4)*E*E+1)
    G=red(2*(A+2)*(A-2)**2*E*E-1);Omega=red(16*E)
    Hstar=red(C+(B-C)*F+Omega*F*v['y']);I=red((G*G-1)*Hstar*Hstar+1)
    Sigma=red(xi*S**5);r=red(T+S*v['y']);Theta=red((r**3-r*S*S-S**3)*(r*r+23*S*S))
    bracket=red(1+(3*O-4)*b*b*v['z']**2)
    A1=red(b*bracket);A2=R2;A3=red(D*F*I);w1=A1;w2=red(A1*(Pn*Pn+K*K+3))
    center=red(Sigma*v['m']-Theta)
    a0=red(Sigma*Sigma*A1);a1=red(Sigma*Sigma*w1*w1*A2);a2=red(Sigma*Sigma*w2*w2*A3)
    # Independent elimination: norm of [(x+sqrt(a2))^2-a0-a1]^2-4a0a1.
    # Writing this as u+v*sqrt(a2), its norm is u^2-a2*v^2.
    z=red(center*center+a2-a0-a1)
    u=red(z*z+4*center*center*a2-4*a0*a1);vv=red(4*z*center)
    out=red(u*u-a2*vv*vv)
    named.update(dict(b=b,base=base,top=top,ell=ell,blockstep=pow(base,step,p),
          Dcode=Dcode,target=target,N0=N0,N1=N1,N=N,Mcode=Mcode,Tcode=Tcode,Jcode=Jcode,
          Scode=Scode,Rcode=Rcode,X=X,Y=Y,Ccap=cap,Lsmall=L,U=U,V=V,Wsmall=W,
          A=A,Bsmall=B,C=C,Pn=Pn,K=K,Ssmall=S,Tsmall=T,R2=R2,Delta=Delta,O0=O,
          xi=xi,D=D,E=E,F=F,Gstar=G,Omega=Omega,Hstar=Hstar,Istar=I,
          Sigma=Sigma,merger_argument=r,Theta=Theta,positivity_bracket=bracket,
          A1=A1,A2=A2,A3=A3,norm_weight1=w1,norm_weight2=w2,norm_center=center,
          scaled_A1=a0,scaled_A2=a1,scaled_A3=a2,F10=out))
    return out,named

def degree(body,fixed,p):
    vals=[]
    for n in body['nodes']:
        kind=n['kind']
        if kind=='literal':x=(0,n['value']%p)
        elif kind=='fixed':x=(0,fixed[n['name']]%p)
        elif kind=='variable':x=(1,1)
        else:
            (da,a),(db,b)=vals[n['left']],vals[n['right']]
            if kind=='mul':x=(da+db,a*b%p)
            else:
                high=max(da,db);x=(high,((a if da==high else 0)+(1 if kind=='add' else -1)*(b if db==high else 0))%p)
        vals.append(x)
    d,leading=vals[body['output']]
    assert d==body['degree_upper_bound'] and leading!=0
    return dict(prime=p,degree=d,diagonal_leading_coefficient=leading)

def main():
    body=json.loads((TARGET/'generated/signed10_b2.json').read_text())
    records=json.loads((TARGET/'generated/source_records.json').read_text())
    raw=(TARGET/'data/parent_quartic31.json').read_bytes();source=json.loads(raw)
    expected='1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287'
    assert hashlib.sha256(raw).hexdigest()==expected==records['source_sha256']
    algebra=verify_sources(body,records,source)
    fixed,bindings=fixed_values(records,TARGET/'data')
    checks=[];rng=random.Random(202610237)
    for p in [101,1009,1000003]:
        deg=degree(body,fixed,p);cases=0;named_count=0
        for _ in range(16):
            v={k:rng.randrange(-10,11) for k in body['variables']}
            actual,named=eval_dag(body,fixed,v,p)
            expected,expected_named=literal(body,records,fixed,v,p)
            assert actual==expected
            assert named==expected_named,(set(named)^set(expected_named))
            cases+=1;named_count+=len(named)
        checks.append(dict(prime=p,assignments=cases,named_node_comparisons=named_count,degree_certificate=deg))
    ops={k:sum(n['kind']==k for n in body['nodes']) for k in ['add','sub','mul']}
    assert ops==body['operation_counts']
    out=dict(status='PASS',scope='Exact algebraic/source and finite transcription audit; no solvability search.',
             source_sha256=records['source_sha256'],symbolic_source_audit=algebra,
             coefficients=bindings,checks=checks,operation_counts=ops,total_operations=sum(ops.values()),
             exact_degree=body['degree_upper_bound'],variables=body['variables'])
    (TARGET/'generated/INDEPENDENT_AUDIT.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))

if __name__=='__main__':main()
