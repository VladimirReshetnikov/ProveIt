#!/usr/bin/env python3
"""Independent audit: JSON only, no imports from the circuit builder.

Recover each actual quadratic source row by evaluations/polarization;
compare a literal sparse-power source and literal Sun finalizer with every
available named node; recompute liveness/counts and degree certificate.
"""
import gzip
import itertools
import json
import math
import random
import sys
from pathlib import Path

DEFAULT_ROOT = Path(__file__).resolve().parents[1]
PRIMES = (1000000007, 1000000009, 998244353)


def parent_at(parent, n, ports, p):
    env = dict(ports)
    env.update({name:(x+1)%p for name,x in zip(parent['variables'],n)})
    def get(x): return x if isinstance(x,int) else env[x]
    for name, op, a, b in parent['source']:
        a,b=get(a),get(b)
        env[name]=(a*b if op=='*' else a+b if op=='+' else a-b)%p
    return [(get(a)-get(b))%p for a,b in parent['comparisons']]


def recipes_at(data, ports, p):
    fixed={}
    for name,recipe in data['recipes'].items():
        value=0
        for term in recipe:
            v=term['coefficient']
            for port,e in zip(data['ports'],term['powers']):
                v=v*pow(ports[port],e,p)%p
            value+=v
        fixed[name]=value%p
    fixed['beta_source']=pow(2,data['beta_source_exponent'],p)
    return fixed


def recover_rows(parent,data,ports,p):
    n=len(parent['variables']);zero=[0]*n
    v0=parent_at(parent,zero,ports,p)
    plus=[];minus=[]
    for i in range(n):
        z=zero.copy();z[i]=1;plus.append(parent_at(parent,z,ports,p))
        z[i]=-1;minus.append(parent_at(parent,z,ports,p))
    rows=[{} for _ in v0]
    def put(alpha,vals):
        for row,v in zip(rows,vals):
            if v%p:row[tuple(alpha)]=v%p
    # These are factorial-weighted coefficients directly.
    put(zero, [2*v for v in v0])
    inv2=pow(2,-1,p)
    for i in range(n):
        a=zero.copy();a[i]=1
        put(a,[(vp-vm)*inv2 for vp,vm in zip(plus[i],minus[i])])
        a[i]=2
        put(a,[vp+vm-2*c for vp,vm,c in zip(plus[i],minus[i],v0)])
    for i,j in itertools.combinations(range(n),2):
        a=zero.copy();a[i]=a[j]=1
        vp=parent_at(parent,a,ports,p)
        put(a,[v-x-y+c for v,x,y,c in zip(vp,plus[i],plus[j],v0)])
    return [rows[j-1] for j in data['row_order_one_based']]


def check_coefficients(parent,data,ports,p):
    expected=recover_rows(parent,data,ports,p)
    fixed=recipes_at(data,ports,p)
    got=[]
    for row in data['rows']:
        d={}
        for term in row:
            leaf=term['leaf']
            v=leaf if isinstance(leaf,int) else fixed[leaf]
            v=v*term['sign']%p
            if v:d[tuple(term['alpha'])]=v
        got.append(d)
    assert got==expected, 'Parent/polarized weighted-coefficient mismatch'
    return fixed,expected


def literal(v, p, fixed, rows, weights):
    f,g,h,k,l,w,x,y,z,m=(v[a]%p for a in ('f','g','h','k','l','w','x','y','z','m'))
    t=max(weights);targets=[2*t+j*(2*t+1) for j in range(22)]
    span=targets[-1]+2*t
    b=(1+3*f)%p;B=fixed['beta_source']*b*b%p
    def power(n):return pow(B,n,p)
    def geom(n):return n%p if B==1 else (power(n)-1)*pow(B-1,-1,p)%p
    Dcode=0
    for row,E in zip(rows,targets):
        for alpha,coefficient in row.items():
            exponent=E-sum(a*w for a,w in zip(alpha,weights[1:]))
            assert exponent>=0
            Dcode=(Dcode+coefficient*power(exponent))%p
    top=power(t);ell=sum(power(w) for w in weights[1:])%p
    N0=power(t+1);N1=4*power(span+1)%p;N=N0*N1%p
    targetsum=sum(power(E) for E in targets)%p
    target=(B-2)*targetsum%p
    mask=(N0-1-(b-1)*ell)%p
    Tc=(mask+target*N0)%p
    J=(2*pow(1+g,2,p)*Dcode+B*geom(span+1))%p
    Sc=(g+J*N0)%p;Rc=((Sc+Tc+1)*N+Tc+1)%p
    X=(N-1)*Rc%p;Y=N*N%p;cap=b*top%p
    got={'b':b,'base':B,'top':top,'block_step':power(2*t+1),
         'Dcode':Dcode,'ell':ell,'N0':N0,'N1':N1,'N':N,
         'targetsum':targetsum,'target':target,'mask':mask,
         'Tcode':Tc,'Jcode':J,'Scode':Sc,'Rcode':Rc,'X':X,'Y':Y,'Ccap':cap}

    L=l*Y%p;U=2*L*X%p;V=4*g*w*Y%p;W=b*w%p
    A=U*(V+1)%p;Bs=(2*X+1)%p;C=(Bs+(A-2)*h)%p
    Pn=U*U*V%p;K=(X+1+k*(Pn-2))%p;S=(2*A-5)%p
    T=(3*W*C-2*(W*W-1))%p;R2=((Pn*Pn-4)*K*K+4)%p
    db=(8*pow(cap,3,p)*g*K*K-g*g*(32*pow(C-K*L,2,p)*pow(cap,3,p)+g*g*K*K))%p
    O=f*f*l*l*db%p;xi=z*x%p
    Dl=((A*A-4)*C*C+4)%p;El=C*C*Dl*xi%p
    Fl=(4*(A*A-4)*El*El+1)%p
    Gs=(2*(A+2)*pow(A-2,2,p)*El*El-1)%p;Omega=16*El%p
    Hs=(C+(Bs-C)*Fl+Omega*Fl*y)%p;Is=((Gs*Gs-1)*Hs*Hs+1)%p
    Sigma=xi*pow(S,5,p)%p;r=(T+S*y)%p
    Theta=(pow(r,3,p)-r*S*S-pow(S,3,p))*(r*r+23*S*S)%p
    r0=b*(1+(3*O-4)*b*b*z*z)%p;r1=R2;r2=Dl*Fl*Is%p
    w1=r0;w2=r0*(Pn*Pn+K*K+3)%p;center=(Sigma*m-Theta)%p
    a0=Sigma*Sigma*r0%p;a1=Sigma*Sigma*w1*w1*r1%p;a2=Sigma*Sigma*w2*w2*r2%p
    Vn=(center*center+a2-a0-a1)%p
    Wn=(Vn*Vn+4*center*center*a2-4*a0*a1)%p
    out=(Wn*Wn-16*Vn*Vn*center*center*a2)%p
    got.update({'Lsmall':L,'U':U,'V':V,'Wsmall':W,'A':A,'Bsmall':Bs,
                'C':C,'Pn':Pn,'K':K,'Ssmall':S,'Tsmall':T,'R2':R2,
                'Delta':db,'O':O,'xi':xi,'D':Dl,'E':El,'F':Fl,'Gstar':Gs,
                'Omega':Omega,'Hstar':Hs,'Istar':Is,'Sigma':Sigma,
                'merger_argument':r,'Theta':Theta,'r0':r0,'r1':r1,'r2':r2,
                'weight1':w1,'weight2':w2,'center':center,'a0':a0,'a1':a1,
                'a2':a2,'Vnorm':Vn,'Wnorm':Wn,'F10':out})
    return out,got


def eval_json(body,fixed,v,p):
    vals=[]
    for i,node in enumerate(body['nodes']):
        kind=node['kind']
        if kind=='literal':value=node['value']
        elif kind=='fixed':value=fixed[node['name']]
        elif kind=='variable':value=v[node['name']]
        else:
            assert node['left']<i and node['right']<i
            a,b=vals[node['left']],vals[node['right']]
            value=a+b if kind=='add' else a-b if kind=='sub' else a*b
        vals.append(value%p)
    return vals[body['output']],{name:vals[i] for name,i in body['named_nodes'].items()}


def main(root):
    body=json.loads((root/'data/polynomial.json').read_text())
    data=json.loads((root/'data/coefficient_recipes.json').read_text())
    parent=json.loads((root/'upstream/parent_system.json').read_text())
    weights=json.loads((root/'data/weights.json').read_text())['weights']
    ports={name:int.from_bytes(gzip.decompress((root/'coefficients/payloads'/f'{file}.bin.gz').read_bytes()),'little')
           for name,file in zip(('beta','K0','MC','MF'),('beta','K','MC','MF_source'))}
    variables=body['variables'];nodes=body['nodes']
    counts={k:sum(n['kind']==k for n in nodes) for k in ('add','sub','mul')}
    assert counts==body['operation_counts']
    assert sum(counts.values())==653
    assert sorted(n['name'] for n in nodes if n['kind']=='variable')==sorted(variables)
    assert len(variables)==10 and len(set(variables))==10
    live={body['output']}
    for i in range(len(nodes)-1,-1,-1):
        assert i in live,('dead node',i)
        if nodes[i]['kind'] in counts:live.update((nodes[i]['left'],nodes[i]['right']))
    coefficient_checks=0;case_count=0;named_checks=0;degree_certificates=[]
    for p in PRIMES:
        pp={k:v%p for k,v in ports.items()}
        fixed,rows=check_coefficients(parent,data,pp,p)
        coefficient_checks+=22*528
        rng=random.Random(20261023+p)
        cases=[dict.fromkeys(variables,a) for a in (0,1,-1,2,-2)]
        cases += [{name:(0 if name==special else 1) for name in variables} for special in variables]
        cases += [{name:rng.randrange(-10000,10001) for name in variables} for _ in range(25)]
        for v in cases:
            expected,refs=literal(v,p,fixed,rows,weights)
            actual,got=eval_json(body,fixed,v,p)
            assert actual==expected,('output',p,v)
            assert set(got)<=set(refs),set(got)-set(refs)
            for name,value in got.items():
                assert value==refs[name],('named node',name,p,v,value,refs[name])
            case_count+=1;named_checks+=len(got)
        # Independent upper-degree and exact diagonal leading-coefficient check.
        deg=[];lead=[]
        for node in nodes:
            k=node['kind']
            if k=='literal':d,v=0,node['value']%p
            elif k=='fixed':d,v=0,fixed[node['name']]
            elif k=='variable':d,v=1,1
            else:
                a,b=node['left'],node['right']
                if k=='mul':d,v=deg[a]+deg[b],lead[a]*lead[b]%p
                else:
                    d=max(deg[a],deg[b]);va=lead[a] if deg[a]==d else 0;vb=lead[b] if deg[b]==d else 0
                    v=(va+vb if k=='add' else va-vb)%p
            deg.append(d);lead.append(v)
        assert deg[body['output']]==56593864 and lead[body['output']]!=0
        degree_certificates.append({'prime':p,'degree':deg[body['output']],'leading_coefficient':lead[body['output']]})
    result={'status':'PASS','operation_counts':counts,'operations':sum(counts.values()),
            'unrestricted_variables':len(variables),'fixed_nonliteral_leaves':sum(n['kind']=='fixed' for n in nodes),
            'all_nodes_live':True,'polarized_weighted_coefficient_checks':coefficient_checks,
            'modular_literal_formula_cases':case_count,'named_node_comparisons':named_checks,
            'degree_certificates':degree_certificates,
            'method':'Independent JSON interpreter, parent polarization, sparse powers and modular geometric quotient; no builder code imported.',
            'scope':'Exact finite algebraic diagnostics and a degree lower-bound certificate, not an end-to-end proof-assistant theorem.'}
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    if not __debug__: raise SystemExit('Run without -O: audit assertions are required.')
    main(Path(sys.argv[1]).resolve() if len(sys.argv)>1 else DEFAULT_ROOT)
