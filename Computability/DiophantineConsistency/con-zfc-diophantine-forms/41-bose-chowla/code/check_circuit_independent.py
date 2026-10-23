#!/usr/bin/env python3
"""Independent audit of the emitted B4 ten-integer circuit.

No import of either circuit builder or its evaluator.  The Dcode identity
is exact over Z[B,beta,K0,MC,MF].  Scalar checks are finite diagnostics,
not a proof of the unbounded Diophantine correspondence.
"""
from pathlib import Path
from collections import Counter
from itertools import combinations_with_replacement
from functools import lru_cache
import gzip, hashlib, json, random

ROOT=Path(__file__).resolve().parents[1]
UP=ROOT/'upstream/source31/signed10/data'
CIRCUIT=ROOT/'generated/equation10.json'
ORDER=['f','g','h','k','l','w','x','y','z','m']

def require(value,message):
    if not value: raise AssertionError(message)

def add(a,b,sign=1):
    result=dict(a)
    for key,value in b.items():
        result[key]=result.get(key,0)+sign*value
        if result[key]==0: del result[key]
    return result

def mul(a,b):
    result={}
    for ea,ca in a.items():
        for eb,cb in b.items():
            ex=tuple(x+y for x,y in zip(ea,eb))
            result[ex]=result.get(ex,0)+ca*cb
    return {ex:c for ex,c in result.items() if c}

def audit_D(circuit,constants):
    nodes=circuit['nodes']; names=circuit['named_nodes']; weights=circuit['weights']
    fixed={row['name']:{(0,)+tuple(t['powers']):t['coefficient']
                      for t in row['coefficient_polynomial_in_fixed_ports']}
           for row in constants['coefficient_records']}
    zero=(0,)*5
    @lru_cache(None)
    def expand(i):
        if i==names['base']: return {(1,0,0,0,0):1}
        n=nodes[i]; kind=n['kind']
        if kind=='literal': return {zero:n['value']} if n['value'] else {}
        if kind=='fixed': return fixed[n['name']]
        require(kind in ('add','sub','mul'),'unexpected variable in Dcode')
        a,b=expand(n['left']),expand(n['right'])
        return mul(a,b) if kind=='mul' else add(a,b,-1 if kind=='sub' else 1)
    expected={}
    for row in constants['coefficient_records']:
        alpha=row['alpha']; require(len(alpha)==32 and alpha[0]==0,'unexpected input term')
        exponent=4*weights[-1]-sum(a*w for a,w in zip(alpha[1:],weights[1:]))
        require(exponent>=0,'negative Dcode exponent')
        for term in row['coefficient_polynomial_in_fixed_ports']:
            key=(exponent,)+tuple(term['powers'])
            expected[key]=expected.get(key,0)+term['coefficient']
    expected={key:value for key,value in expected.items() if value}
    actual=expand(names['Dcode'])
    require(actual==expected,'exact source encoding differs')
    for name,exponent in [('qcode',4*weights[-1]),('top',weights[-1]),('N0',weights[-1]+1)]:
        require(expand(names[name])=={(exponent,0,0,0,0):1},name+' exponent differs')
    require(expand(names['ell'])=={(w,0,0,0,0):1 for w in weights[1:]},'mask positions differ')
    require(expand(names['N1'])=={(8*weights[-1]+1,0,0,0,0):4},'N1 differs')
    require(expand(names['N'])=={(9*weights[-1]+2,0,0,0,0):4},'N differs')
    return dict(exact_identity=True,ring='Z[B,beta,K0,MC,MF]',
                coefficient_records=len(constants['coefficient_records']),
                expanded_terms=len(expected),positions=31,target=4*weights[-1])

def actual_ports():
    binding=json.loads((UP/'coefficients_binding.json').read_text()); ports={}; hashes={}
    for row in binding['files']:
        name=row['name']; compressed=(UP/(name+'.bin.gz')).read_bytes(); raw=gzip.decompress(compressed)
        require(hashlib.sha256(compressed).hexdigest()==row['gzip_sha256'],'gzip hash')
        require(hashlib.sha256(raw).hexdigest()==row['sha256'],'raw hash')
        value=int.from_bytes(raw,'little');require(value.bit_length()==row['bit_length'],'port size')
        ports[{'K':'K0','MF_source':'MF'}.get(name,name)]=value;hashes[name]=row['sha256']
    ins=json.loads((UP/'INSTANCE.json').read_text()); row=ins['beta_sun']
    compressed=(UP/row['file']).read_bytes();raw=gzip.decompress(compressed)
    require(hashlib.sha256(compressed).hexdigest()==row['gzip_sha256'],'beta gzip')
    require(hashlib.sha256(raw).hexdigest()==row['sha256'],'beta hash')
    require(int.from_bytes(raw,'little')==1<<4269882,'beta literal')
    return ports,hashes

def evaluate(circuit,variables,fixed,p):
    values=[]
    for i,n in enumerate(circuit['nodes']):
        kind=n['kind']
        if kind=='literal': z=n['value']
        elif kind=='variable': z=variables[n['name']]
        elif kind=='fixed': z=fixed[n['name']]
        else:
            require(n['left']<i and n['right']<i,'cyclic DAG')
            a,b=values[n['left']],values[n['right']]
            z=a+b if kind=='add' else a-b if kind=='sub' else a*b
        values.append(z%p)
    return {name:values[index] for name,index in circuit['named_nodes'].items()}

def literal(circuit,constants,v,fixed,p):
    Wmax=circuit['W'];weights=circuit['weights'];r=lambda z:z%p
    b=r(1+3*v['f']);B=r(fixed['beta_sun']*pow(b,4,p))
    top=pow(B,Wmax,p);qcode=pow(B,4*Wmax,p)
    ell=sum(pow(B,w,p) for w in weights[1:])%p
    Dcode=0
    for row in constants['coefficient_records']:
        e=sum(a*w for a,w in zip(row['alpha'][1:],weights[1:]))
        Dcode+=fixed[row['name']]*pow(B,4*Wmax-e,p)
    Dcode%=p
    N0=pow(B,Wmax+1,p);N1=r(4*pow(B,8*Wmax+1,p));N=r(N0*N1)
    Mcode=r(N0-1-(b-1)*ell);Tcode=r(Mcode+(B-2)*qcode*N0)
    length=8*Wmax+1
    geometric=length%p if B==1 else r((pow(B,length,p)-1)*pow((B-1)%p,-1,p))
    Jcode=r(2*pow(1+v['g'],4,p)*Dcode+B*geometric)
    Scode=r(v['g']+Jcode*N0);Rcode=r((Scode+Tcode+1)*N+Tcode+1)
    X=r((N-1)*Rcode);Y=r(N*N);Ccap=r(b*top)
    result=dict(b=b,base=B,top=top,qcode=qcode,ell=ell,Dcode=Dcode,N0=N0,N1=N1,N=N,
                Mcode=Mcode,Tcode=Tcode,Jcode=Jcode,Scode=Scode,Rcode=Rcode,X=X,Y=Y,Ccap=Ccap)
    L=r(v['l']*Y);U=r(2*L*X);V=r(4*v['g']*v['w']*Y);W=r(b*v['w'])
    A=r(U*(V+1));smallB=r(2*X+1);C=r(smallB+(A-2)*v['h']);Pn=r(U*U*V)
    K=r(X+1+v['k']*(Pn-2));S=r(2*A-5);T=r(3*W*C-2*(W*W-1))
    R2=r((Pn*Pn-4)*K*K+4)
    Delta=r(8*Ccap**3*v['g']*K*K-v['g']**2*(32*(C-K*L)**2*Ccap**3+v['g']**2*K*K))
    O0=r(v['f']**2*v['l']**2*Delta);xi=r(v['z']*v['x'])
    D=r((A*A-4)*C*C+4);E=r(C*C*D*xi);F=r(4*(A*A-4)*E*E+1)
    G=r(2*(A+2)*(A-2)**2*E*E-1);Omega=r(16*E)
    H=r(C+(smallB-C)*F+Omega*F*v['y']);I=r((G*G-1)*H*H+1)
    Sigma=r(xi*pow(S,5,p));arg=r(T+S*v['y'])
    Theta=r((arg**3-arg*S*S-S**3)*(arg*arg+23*S*S))
    bracket=r(1+(3*O0-4)*b*b*v['z']**2)
    rad=[r(b*bracket),R2,r(D*F*I)];weight1=rad[0];weight2=r(weight1*(Pn*Pn+K*K+3))
    center=r(Sigma*v['m']-Theta);scaled=[r(Sigma*Sigma*ww*ww*aa) for aa,ww in zip(rad,[1,weight1,weight2])]
    a0,a1,a2=scaled;xx=r(center*center);vv=r(xx+a2-a0-a1)
    ww=r(vv*vv+4*xx*a2-4*a0*a1)
    out=r(ww*ww-16*vv*vv*xx*a2)
    result.update(Lsmall=L,U=U,V=V,Wsmall=W,A=A,Bsmall=smallB,C=C,Pn=Pn,K=K,Ssmall=S,Tsmall=T,
                  R2=R2,Delta=Delta,O0=O0,xi=xi,D=D,E=E,F=F,Gstar=G,Omega=Omega,Hstar=H,Istar=I,
                  Sigma=Sigma,merger_argument=arg,Theta=Theta,positivity_bracket=bracket,
                  norm_weight1=weight1,norm_weight2=weight2,norm_center=center,F10=out,
                  **{'A'+str(i+1):a for i,a in enumerate(rad)},
                  **{'scaled_A'+str(i+1):a for i,a in enumerate(scaled)})
    return result

def main():
    circuit=json.loads(CIRCUIT.read_text());constants=json.loads((UP/'constants.json').read_text())
    weights=circuit['weights'];seen=set()
    for inds in combinations_with_replacement(range(32),4):
        s=sum(weights[i] for i in inds);require(s not in seen,'B4 collision');seen.add(s)
    require(len(seen)==52360,'B4 count');require(weights[0]==0 and weights==sorted(set(weights)),'weight order')
    require(circuit['W']==weights[-1]==610895,'W binding')
    require(circuit['reversal_target']==4*weights[-1] and circuit['convolution_top']==8*weights[-1],'block lengths')
    variables=[n['name'] for n in circuit['nodes'] if n['kind']=='variable'];require(variables==ORDER,'ten variables')
    counts=Counter(n['kind'] for n in circuit['nodes']);operations=sum(counts[k] for k in ('add','sub','mul'))
    require(operations==1333 and counts['fixed']==79,'size metrics')
    require({k:counts[k] for k in ('add','sub','mul')}==circuit['operation_counts'],'operation metadata')
    live={circuit['output']}
    for i in reversed(range(len(circuit['nodes']))):
        n=circuit['nodes'][i]
        if i in live and n['kind'] in ('add','sub','mul'):live.update((n['left'],n['right']))
    require(len(live)==len(circuit['nodes']),'dead gate or input')
    d_audit=audit_D(circuit,constants);ports,hashes=actual_ports();rng=random.Random(183726)
    scalar=0
    for p in [1000000007,1000000009,2147483647]:
        fixed={'beta_sun':pow(2,4269882,p)}
        for row in constants['coefficient_records']:
            fixed[row['name']]=sum(t['coefficient']*__import__('functools').reduce(
                lambda a,b:a*b%p,(pow(ports[name]%p,e,p) for name,e in zip(constants['fixed_port_order'],t['powers'])),1)
                for t in row['coefficient_polynomial_in_fixed_ports'])%p
        samples=[{name:0 for name in ORDER},{name:1 for name in ORDER},{name:-1 for name in ORDER}]
        samples += [{name:rng.randrange(-p,p) for name in ORDER} for _ in range(17)]
        for v in samples:
            got=evaluate(circuit,v,fixed,p);expected=literal(circuit,constants,v,fixed,p)
            require(got==expected,'literal scalar mismatch '+str([(k,got[k],expected.get(k)) for k in got if got[k]!=expected.get(k)][:3]))
            scalar+=1
    receipt=dict(status='PASS',circuit_sha256=hashlib.sha256(CIRCUIT.read_bytes()).hexdigest(),
                 unknowns=variables,operations=operations,fixed_leaves=counts['fixed'],
                 all_gates_live=True,B4_multisets=len(seen),maximum_weight=weights[-1],
                 exact_Dcode_audit=d_audit,all_named_values_scalar_checks=scalar,
                 primes=[1000000007,1000000009,2147483647],coefficient_payload_hashes=hashes,
                 scope='Exact source polynomial coding identity and literal DAG checks; finite scalar checks do not prove semantic equivalence.')
    path=ROOT/'generated/CIRCUIT_AUDIT.json';path.write_text(json.dumps(receipt,indent=2)+'\n')
    print(json.dumps(receipt,indent=2))

if __name__=='__main__':main()
