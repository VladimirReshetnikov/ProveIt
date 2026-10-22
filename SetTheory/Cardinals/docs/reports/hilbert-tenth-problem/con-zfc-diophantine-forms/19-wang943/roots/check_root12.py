"""Independent tests: quadratic-algebra norm, modular degree, and kernel witnesses."""
import json, random, hashlib
from fractions import Fraction
from math import isqrt
from pathlib import Path
import numpy as np

HERE=Path(__file__).resolve().parent
RNG=random.Random(20261022)

def evaluate(data,inputs,p=None):
    env=dict(inputs)
    for name,op,a,b in data['source']:
        a=env[a] if isinstance(a,str) else a;b=env[b] if isinstance(b,str) else b
        val=a*b if op=='*' else a+b if op=='+' else a-b
        env[name]=val%p if p else val
    return env

def ringmul(x,y,A,G,p):
    z=[0]*4
    for i,a in enumerate(x):
        for j,b in enumerate(y):
            f=(A if i&j&1 else 1)*(G if i&j&2 else 1)
            z[i^j]=(z[i^j]+a*b*f)%p
    return z

def direct_norm(A,G,Z,u,K,H,e,B,D,d,p):
    # Work independently in F_p[r,s]/(r^2-A,s^2-G).
    W=[Z,-u,-K,0]
    P=ringmul(W,W,A,G,p)
    P=[d*x%p for x in P];P[0]=(P[0]-H*H*e)%p
    F=ringmul(P,P,A,G,p);F[0]=(F[0]-H**4*B*B*D)%p
    norm=[1,0,0,0]
    for er,es in [(1,1),(-1,1),(1,-1),(-1,-1)]:
        factor=[F[0],er*F[1],es*F[2],er*es*F[3]]
        norm=ringmul(norm,factor,A,G,p)
    assert norm[1:]==[0,0,0]
    return norm[0]

def univariate_degrees(data,p,seed):
    rng=random.Random(seed)
    env={name:np.array([rng.randrange(1,p),rng.randrange(1,p)],dtype=np.int64) for name in data['witnesses']}
    env.update({name:np.array([rng.randrange(1,p)],dtype=np.int64) for name in data['fixed_numerals']})
    def value(x):return env[x] if isinstance(x,str) else np.array([x%p],dtype=np.int64)
    for name,op,x,y in data['source']:
        a,b=value(x),value(y)
        if op=='*':
            # Degree below 3000 and p<65536 imply convolution sums <2^63.
            assert min(len(a),len(b))*(p-1)**2 <2**63
            z=np.convolve(a,b)%p
        else:
            z=np.zeros(max(len(a),len(b)),dtype=np.int64)
            z[:len(a)]+=a;z[:len(b)]+=b if op=='+' else -b;z%=p
        while len(z)>1 and z[-1]==0:z=z[:-1]
        env[name]=z
    return {name:len(env[name])-1 for name in ['Nk','Nt','Res12','polynomial12'] if name in env}

def audit_liveness(data):
    definitions={x[0]:x[2:] for x in data['source']}
    outputs=[data['output']] if 'output' in data else [x for pair in data['comparisons'] for x in pair if isinstance(x,str)]
    live=set();pending=outputs[:]
    while pending:
        x=pending.pop()
        if x in live:continue
        live.add(x)
        if x in definitions:pending.extend(a for a in definitions[x] if isinstance(a,str))
    assert set(definitions)<=live
    assert set(data['witnesses'])<=live
    assert set(data['fixed_numerals'])<=live
    known=set(data['witnesses']+data['fixed_numerals'])
    for name,op,a,b in data['source']:
        assert name not in known
        assert all(not isinstance(x,str) or x in known for x in (a,b))
        known.add(name)

def pell(S,n):
    x,y=1,0
    for _ in range(n):x,y=S*x+(S*S-1)*y,x+S*y
    return x,y

def kernel_cases(scaled):
    count=0;p=1000000007
    for S in range(2,9):
        for n in [1,3,5]:
            x,y=pell(S,n);V=x//S;assert x%S==0
            f=2;D=f*f;v=V+3;b=v*f-V
            Q=S*S;d=Q-1;e=Q*(D*v*v+b*b)-1;B=2*Q*v*b
            tau,g,H,offset=9,15,7,1
            gamma=2;assert g-offset==H*gamma
            Y=2*(S*v+b);bound=d*Y if scaled else Y
            K=H*bound+1;M=6*bound
            tail=d*y if scaled else y
            t=K*gamma+M*tau+tail
            Z=H*t+K*offset;u=H*M
            er,Br,dr=(d*e,d*B,1) if scaled else (e,B,d)
            assert direct_norm(tau*tau,g*g,Z,u,K,H,er,Br,D,dr,p)==0
            count+=1
    return count

def main():
    binding=json.loads((HERE/'COEFFICIENT_BINDING.json').read_text())
    assert binding['port_aliases']=={'beta':'beta','K0':'K','MC':'MC','MF':'MF_source'}
    file_checks={}
    for name,entry in binding['coefficient_files'].items():
        data=(HERE/entry['path']).read_bytes()
        assert len(data)==entry['bytes']
        digest=hashlib.sha256(data).hexdigest();assert digest==entry['sha256']
        file_checks[name]=digest
    report={'coefficient_binding':{'backend':binding['selected_backend'],'all_four_exact_files_checked':True,'sha256':file_checks}}
    for name in ['root12_product','root12_scaled_y_product','root12_saturated_product']:
        data=json.loads((HERE/(name+'.json')).read_text());audit_liveness(data)
        assert data['coefficient_binding']==binding
        scaled='scaled_y' in name
        for _ in range(100):
            p=1000000007
            inputs={n:RNG.randrange(1,100) for n in data['witnesses']+data['fixed_numerals']}
            env=evaluate(data,inputs,p)
            er=env['eraux'] if scaled else env['eaux']
            Br=env['Braux'] if scaled else env['Baux']
            d=1 if scaled else env['daux']
            expected=direct_norm(env['Afirst'],env['Gmain'],env['Zlinear'],env['uweight'],env['Kweight'],env['H'],er,Br,env['Dstrong'],d,p)
            assert expected==env['Res12'],(name,expected,env['Res12'])
        degrees=[univariate_degrees(data,p,seed) for p,seed in [(65521,12121),(65519,12122)]]
        assert degrees[0]==degrees[1]
        data['exact_degree']=degrees[0]['polynomial12']
        data['residual_exact_degrees']=[degrees[0]['Nk'],degrees[0]['Nt'],degrees[0]['Res12']]
        data['ledger'].update(all_gates_live=True,all_ports_live=True)
        (HERE/(name+'.json')).write_text(json.dumps(data,indent=2)+'\n')
        sysname=name.replace('_product','_system');system=json.loads((HERE/(sysname+'.json')).read_text())
        audit_liveness(system);system['residual_exact_degrees']=data['residual_exact_degrees']
        system['ledger'].update(all_gates_live=True,all_ports_live=True)
        (HERE/(sysname+'.json')).write_text(json.dumps(system,indent=2)+'\n')
        report[name]={'ledger':data['ledger'],'independent_norm_assignments':100,
                      'modular_degrees':degrees,'synthetic_kernel_witnesses':kernel_cases(scaled)}
    checks=0;squares=0
    for S in range(2,51):
        for V in range(1,1001):
            f=Fraction(S*S*V*V-1,S*S-1);a,b=isqrt(f.numerator),isqrt(f.denominator)
            if a*a==f.numerator and b*b==f.denominator:
                assert b==1;squares+=1
            checks+=1
    report['rational_y_saturation_test']={'pairs':checks,'rational_square_cases':squares,'nonintegral_cases':0}
    (HERE/'ROOT12_TEST_RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))

if __name__=='__main__':main()
