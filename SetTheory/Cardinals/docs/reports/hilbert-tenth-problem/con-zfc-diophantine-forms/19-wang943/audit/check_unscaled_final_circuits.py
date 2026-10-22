"""Fresh independent rank-four norm checks. No received code is executed."""
import hashlib
import json
from pathlib import Path
from random import Random

ROOT = Path(__file__).resolve().parents[1]
RNG = Random(12572465)

def multiply(x, y, a, g, p):
    out = [0] * 4
    for ix, vx in enumerate(x):
        for iy, vy in enumerate(y):
            z = vx * vy
            if ix & iy & 1:
                z *= a
            if ix & iy & 2:
                z *= g
            out[ix ^ iy] = (out[ix ^ iy] + z) % p
    return out

def norm(x, a, g, p):
    out = [1, 0, 0, 0]
    for r, s in ((1, 1), (-1, 1), (1, -1), (-1, -1)):
        out = multiply(out, [x[0], r*x[1], s*x[2], r*s*x[3]], a, g, p)
    assert out[1:] == [0, 0, 0]
    return out[0]

def direct(raw, coeff, signed, p):
    if signed:
        def pos(n):
            a, b, c = [raw[n + '_positive_' + t] for t in 'abc']
            return 1 + a*a + b*b + c*(c+1)
        z = {n: pos(n) for n in ('J', 'F', 'alpha', 'z', 's', 'eta', 'zeta')}
        z.update(h=raw['h'], T=raw['T'], t=raw['t'], i=2*raw['i_integer']+1,
                 w=raw['w_integer']**2)
    else:
        z = raw
    J,F,alpha,zz,h,i,T,s,w,eta,zeta,t = [z[n] for n in
        ('J','F','alpha','z','h','i','T','s','w','eta','zeta','t')]
    beta,K0,MC,MF = [coeff[n] for n in ('beta','K0','MC','MF')]
    q=beta*J+1; X=w*q; Y=s*q**3; E=X*Y; k=eta+zeta
    c=k*Y+eta; a=E+Y; H=4*a+3; Delta=a*a+H
    R=((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J
    L=E*k*Y; A=1+L*(L+k); G=1+Delta*c*c
    I=i*c*c; S=Delta*I; Q=S*S; D=1+I*S; d=Q-1
    v=c*T; b=c+R*D; e=Q*(D*v*v+b*b)-1; B=2*Q*v*b
    W=2*((S*i)*v*v+b) if signed else 2*(S*v+b)
    P=H*W; K=P+1; u=6*P; Z=H*t+K*(X+a*c)
    lin=[Z%p, -u%p, -K%p, 0]
    bracket=[d*x%p for x in multiply(lin,lin,A,G,p)]
    bracket[0]=(bracket[0]-H*H*e)%p
    f=multiply(bracket,bracket,A,G,p)
    f[0]=(f[0]-H**4*B*B*D)%p
    res=norm(f,A,G,p)
    Nk=k-h*E-R; Nt=(K0+w)*(q-F-alpha)+q-F-zz*(q-1)
    return (Nk*Nt*(1+res)-1)%p

receipts=[]
for rel, signed, nv, ng, nm, degree in (
    ('roots/root12_saturated_product.json', False, 12,139,93,1257),
    ('integers/integer26_unscaled_four_root192_degree2465.json', True,26,192,117,2465),
):
    path=ROOT/rel
    body=path.read_bytes(); f=json.loads(body); gates=f['source']; ws=f['witnesses']
    assert len(ws)==nv and len(set(ws))==nv and len(gates)==ng
    assert sum(g[1]=='*' for g in gates)==nm
    known=set(ws)|set(f['fixed_numerals']); deps={}
    for name,op,a,b in gates:
        assert name not in known and op in ('+','-','*')
        assert all(not isinstance(x,str) or x in known for x in (a,b))
        deps[name]={x for x in (a,b) if isinstance(x,str)}
        known.add(name)
    live={f['output']}; todo=list(live)
    while todo:
        for x in deps.get(todo.pop(),()):
            if x not in live:
                live.add(x); todo.append(x)
    assert all(g[0] in live for g in gates) and all(x in live for x in ws)
    for case in range(240):
        prime=(1000003,1000033)[case%2]
        raw={x:RNG.randrange(-4,5) if signed else RNG.randrange(1,8) for x in ws}
        coeff={'beta':15,'K0':7,'MC':2,'MF':20}
        env=raw|coeff
        for name,op,a,b in gates:
            aa=env[a] if isinstance(a,str) else a
            bb=env[b] if isinstance(b,str) else b
            env[name]=(aa+bb if op=='+' else aa-bb if op=='-' else aa*bb)%prime
        assert env[f['output']]==direct(raw,coeff,signed,prime), (rel,case)
    receipts.append({'path':rel,'status':'PASS','variables':nv,'operations':ng,
        'multiplications':nm,'additions_subtractions':ng-nm,
        'all_gates_live':True,'all_ports_live':True,
        'independent_rank_four_norm_comparisons':240,
        'written_proof_exact_degree':degree,
        'sha256':hashlib.sha256(body).hexdigest()})
out={'status':'PASS','artifacts':receipts,
     'method':'Fresh direct rank-four norm; JSON interpreted only as inert binary arithmetic data.'}
(ROOT/'audit/UNSCALED_FINAL_CIRCUIT_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
