#!/usr/bin/env python3
"""Build and check the 121-operation, degree-246 positive equation.

No external packages or network required. Universal center identities use
exact sparse polynomials. Modular circuit/degree evaluations are independent
transcription controls, not proofs of Diophantine equivalence.
"""
import gzip, hashlib, json, math, random
from collections import Counter
from pathlib import Path
import sparse_polynomials as S

HERE = Path(__file__).resolve().parent
checks = []

def require(name, ok, **details):
    checks.append(dict(name=name, ok=bool(ok), **details))
    if not ok:
        raise ValueError(name)

def make_graph():
    raw = (HERE/'source/parent94.json').read_bytes()
    require('pinned parent graph', hashlib.sha256(raw).hexdigest()==
            'f0fc0e216a0cfdb8371a022d498b0fc9d92845ac65204e5eeef4febe7bd63efa')
    require('pinned parent proof', hashlib.sha256((HERE/'source/parent_proof.md').read_bytes()).hexdigest()==
            '765c519246a738a03bfff54c902e171ac0f7ee668a0a43a4463ce7e00c63c408')
    parent = json.loads(raw)
    newrows = [
        ['L2','*','Xp1','Xp1'],
        ['L3','*','L2','Xp1'],
        ['lambda','*',8,'L3'],
        ['tX','*','muY','X'],
        ['tX2','*','tX','X'],
        ['Hm3','-','Hp',3],
        ['pHm3','*','Am1','Hm3'],
        ['fourL','*',4,'Xp1'],
        ['sumHigh','+','pHm3','fourL'],
        ['coefHigh','+','sumHigh',9],
        ['uHigh','*','tX2','coefHigh'],
        ['tXmL2','-','tX','L2'],
        ['fourLow','*',4,'tXmL2'],
        ['threeL','*',3,'Xp1'],
        ['low1','-','fourLow','threeL'],
        ['low2','+','low1',14],
        ['corrInner','+','uHigh','low2'],
        ['k2','*','k','k'],
        ['corrFactor','*','k2','corrInner'],
        ['Ecorrection','*','I','corrFactor'],
        ['Afull','+','Am1',1],
        ['lambdaA','*','lambda','Afull'],
        ['topCenter','*','lambdaA','DtauI'],
        ['Gamma','-','topCenter','Ecorrection'],
    ]
    rows = []
    for original in parent['source']:
        row = list(original)
        if row[0] == 'nV': rows.extend(newrows)
        if row[0] == 'nVL': row[2] = 'nVGamma'
        if row[0] == 'fa': row[3] = 'weightedPair'
        rows.append(row)
        if row[0] == 'nV': rows.append(['nVGamma','+','nV','Gamma'])
        if row[0] == 'pair':
            rows.extend([['lambda2','*','lambda','lambda'],
                         ['weightedPair','*','lambda2','pair']])
    out = {k:v for k,v in parent.items() if k not in
           ('source','operations','operation_breakdown','exact_degree',
            'syntactic_degree','parent','parent_sha256','centre','name')}
    out.update(name='weighted_polynomial_center246',
               parent='source/parent94.json',
               parent_sha256=hashlib.sha256(raw).hexdigest(),
               centre='Gamma=E(8(X+1)^3 A D-4Q1-Q3)',
               radical_weight='lambda=8(X+1)^3',
               exact_degree=246, operations=len(rows), source=rows,
               operation_breakdown=dict(Counter(r[1] for r in rows)),
               proof='PROOF.md')
    return out

def validate_graph(d):
    seen=set(d['witnesses']+d['fixed_numerals'])
    deg={v:1 for v in d['witnesses']}
    deg.update({v:0 for v in d['fixed_numerals']})
    rows=d['source']
    for name,op,a,b in rows:
        require('valid graph '+name, name not in seen and op in '+-*'
                and all(not isinstance(x,str) or x in seen for x in (a,b)))
        da=deg[a] if isinstance(a,str) else 0
        db=deg[b] if isinstance(b,str) else 0
        deg[name]=da+db if op=='*' else max(da,db)
        seen.add(name)
    live={d['output']}
    for name,op,a,b in reversed(rows):
        if name in live:
            live.update(x for x in (a,b) if isinstance(x,str))
    require('all rows and inputs live',all(r[0] in live for r in rows)
            and set(d['witnesses']+d['fixed_numerals'])<=live)
    require('operation count',len(rows)==121,count=len(rows))
    d['syntactic_degree']=deg[d['output']]

def ports():
    binding=json.loads((HERE/'coefficients/BINDING.json').read_text())
    values={}
    for name,meta in binding['ports'].items():
        data=(HERE/'coefficients'/meta['file']).read_bytes()
        raw=gzip.decompress(data)
        require('whole-tuple hash '+name,
                hashlib.sha256(data).hexdigest()==meta['gzip_sha256'] and
                hashlib.sha256(raw).hexdigest()==meta['raw_sha256'])
        values[name]=int.from_bytes(raw,'little')
        require('coefficient bits '+name,values[name].bit_length()==meta['bits'])
    b=values['beta']
    require('port box',b>=31 and b%2==1 and values['K0']>0 and
            0<values['MC']<b<values['MF']<2*b)
    return values

def ev(rows,env,p):
    v=dict(env)
    for name,op,a,b in rows:
        a=v[a] if isinstance(a,str) else a
        b=v[b] if isinstance(b,str) else b
        v[name]=(a+b if op=='+' else a-b if op=='-' else a*b)%p
    return v

def formula(env,p):
    v={k:x%p for k,x in env.items()}
    J,F,alpha,i,T,x,Y,n,eta,zeta=(v[k] for k in
        ('J','F','alpha','i','T','x','Y','n','eta','zeta'))
    beta,K0,MC,MF=(v[k] for k in ('beta','K0','MC','MF'))
    q=(beta*J+1)%p; X=(q+x)%p; L=(X+1)%p
    mu=(q*q+1)%p; t=mu*Y%p; A=(t*L+1)%p; Delta=(A*A-1)%p
    H=(4*A-5)%p; k=(eta+zeta)%p; c=(k*Y+eta)%p
    V1=X*t*t%p; D=(1+V1*(V1+1)*k*k)%p; E=i*c*c%p
    R=(((q-1)*(q-F)+alpha)*(q*q-1)+(MC+q*MF)*J)%p
    e=(k-R-1)%p; B=((q*K0+X)*(q-F-alpha)-q*F)%p
    Fs=(1+Delta*D*E*E)%p; Q=Delta*Delta*D*E*E%p
    delta=(Q-1)%p; b=(c*(T+alpha)-R)%p; V=(Fs*b-c)%p
    Dnum=(Q*V*V-1)%p; P=q**4*(q-1)%p; M=P*mu*mu*H%p
    Kpos=(X*(3*c-2*X)+2)%p; lam=8*L**3%p
    Q1=k*k*(t**3*L*L*X*X-t*t*L*X*X+
            t*(L**3-2*L+1)-L*L+2)%p
    Q3=k*k*(t*X*X-3*L+6)%p
    Gamma=E*(8*L**3*A*D-4*Q1-Q3)%p
    Z=(P*mu*mu*(H*(n+V+Gamma-b*B)+Kpos)+
       H*(mu*mu*(q*(q-1)*Y-q**3*B-(q-1)*X)-P*e))%p
    a=lam*lam*D*Fs%p
    return ((delta*Z*Z-M*M*Dnum-delta*M*M*a)**2-
            4*delta*M**4*a*Dnum)%p

def local_identities():
    L,t,k,E=S.L,S.t,S.k,S.E
    A,D=S.A,S.D
    C,residual,qs=S.make(3,0)
    q1=qs[0][2];q3=qs[1][2]
    X=L-1; u=t*X*X; par=A-1
    q1_display=k*k*(t**3*L**2*X**2-t**2*L*X**2+
                    t*(L**3-2*L+1)-L**2+2)
    q3_display=k*k*(t*X*X-3*L+6)
    require('exact Q1 polynomial',not(q1-q1_display))
    require('exact Q3 polynomial',not(q3-q3_display))
    correction=k*k*(u*(4*par*(par-1)+4*L+9)+
                     4*(t*X-L*L)-3*L+14)
    require('paid circuit center identity',not(correction-4*q1-q3))
    require('r1 identity',not(L**3*D-A*q1-(L**3+k*k*(L*L-t-2))))
    r3=L**3*D-A**3*q3
    require('r3 degree',r3.degree()==13,degree=r3.degree())
    actual=64*residual
    require('center defect degree',actual.degree()==34,degree=actual.degree())
    lead=S.Poly({m:c for m,c in actual.items()
                 if sum(a*b for a,b in zip(m,S.WEIGHTS))==34})
    expected=-112*L**5*t**5*k**4*E**2
    require('exact center leading form',not(lead-expected))
    require('all defect coefficients integral',all(c.denominator==1 for c in actual.values()))
    certificate={'variables':['L','t','k','E'],'weights':list(S.WEIGHTS),
                 'identity':'Gamma^2-lambda^2*a; a=D+Delta*D^2*E^2',
                 'terms':[[int(c),list(m)] for m,c in sorted(actual.items())]}
    (HERE/'center_defect.json').write_text(json.dumps(certificate,indent=2)+'\n')

def leading(point,pm,p):
    q=pm['beta']*point['J']%p; X=(q+point['x'])%p
    mu=q*q%p;t=mu*point['Y']%p;k=(point['eta']+point['zeta'])%p
    E=point['i']*(k*point['Y'])**2%p;D=X*X*t**4*k*k%p
    A=t*X%p;Delta=A*A%p;Q=Delta*Delta*D*E*E%p
    b=-q**3*(q-point['F'])%p;Fs=Delta*D*E*E%p;V=Fs*b%p
    M=4*q**9*A%p
    B=((q*pm['K0']+X)*(q-point['F']-point['alpha'])-
       q*point['F'])%p
    C0=-112*X**5*t**5*k**4*E*E%p
    G0=8*X**6*t**5*k*k*E%p
    return 4*Q*Q*M**4*V*V*(C0-2*G0*b*B)%p

def line_check(d,pm,p,seed):
    rng=random.Random(seed)
    direction={w:rng.randrange(1,p) for w in d['witnesses']}
    vals=[]
    for h in range(d['syntactic_degree']+2):
        env={k:v%p for k,v in pm.items()}
        env.update({w:h*x%p for w,x in direction.items()})
        vals.append(ev(d['source'],env,p)['N'])
    top=0;degree=0;cur=vals
    for j in range(len(vals)):
        if not any(cur):break
        top=cur[0];degree=j
        cur=[(cur[h+1]-cur[h])%p for h in range(len(cur)-1)]
    top=top*pow(math.factorial(degree)%p,-1,p)%p
    require('actual whole-tuple ray degree '+str(seed),degree==246,
            degree=degree,prime=p)
    require('full norm leading form '+str(seed),
            top==leading(direction,{k:v%p for k,v in pm.items()},p))

def main():
    d=make_graph();validate_graph(d);local_identities();pm=ports()
    for p,seed in [((1<<61)-1,31),((1<<89)-1,47),((1<<127)-1,83)]:
        rng=random.Random(seed)
        okay=True
        for _ in range(24):
            env={k:v%p for k,v in pm.items()}
            env.update({w:rng.randrange(p) for w in d['witnesses']})
            okay &= ev(d['source'],env,p)['N']==formula(env,p)
        require('independent formula evaluations '+str(seed),okay,count=24)
        line_check(d,pm,p,seed)
    (HERE/'equation.json').write_text(json.dumps(d,indent=2)+'\n')
    summary={'ok':all(c['ok'] for c in checks),'checks':checks,
             'operations':d['operations'],'operation_breakdown':d['operation_breakdown'],
             'exact_degree':246,'syntactic_degree':d['syntactic_degree']}
    (HERE/'RESULTS.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps({k:summary[k] for k in
          ('ok','operations','operation_breakdown','exact_degree','syntactic_degree')}))
    print('Checks:',len(checks))

if __name__=='__main__':main()
