#!/usr/bin/env python3
"""Independent live-gate and leading-form audit, using only Python stdlib."""
import hashlib
import gzip
import json
from pathlib import Path
import random
ROOT=Path(__file__).resolve().parent

def require(p,msg):
    if not p: raise ValueError(msg)

def add(a,b,sign=1):
    out=dict(a)
    for m,c in b.items():
        out[m]=out.get(m,0)+sign*c
        if out[m]==0: del out[m]
    return out

def mul(a,b):
    out={}
    for m,c in a.items():
        for n,d in b.items():
            key=tuple(x+y for x,y in zip(m,n))
            out[key]=out.get(key,0)+c*d
    return {m:c for m,c in out.items() if c}

def audit():
    path=ROOT/'fourteen_positive.json'
    data=json.loads(path.read_text())
    witnesses=data['witnesses'];ports=data['fixed_numerals'];names=witnesses+ports
    require(len(witnesses)==14 and len(set(names))==18,'ports')
    zero=(0,)*len(names)
    def const(n): return {zero:n} if n else {}
    def var(name):
        e=list(zero);e[names.index(name)]=1
        return {tuple(e):1}
    def power(a,n):
        b=const(1)
        for _ in range(n):b=mul(b,a)
        return b
    values={n:(1 if n in witnesses else 0,var(n)) for n in names}
    exact={n:var(n) for n in names}
    main_poly=None
    producers={};counts={'+':0,'-':0,'*':0}
    def operand(x):return (0,const(x)) if type(x)==int else values[x]
    for name,op,a,b in data['source']:
        require(name not in values,'duplicate gate')
        da,pa=operand(a);db,pb=operand(b)
        degree=da+db if op=='*' else max(da,db)
        top=mul(pa,pb) if op=='*' else add(pa if da==degree else {},pb if db==degree else {},1 if op=='+' else -1)
        if main_poly is None:
            ea=const(a) if type(a)==int else exact[a]
            eb=const(b) if type(b)==int else exact[b]
            exact[name]=mul(ea,eb) if op=='*' else add(ea,eb,1 if op=='+' else -1)
            if name=='main_residual':
                main_poly=exact[name]
                degree=max(sum(m[:len(witnesses)]) for m in main_poly)
                top={m:v for m,v in main_poly.items() if sum(m[:len(witnesses)])==degree}
                require(degree==26,'exact main residual expansion')
        values[name]=(degree,top);producers[name]=(a,b);counts[op]+=1
    live=set();todo=[data['output']]
    while todo:
        n=todo.pop()
        if type(n)==int or n in live:continue
        live.add(n);todo.extend(producers.get(n,()))
    require(live==set(values),'dead gates/ports')
    require(len(data['source'])==79,'79 operations')
    require(values['polynomial'][0]==56,'upper degree')
    q=mul(var('beta'),var('J'));k=add(var('eta'),var('zeta'))
    expected=mul(power(q,28),power(k,4))
    for n,e in [('T',4),('f',8),('w',4),('s',8)]:expected=mul(expected,power(var(n),e))
    require(values['polynomial'][1]==expected,'exact highest homogeneous part')
    require(values['main_residual'][0]==26,'main exact bound')
    binding_path=ROOT/data['coefficient_binding']
    binding=json.loads(binding_path.read_text())
    fixed={}
    for item in binding['ports']:
        packed=(binding_path.parent/item['file']).read_bytes()
        raw=gzip.decompress(packed)
        require(hashlib.sha256(packed).hexdigest()==item['gzip_sha256'],'packed fixed coefficient')
        require(hashlib.sha256(raw).hexdigest()==item['sha256'],'raw fixed coefficient')
        require(len(raw)==item['bytes'],'fixed coefficient size')
        fixed[item['port']]=int.from_bytes(raw,'little')
    require(set(fixed)==set(ports) and fixed['beta']>0,'complete fixed tuple')
    rand=random.Random(14005679)
    formula_checks=0
    for prime in (1009,1000000007):
        for trial in range(16):
            v={name:rand.randrange(prime) for name in witnesses}
            env=dict(v,**{name:value%prime for name,value in fixed.items()})
            for name,op,a,b in data['source']:
                va=a if type(a)==int else env[a];vb=b if type(b)==int else env[b]
                env[name]=(va*vb if op=='*' else va+vb if op=='+' else va-vb)%prime
            q=(fixed['beta']%prime*v['J']+1)%prime;X=v['w']*q;Y=v['s']*q**3;E=X*Y
            k=v['eta']+v['zeta'];c=k*Y+v['eta'];a=E+Y;H=4*a+3;Delta=a*a+H
            C=q-v['F']-v['alpha'];b0=X+a*c
            R=((q-1)*(q-v['F'])+v['alpha'])*(q*q-1)+((fixed['MC']%prime)+q*(fixed['MF']%prime))*v['J']
            V=c*(v['T']*v['f']-1)-R*v['f']**2;I=v['i']*c*c
            Aaux=Delta*(v['f']**2-1);Na=Aaux*(V*V-v['y']**2)+v['y']**2
            N0=v['tau']**2-(X*Y*Y)*(X*Y*Y+1)*k*k
            Nt=((fixed['K0']%prime)+v['w'])*C+q-v['F']-v['z']*(q-1)
            U=4*q**4;r=k-R-1;Ds=U*b0+H*(U*v['gamma']-r)
            displayed=((Ds*Ds-U*U*(1+Delta*c*c))**2+(I*I-Aaux)**2+(Na-1)**2+(N0*Nt-1)**2)%prime
            require(displayed==env['polynomial'],'displayed formula versus literal DAG')
            formula_checks+=1
    result=dict(operations=79,operation_counts=counts,witnesses=14,fixed_ports=4,
        all_gates_and_ports_live=True,degree_upper_bound=56,exact_degree=56,
        highest_homogeneous_form='T^4*f^8*w^4*s^8*(eta+zeta)^4*(beta*J)^28',
        distinguished_coefficient='beta^28',requires='beta != 0',
        main_residual_exact_degree=26,main_residual_full_expansion_terms=len(main_poly),
        fixed_tuple_hashes_verified=True,displayed_formula_checks_at_fixed_port_residues=formula_checks,
        proof_scope='Finite circuit/degree certificate; unbounded semantic adapter is proved separately.',
        sha256=hashlib.sha256(path.read_bytes()).hexdigest())
    (ROOT/'fourteen_audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':audit()
