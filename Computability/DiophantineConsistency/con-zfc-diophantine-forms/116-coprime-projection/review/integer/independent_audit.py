#!/usr/bin/env python3
"""Independent equation audit. Exact algebra and source checks are separate
from deliberately labelled finite formula diagnostics. Standard library only.
"""
import gzip, hashlib, itertools, json, os, random, subprocess, sys
from collections import Counter
from pathlib import Path
BASE=Path(__file__).resolve().parents[2]
ROOT=BASE/'integer'
sys.path.insert(0,str(ROOT))
from exact_polynomial import Ring
from audit_support import coefficients

def check(b,msg):
    if not b: raise RuntimeError(msg)

def poly_norm_checks():
    ring=Ring(['x','r','s','t','u'])
    x,r,s,t,u=[ring.var(n) for n in ring.names]
    a,b,c=r*r,s*s,t*t
    z=(x*x-a-b-c)**2-4*(a*b+a*c+b*c)
    f3=z*z-64*a*b*c*x*x
    prod=ring.scalar(1)
    for signs in itertools.product([-1,1],repeat=3):
        prod*=x-signs[0]*r-signs[1]*s-signs[2]*t
    check(not (prod-f3).terms,'universal three-root coefficient identity')
    # Independent direct substitution into the displayed fourth quadratic norm.
    e=u*u
    t20=x*x+e;t21=-2*x
    q0=t20-a-b-c;q1=t21
    v0=q0*q0+e*q1*q1-4*(a*b+c*(a+b));v1=2*q0*q1
    n0=v0*v0+e*v1*v1-64*a*b*c*t20
    n1=2*v0*v1-64*a*b*c*t21
    f4=n0*n0-e*n1*n1
    prod4=ring.scalar(1)
    for signs in itertools.product([-1,1],repeat=4):
        prod4*=x-signs[0]*r-signs[1]*s-signs[2]*t-signs[3]*u
    check(not (prod4-f4).terms,'universal four-root coefficient identity')
    ring2=Ring(['Q','V','S','W'])
    Q,V,S,W=[ring2.var(n) for n in ring2.names]
    check(not (((W+S*(2*Q-1)*V)**2-4*S*S*(Q-1)*(Q*V*V-1))-
        (W*W+2*W*S*(2*Q-1)*V+S*S*(V*V+4*(Q-1)))).terms,
        'universal centering identity')
    ring3=Ring(['X','a','c'])
    X,a,c=[ring3.var(n) for n in ring3.names]
    check(not (X*(3*c-2*X)+2-((4*a+3)*X*c-2*(X*(X+2*a*c)-1))).terms,'short projection identity')
    return {'three_root_exact_coefficients':len(f3.terms),'four_root_exact_coefficients':len(f4.terms),'centering_identity':True,'short_projection_identity':True}

def independent_values(inp,co,p):
    # Independently transcribed equations; all arithmetic here is ordinary
    # integers, reduced only in comparisons with the literal DAG.
    j,C,z,h,r,v,w,T,c,n,s=[inp[n] for n in ['j','C','z','h','r','v','w','T','c','n','s']]
    beta,K0,MC,MF,cone_A,cone_B=[co[n] for n in ['beta','K0','MC','MF','cone_A','cone_B']]
    J=6*j+1;qm=beta*J;q=qm+1;q2=q*q;q3=q*q*q;W=12*w+4
    X=q*W;Y=(2*v+1)*q**3;E=X*Y;a=(X+1)*Y;H=4*a+3;Delta=(a+2)**2-1
    F=(K0+W)*C-z*(q-1)
    R=(q*q-q*F-C)*(q*q-1)+(MC+q*MF)*J
    k=R+1+h*X*Y;c2=c*c;eta=c-Y*k
    U=cone_A*F;Vc=cone_B*C;Derr=(U-q)**2+(Vc-q)**2
    Budget=k*k*(q*q-Derr)-4*q*q*(c-Y*k)**2
    ell=X*Y*Y;L=ell*k;Dt=1+ell*(ell+1)*k*k;D=3*Budget-4;s2=2*s
    Dg=1+4*D*s*s*(Dt if p['fused'] or p['guard_fused'] else 1)
    Amain=a+2;Dm=1+Delta*c*c;I=2*s*r*c*c
    if p['fused']:I*=Dt*Dg*Dm*Amain
    I2=I*I;strong=Delta*I2;Df=1+Delta*I*I;Q=Delta*Delta*I*I;delta=Q-1
    b=c-R+4*I*T;V=Df*b-c;Cy=Q*V*V-1;Da=(Q-1)*Cy
    K=X*(3*c-2*X)+2;H2=H*H;H3=H**3;H5=H**5;S=I*H**5;S2=S*S
    zc=H*T+K;zc2=zc*zc;Ac=zc**5+3*H*H*zc**3-19*H**3*zc**2-57*H**5
    shift=0 if p['center']=='direct' else (2*Q-1)*V
    if p['center']=='both':shift+=4*L
    if p['fused']:
        Z=S*n-Ac;product=Df*Dt*Dg
        output=delta*Z*Z-S*S*Df*Dt*Dg*Cy if p['rational'] else Z*Z-S*S*Df*Dt*Dg*Da
    elif p['guard_fused']:
        Z=S*(n+shift)-Ac;P=Dt*Dg;ra=S*S*Df;rb=4*S*S*Da;rc=16*S*S*P
        Z2=Z*Z;ab=ra+rb;arb=ra*rb;vnorm=Z2-ra-rb-rc
        ynorm=vnorm*vnorm-4*(ra*rb+ra*rc+rb*rc)
        output=ynorm*ynorm-64*ra*rb*rc*Z*Z
    else:
        Z=S*(n+shift)-Ac;ra=S*S*Df;rb=16*S*S*Dt;re=64*S*S*Dg;rc=4*S*S*Da
        # Product in a four-generator quadratic algebra, independent of
        # the recursive squaring implementation in build.py.
        def mul(A,B):
            out={};rs=[ra,rb,re,rc]
            for i,x0 in A.items():
                for j,y0 in B.items():
                    val=x0*y0;common=i&j
                    for k0 in range(4):
                        if common&(1<<k0):val*=rs[k0]
                    out[i^j]=(out.get(i^j,0)+val)%modulus
            return {i:x0 for i,x0 in out.items() if x0}
        prod={0:1}
        for eps in itertools.product([-1,1],repeat=4):
            prod=mul(prod,{0:Z%modulus,**{1<<i:-eps[i] for i in range(4)}})
        check(not any(i for i in prod),'formal radical cancellation diagnostic')
        output=prod.get(0,0)
    return {key:value for key,value in locals().items() if isinstance(value,int)}

def check_literals(actual):
    rng=random.Random(2402026);report=[]
    global modulus
    for path in sorted(ROOT.glob('*11_*.json')):
        p=json.loads(path.read_text());nodes=p['nodes'];seen=[]
        counts=Counter();used=set();ports=set()
        for i,row in enumerate(nodes):
            if row[0] in ['add','sub','mul']:
                check(len(row)==3 and 0<=row[1]<i and 0<=row[2]<i,'topology');counts[row[0]]+=1
            elif row[0]=='variable':used.add(row[1])
            elif row[0]=='coefficient':ports.add(row[1])
            else:check(row[0]=='integer' and isinstance(row[1],int),'leaf type')
        live=set()
        def visit(i):
            if i in live:return
            live.add(i)
            row=nodes[i]
            if row[0] in ['add','sub','mul']:visit(row[1]);visit(row[2])
        visit(p['output'])
        check(len(live)==len(nodes),'all nodes live')
        check(used==set(p['variables']) and len(used)==11,'variable closure')
        check(ports==set(actual),'coefficient closure')
        check(dict(counts)==p['operation_counts'] and sum(counts.values())==p['operations'],'operation count')
        tests=0;comparisons=0
        for modulus in [101,1009,65537]:
            for trial in range(9):
                co={k:v%modulus for k,v in actual.items()} if trial%2 else {k:rng.randrange(1,modulus) for k in actual}
                inp={k:rng.randrange(-3,4) for k in p['variables']}
                expect=independent_values(inp,co,p);vals=[]
                for row in nodes:
                    op=row[0]
                    if op=='variable':v=inp[row[1]]
                    elif op=='coefficient':v=co[row[1]]
                    elif op=='integer':v=row[1]
                    elif op=='add':v=vals[row[1]]+vals[row[2]]
                    elif op=='sub':v=vals[row[1]]-vals[row[2]]
                    else:v=vals[row[1]]*vals[row[2]]
                    vals.append(v%modulus)
                for name,idx in p['named_registers'].items():
                    check(name in expect,'missing transcribed register '+name)
                    check(vals[idx]==expect[name]%modulus,path.name+': register '+name)
                    comparisons+=1
                check(vals[p['output']]==expect['output']%modulus,'literal output');tests+=1
        report.append({'file':path.name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'operations':p['operations'],'variable_count':11,'finite_assignment_checks':tests,'finite_register_comparisons':comparisons})
    return report

def source_checks():
    folder=ROOT/'source/provenance/rootfusion/upstream_ordinary'
    ledger=json.loads((folder/'SOURCES.json').read_text());records=[]
    repo=BASE/'baseline/ProveIt'
    for item in ledger['sources']:
        blob=(folder/item['file']).read_bytes()
        check(hashlib.sha256(blob).hexdigest()==item['sha256'] and len(blob)==item['bytes'],'source ledger binding '+item['file'])
        git_identity='not rerun: optional baseline Git clone absent'
        if (repo/'.git').exists():
            obj=subprocess.run(['git','-C',str(repo),'show',item['commit']+':'+item['path']],capture_output=True,env={**os.environ,'GIT_NO_LAZY_FETCH':'1'})
            check(obj.returncode==0,'pinned source object unavailable '+item['file'])
            check(obj.stdout==blob,'source git byte identity '+item['file'])
            git_identity=True
        records.append({'file':item['file'],'commit':item['commit'],'sha256':item['sha256'],'local_digest_and_size':True,'git_byte_identity':git_identity})
    return records

def exact_circuit_core():
    results=[]
    for path in sorted(ROOT.glob('*11_*.json')):
        packet=json.loads(path.read_text());regs=packet['named_registers']
        names=['Z','S','Df','Dt','Dg',('Cy' if packet['rational'] else 'Da')]
        if packet['rational']:names.append('delta')
        if not packet['fused']:names=['Z','ra','rb','rc']
        ring=Ring(names);symbols={n:ring.var(n) for n in names}
        cuts={regs[n]:symbols[n] for n in names};cache={}
        def at(i):
            if i in cuts:return cuts[i]
            if i in cache:return cache[i]
            row=packet['nodes'][i];op=row[0]
            if op=='integer':value=ring.scalar(row[1])
            elif op=='add':value=at(row[1])+at(row[2])
            elif op=='sub':value=at(row[1])-at(row[2])
            elif op=='mul':value=at(row[1])*at(row[2])
            else:raise RuntimeError('core cut escaped: '+str(row))
            cache[i]=value;return value
        z=symbols['Z']
        if not packet['fused']:
            a,b,c=[symbols[n] for n in ['ra','rb','rc']]
            expected=((z*z-a-b-c)**2-4*(a*b+b*c+c*a))**2-64*a*b*c*z*z
        else:
            S,F,T,G=[symbols[n] for n in ['S','Df','Dt','Dg']]
            expected=(symbols['delta']*z*z-S*S*F*T*G*symbols['Cy'] if packet['rational'] else z*z-S*S*F*T*G*symbols['Da'])
        exact=at(packet['output'])
        check(not (exact-expected).terms,'literal core universal identity: '+path.name)
        results.append({'file':path.name,'free_registers':names,'exact_coefficients':len(exact.terms),'universal_literal_core_identity':True})
    return results

def leading_certificates():
    names=['beta','j','C','z','h','r','v','w','T','c','n','s']
    ring=Ring(names);v={n:ring.var(n) for n in names};weights=[0]+[1]*11
    beta,j,C,z,h,r,vv,w,T,c,n,s=[v[n] for n in names]
    q=6*beta*j;Y=2*vv*q**3;a=12*w*q*Y
    I=2*s*r*c*c;R=-q**3*(12*w*C-z*q);baux=4*I*T-R
    Dt=h*h*a**4*Y*Y
    Dg=-48*q*q*Y**4*h**4*a**6*s*s
    P=Dt*Dg
    S=(4*a)**5*I
    rb=4*S*S*a**12*I**8*baux*baux
    rc=16*S*S*P
    direct=rb**4;centered=16*rb*rb*rc*rc
    If=I*P*a**3*c*c
    rational=-2**24*a**20*If**12*P*T*T
    integral=rational*a**4*If*If
    specifications=[
       ('guard_fused11_direct',728,direct,{'beta':352,'j':352,'w':88,'v':88,'s':48,'r':48,'c':96,'T':8},768,440),
       ('guard_fused11_aux',688,centered,{'beta':376,'j':376,'w':84,'v':96,'s':32,'r':28,'c':56,'h':12,'T':4},780,462),
       ('fused11_rational',1632,rational,{'beta':1004,'j':1004,'w':186,'v':264,'s':38,'r':12,'c':48,'h':78,'T':2},1728,1203),
       ('fused11_integral',1892,integral,{'beta':1164,'j':1164,'w':216,'v':306,'s':44,'r':14,'c':56,'h':90,'T':2},2000,1395)]
    results=[]
    for name,degree,poly,exps,p2,p3 in specifications:
        check(poly.weighted_degree(weights)==degree,'homogeneous degree '+name)
        monomial=tuple(exps.get(n,0) for n in names)
        check(poly.terms.get(monomial)==2**p2*3**p3,'selected exact leading coefficient '+name)
        results.append({'name':name,'exact_degree':degree,'selected_monomial':{n:e for n,e in exps.items() if n!='beta'},'coefficient':'2^'+str(p2)+' * 3^'+str(p3)+' * beta^'+str(exps['beta']),'leading_form_term_count':len(poly.terms)})
    return results

def main():
    vals,co_report=coefficients(ROOT)
    out={'scope':'Independent ordinary mathematical review plus separate exact symbolic identities, full coefficient reconstruction, source binding, and finite literal diagnostics. Not a proof-assistant certificate.','exact_algebra':poly_norm_checks(),'universal_literal_core':exact_circuit_core(),'exact_leading_coefficients':leading_certificates(),'coefficients':co_report,'literal_diagnostics':check_literals(vals),'source_git_checks':source_checks()}
    (Path(__file__).parent/'AUDIT_RESULTS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
