#!/usr/bin/env python3
"""Independent audit of the v8 and lambda-2048 finalizers.

No construction module is imported.  The only imported code is the independent
source auditor verify.py, for sparse parent arithmetic and primitive DAG replay.
Explicit exceptions make every check effective under Python -O.
"""
from pathlib import Path
import argparse,importlib.util,json,hashlib,random

def need(ok,message):
    if not ok:raise ValueError(message)

class Poly:
    """Tiny exact integer polynomial ring used only for universal identities."""
    width=10
    def __init__(self,x=0):
        self.terms={m:c for m,c in x.items() if c} if isinstance(x,dict) else ({(0,)*self.width:x} if x else {})
    @classmethod
    def var(cls,i):
        e=[0]*cls.width;e[i]=1;return cls({tuple(e):1})
    def __add__(self,other):
        other=other if isinstance(other,Poly) else Poly(other);r=dict(self.terms)
        for m,c in other.terms.items():r[m]=r.get(m,0)+c
        return Poly(r)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.terms.items()})
    def __sub__(self,other):return self+-aspoly(other)
    def __rsub__(self,other):return aspoly(other)+-self
    def __mul__(self,other):
        other=aspoly(other);r={}
        for m,c in self.terms.items():
            for n,d in other.terms.items():
                e=tuple(x+y for x,y in zip(m,n));r[e]=r.get(e,0)+c*d
        return Poly(r)
    __rmul__=__mul__
    def __pow__(self,n):
        need(isinstance(n,int) and n>=0,'polynomial exponent')
        r=Poly(1);b=self
        while n:
            if n&1:r=r*b
            n//=2
            if n:b=b*b
        return r
def aspoly(x):return x if isinstance(x,Poly) else Poly(x)
def ident(a,b,name):need(not (a-b).terms,'universal polynomial identity: '+name)

def symbolic_checks():
    D,A,C,e,i,H,Bgap=[Poly.var(j) for j in range(7)]
    F=(D-1)*e**2*D**2+1
    S=e*(8*D**2-4*D-1)
    gap=e**2*(8*D+1)-64*D
    ident(S**2-64*D*F,gap,'v8 scalar gap')
    G=Poly.var(7);I=(G**2-1)*H**2+1
    ident((S*G*H)**2-64*D*F*I,gap*(G*H)**2+64*D*F*(H**2-1),'v8 full radical gap')

    L=C*D+1-A
    X=e**2*D**3*(D-1)
    G=e**2*D**2*(D-1)*L+C*D+1
    N=2*G+L
    N1=2*e**2*D*(D-1)*L+3*C
    N2=2*e**2*(D-1)*L
    N3=2*e**2*(L-C)
    N4=2*e**2*C
    r1=3-A;r2=3*C*D+3-A;r3=2*e**2*(A-1)*D**2+r2
    r4=2*e**2*(1-A-C)*D**3+r3
    for k,Nk,rk in [(1,N1,r1),(2,N2,r2),(3,N3,r3),(4,N4,r4)]:ident(N,D**k*Nk+rk,f'lambda2048 quotient remainder {k}')
    tn=1024*D**6-512*D**5-128*D**4-64*D**3-40*D**2-28*D-21
    dn=33792*D**5+10560*D**4+4928*D**3+2464*D**2+1176*D+441
    ident(tn**2-1024**2*D**11*(D-1),dn,'lambda2048 square approximant')
    correction=256*i*(e**2+2)+2048
    T=e*((1024*D**2-512*D-128)*N-64*N1-40*N2-28*N3-21*N4)+correction
    Rnum=e*(64*r1*D**3+40*r2*D**2+28*r3*D+21*r4)+correction*D**4
    ident(D**4*T,e*tn*N+Rnum,'lambda2048 polynomial remainder')
    ident(D*F,X+D,'DF relation')
    deltaT8=e**2*dn*N**2+1024**2*D**8*(X*L**2-4*D*G*(C*D+1))+2*e*tn*N*Rnum+Rnum**2
    ident(D**8*(T**2-2048**2*D*F*G**2),deltaT8,'lambda2048 D8 radical gap')
    I=(G**2-1)*H**2+1;V=T*H+Bgap
    deltaV8=H**2*deltaT8+2048**2*D*F*D**8*(H**2-1)+D**8*(2*T*H*Bgap+Bgap**2)
    ident(D**8*(V**2-2048**2*D*F*I),deltaV8,'lambda2048 complete D8 gap')

    D,E0,Omega,h,V,a0,a1=[Poly.var(j) for j in range(7)]
    theta=E0-Omega*h*V
    inner=theta**2-Omega**2*(a0+h**2*a1)
    expanded=E0**2-2*E0*Omega*h*V+Omega**2*h**2*(V**2-a1)-Omega**2*a0
    ident(inner,expanded,'common inner norm expansion')
    inner8=D**8*(E0**2-2*E0*Omega*h*V-Omega**2*a0)+Omega**2*h**2*(D**8*(V**2-a1))
    ident(inner8,D**8*inner,'lambda2048 inner multiplier')
    ident(inner8**2-4*D**16*Omega**4*h**2*a0*a1,D**16*(inner**2-4*Omega**4*h**2*a0*a1),'lambda2048 final D16 multiplier')
    return {'status':'PASS','universal_integer_polynomial_identities':14,'method':'Exact multivariate polynomial expansion; no numerical specialization.'}

def direct_tail(body,values,assignment,prime):
    """Literal mathematical formulas, independent of both construction tails."""
    q={};v=dict(assignment);variant=body['variant']
    if body['domain']=='positive integers':
        for name in ['epsilon','phi','n']:v[name]-=1
    else:
        need(body['domain']=='nonnegative integers','refined domain')
        for name in ['g','h','s','w','i','j']:v[name]+=1
    def put(name,x):q[name]=x%prime;return q[name]
    def source(name):return values[body['named_nodes'][name]]
    b,N,R,cap=source('b'),source('N'),source('X'),source('Gcap')
    U=put('U',N*N*v['w']);Y=put('Y',N*N*v['s']);M=put('M',R*Y)
    P=put('P',2*M*M*U);K=put('K',R+1+v['h']*(P-1));A=put('A',M*(U+1))
    B1=(2*R+1)%prime;W1=b*v['w']%prime
    C=put('C',B1+W1+v['phi']);J=put('J',4*A-5)
    Q=put('Q',3*W1*C-2*(W1*W1-1));D=put('D',(A*A-1)*C*C+1)
    e=put('e',v['i']*J*C);E=put('E',e*D*C)
    F=put('F',(A*A-1)*E*E+1);G=put('G',A+F*(C*D+1-A));H=put('H',B1+v['j']*C)
    I=put('I',(G*G-1)*H*H+1);a0=put('a0',(P*P-1)*K*K+1)
    scale=64 if variant=='v8' else 2048**2
    a1=put('a1',scale*D*F*I);u=put('u',J*F);vc=put('v',Q*F+J*(H-C))
    m=put('m',(K*K-4*(C-K*Y)**2)*cap-8*v['g']*K*K)
    if variant=='v8':
        S=put('Smajor',e*(8*D*D-4*D-1));V=put('Vmajor',S*G*H)
        gap=put('gapDF',e*e*(8*D+1)-64*D)
        delta=put('deltaV',gap*(G*H)**2+64*D*F*(H*H-1))
    else:
        need(variant=='major2048','unknown refined variant')
        L=put('major_L',C*D+1-A);Nstar=put('major_Nstar',2*G+L)
        N1=put('major_N1',2*e*e*D*(D-1)*L+3*C);N2=put('major_N2',2*e*e*(D-1)*L)
        N3=put('major_N3',2*e*e*(L-C));N4=put('major_N4',2*e*e*C)
        correction=put('major_correction',256*v['i']*(e*e+2)+2048)
        T=put('major_T',e*((1024*D*D-512*D-128)*Nstar-64*N1-40*N2-28*N3-21*N4)+correction)
        Bgap=put('major_Bgap',2*P*(P+R)+1);V=put('Vmajor',T*H+Bgap)
        r1=put('major_r1',3-A);r2=put('major_r2',3*C*D+r1);r3=put('major_r3',2*e*e*(A-1)*D*D+r2)
        r4=put('major_r4',2*e*e*(1-A-C)*D**3+r3)
        tn=put('major_tnum',1024*D**6-512*D**5-128*D**4-64*D**3-40*D*D-28*D-21)
        dn=put('major_dnum',33792*D**5+10560*D**4+4928*D**3+2464*D*D+1176*D+441)
        rn=put('major_Rnum',e*(64*r1*D**3+40*r2*D*D+28*r3*D+21*r4)+correction*D**4)
        X=put('major_X',e*e*D**3*(D-1))
        deltaT8=put('deltaT8',e*e*dn*Nstar*Nstar+1024**2*D**8*(X*L*L-4*D*G*(C*D+1))+2*e*tn*Nstar*rn+rn*rn)
        deltaV8=put('deltaV8',H*H*deltaT8+2048**2*D*F*D**8*(H*H-1)+D**8*(2*T*H*Bgap+Bgap*Bgap))
        need(deltaT8==pow(D,8,prime)*(T*T-2048**2*D*F*G*G)%prime,'literal lambda gap formula')
        need(deltaV8==pow(D,8,prime)*(V*V-a1)%prime,'literal lambda full gap formula')
    Md=put('Mdiv',Q+H);Omega=put('Omega',u*m)
    E0=put('E0',u*(v['n']+Md)+vc-2*Omega*Md);Theta=put('Theta',E0-Omega*v['h']*V)
    inner=put('inner',Theta*Theta-Omega*Omega*(a0+v['h']**2*a1))
    out=(inner*inner-4*pow(Omega,4,prime)*v['h']**2*a0*a1)%prime
    if variant=='major2048':
        other=put('inner_other',E0*E0-2*E0*Omega*v['h']*V-Omega*Omega*a0)
        put('inner_D8',pow(D,8,prime)*other+Omega*Omega*v['h']**2*deltaV8)
    for name,x in q.items():
        if name in body['named_nodes']:need(values[body['named_nodes'][name]]==x,f'{variant} direct register formula: {name}')
    if body.get('certificate_form') and variant=='major2048':out=out*pow(D,16,prime)%prime
    need(values[body['output']]==out,f'{variant} direct final polynomial')
    return q

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--root',type=Path,default=Path(__file__).resolve().parent);parser.add_argument('--directory',type=Path,action='append');args=parser.parse_args();root=args.root.resolve()
    spec=importlib.util.spec_from_file_location('independent_source_audit',root/'verify.py');audit=importlib.util.module_from_spec(spec);spec.loader.exec_module(audit);audit.ROOT=root
    symbolic=symbolic_checks();parent,rows=audit.parent();weighted=audit.weighted_terms(rows)
    w=json.loads((root/'data/weights.json').read_text())['weights_in_parent_coordinate_order'];support,pairs=audit.support_check(weighted,w)
    Ds={}
    for name,layout in audit.layouts(max(w)).items():Ds[name],_=audit.source_identity(rows,weighted,w,pairs,layout)
    ports,port_receipts=audit.load_ports();recipes=json.loads((root/'data/coefficient_recipes.json').read_text());primes=[1000003,1000033,1000000007]
    reduced_ports={p:[x%p for x in ports] for p in primes};fixed={p:audit.fixed_values(recipes,reduced_ports[p],p) for p in primes}
    directories=args.directory or [root/'refined',root/'majorant'];files=[]
    for directory in directories:
        if directory.is_dir():files.extend(sorted(directory.rglob('*.json')))
    docs={}
    for path in files:
        d=json.loads(path.read_text())
        if isinstance(d,dict) and 'nodes'in d and d.get('variant') in ('v8','major2048'):docs[path]=d
    need(bool(docs),'no refined polynomial circuits found');rng=random.Random(2048179);receipts=[]
    for path,body in docs.items():
        variant=body['variant'];layout=body['layout'];certificate=bool(body.get('certificate_form'));W=max(w);t=3*(body['targets'][-1]+3*W+2)
        need(body['weights']==w and body['targets']==audit.layouts(W)[layout]['targets'],'refined source binding')
        expected_primary=(964*t+12*W+240) if variant=='v8' else (820*t+12*W+208)
        expected_certificate=expected_primary if variant=='v8' else (1140*t+12*W+272)
        records=[]
        for prime in primes:
            for trial in range(4):
                assignment={name:rng.randrange(-3,45) for name in body['variables']}
                if trial==0:assignment={name:1 for name in body['variables']}
                values,degrees,leads=audit.dag_check(body,fixed[prime],assignment,prime)
                audit.source_modular_check(body,values,Ds[layout],reduced_ports[prime],assignment,prime)
                q=direct_tail(body,values,assignment,prime)
                if trial==0:
                    Dnode=body['named_nodes']['D'];need(degrees[Dnode]==20*t+4 and leads[Dnode]==pow(2,34,prime),'exact D degree/leading coefficient')
                    if certificate:
                        expected_lc=pow(2,1730,prime) if variant=='v8' else 3*pow(2,2038,prime)%prime
                        need(degrees[body['output']]==expected_certificate and leads[body['output']]==expected_lc and expected_lc!=0,'refined exact certificate degree')
                    records.append({'prime':prime,'propagated_degree':degrees[body['output']],'coefficient_at_degree':leads[body['output']],'D_degree':degrees[Dnode],'D_leading_coefficient':leads[Dnode]})
        if not certificate:
            need(body.get('exact_degree')==expected_primary,'primary degree claim')
            companion=path.with_name(path.stem+'_degree_certificate.json');need(companion in docs,'missing certificate circuit');cert=docs[companion]
            power=0 if variant=='v8' else 16
            need(cert.get('certificate_multiplier')=={'register':'D','exponent':power},'certificate multiplier metadata')
            for prime in primes:
                assignment={name:rng.randrange(-10,100) for name in body['variables']};pv,_,_=audit.dag_check(body,fixed[prime],assignment,prime);cv,_,_=audit.dag_check(cert,fixed[prime],assignment,prime)
                need(cv[cert['output']]==pv[body['output']]*pow(pv[body['named_nodes']['D']],power,prime)%prime,'primary/certificate multiplier agreement')
            need(expected_certificate-power*(20*t+4)==expected_primary,'degree cancellation arithmetic')
        receipts.append({'file':str(path.relative_to(root)) if path.is_relative_to(root) else path.name,'variant':variant,'domain':body['domain'],'layout':layout,'certificate':certificate,'operations':body['total_operations'],'certified_primary_degree':expected_primary,'degree_receipts':records,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()})
    result={'status':'PASS','scope':'Exact universal ring identities and finite circuit/data audits, not an unbounded consistency proof.','symbolic_identities':symbolic,'source_support':support,'port_bindings':port_receipts,'circuit_count':len(receipts),'direct_formula_fixtures':len(receipts)*len(primes)*4,'circuits':receipts,'optimized_python_safe':True}
    (root/'REFINED_VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'PASS','circuits':len(receipts),'direct_formula_fixtures':result['direct_formula_fixtures'],'universal_ring_identities':symbolic['universal_integer_polynomial_identities']},indent=2))
if __name__=='__main__':main()
