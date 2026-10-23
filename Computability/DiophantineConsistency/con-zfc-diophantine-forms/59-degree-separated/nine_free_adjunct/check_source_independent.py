#!/usr/bin/env python3
"""Independent AI-assisted source and circuit review checks. Imports no construction/audit module.
Exact local identities and actual-tuple modular leading-coefficient certificates.
"""
from pathlib import Path
from collections import defaultdict, Counter
from itertools import product
import gzip, hashlib, json
R=Path(__file__).resolve().parent

def require(ok,msg):
    if not ok:raise RuntimeError(msg)

class Poly:
    def __init__(self,x=0):self.t=({():x} if x else {}) if isinstance(x,int) else {m:c for m,c in x.items() if c}
    @staticmethod
    def var(n):return Poly({((n,1),):1})
    def __add__(self,o):
        o=poly(o);d=dict(self.t)
        for m,c in o.t.items():d[m]=d.get(m,0)+c
        return Poly(d)
    __radd__=__add__
    def __neg__(self):return Poly({m:-c for m,c in self.t.items()})
    def __sub__(self,o):return self+-poly(o)
    def __rsub__(self,o):return poly(o)+-self
    def __mul__(self,o):
        o=poly(o);d=defaultdict(int)
        for m,c in self.t.items():
            for n,e in o.t.items():
                powers=dict(m)
                for v,k in n:powers[v]=powers.get(v,0)+k
                d[tuple(sorted(powers.items()))]+=c*e
        return Poly(dict(d))
    __rmul__=__mul__
    def __pow__(self,n):
        r=Poly(1);a=self
        while n:
            if n&1:r=r*a
            n//=2
            if n:a=a*a
        return r
    def __eq__(self,o):return self.t==poly(o).t
    def names(self):return {v for m in self.t for v,e in m}

def poly(x):return x if isinstance(x,Poly) else Poly(x)

def identities():
    D,k,G,H,K,P,E0,Om,V0,V1,a0,a1=[Poly.var(s) for s in ('D','k','G','H','K','P','E0','Om','V0','V1','a0','a1')]
    F=k*k*D*D*(D-1)+1; I=(G*G-1)*H*H+1; T=k*(8*D*D-4*D-1)
    defect=(8*D+1)*k*k-64*D
    require(T*T-64*D*F==defect,'Pell pair defect')
    delta=defect*G*G*H*H+64*D*F*(H*H-1)
    require((T*G*H)**2-64*D*F*I==delta,'full root defect')
    require((E0-Om*(V0+V1))**2-Om**2*(a0+64*a1)==
            E0**2-2*E0*Om*(V0+V1)+Om**2*(V0**2-a0+V1**2-64*a1+2*V0*V1),'cancelled inner identity')
    x,u,v=[Poly.var(s) for s in ('x','u','v')]
    fact=Poly(1)
    for es,ds in product((-1,1),repeat=2):fact*=x+es*u+ds*v
    require(fact==(x*x-u*u-v*v)**2-4*u*u*v*v,'real four-factor norm')
    A,C,J,i=[Poly.var(s) for s in ('A','C','J','i')]
    dd=(A*A-1)*C*C+1;kk=i*J*C;ee=kk*dd*C;ff=(A*A-1)*ee*ee+1
    require(ff==kk*kk*dd*dd*(dd-1)+1,'DF support substitution')
    return {'status':'PASS','exact_universal_polynomial_identities':5}

def leading_audit():
    path=R/'generated/split_116_positive_certificate.json';body=json.loads(path.read_text())
    manifest=json.loads((R/'coefficients/old_tuple/COEFFICIENT_BINDING.json').read_text());ports={}
    for row in manifest['payloads']:
        data=gzip.decompress((R/'coefficients/old_tuple'/Path(row['path']).name).read_bytes())
        require(hashlib.sha256(data).hexdigest()==row['sha256'],'actual port hash')
        ports[row['name']]=int.from_bytes(data,'little')
    ports={key:ports[val] for key,val in manifest['port_aliases'].items()}
    results=[]
    for p in (101,1009,1000003):
        require(all(p%d for d in range(2,int(p**0.5)+1)),'prime modulus')
        fv={'base_scale':pow(2,body['base_scale_exponent'],p),'threshold_scale':pow(2,body['threshold_scale_exponent'],p)}
        for rec in body['coefficient_recipes']:
            value=0
            for term in rec['terms']:
                x=term['coefficient']
                for name,ex in zip(('beta','K0','MC','MF'),term['powers']):x=x*pow(ports[name],ex,p)%p
                value=(value+x)%p
            fv[rec['name']]=value
        degree=[];head=[]
        for i,node in enumerate(body['nodes']):
            kind=node['kind']
            if kind=='variable':d,h=1,1
            elif kind=='literal':d,h=0,node['value']%p
            elif kind=='fixed':d,h=0,fv[node['name']]
            else:
                a,b=node['left'],node['right'];require(a<i and b<i,'topological order')
                if kind=='mul':d,h=degree[a]+degree[b],head[a]*head[b]%p
                else:
                    d=max(degree[a],degree[b]);h=((head[a] if degree[a]==d else 0)+(1 if kind=='add' else -1)*(head[b] if degree[b]==d else 0))%p
            degree.append(d);head.append(h)
        require(degree[body['output']]==1910404 and head[body['output']]!=0,'exact final degree')
        promised=pow(2,186,p)*pow(fv['base_scale'],954792,p)*pow(fv['threshold_scale'],400,p)%p
        require(head[body['output']]==promised,'stated symbolic diagonal head')
        results.append({'prime':p,'leading_coefficient':head[body['output']]})
    principal=json.loads((R/'generated/split_116_positive.json').read_text())
    require(principal['domain']=='positive integers' and principal['variables']==['b','g','h','s','w','C','i','j','n'],'principal domain and inputs')
    live=set(); todo=[principal['output']]
    while todo:
        idx=todo.pop()
        if idx in live:continue
        live.add(idx); node=principal['nodes'][idx]
        if 'left' in node:
            require(node['left']<idx and node['right']<idx,'principal topological order')
            todo.extend([node['left'],node['right']])
    require(live==set(range(len(principal['nodes']))),'principal dead gate')
    counts=dict(Counter(n['kind'] for n in principal['nodes'] if 'left' in n))
    require(sum(counts.values())==473 and counts==principal['operation_counts'],'primary gate ledger')
    return {'status':'PASS','exact_degree':1910404,'certificate_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),
            'certificates':results,'symbolic_leader':'2^186 * base_scale^954792 * threshold_scale^400',
            'principal_gate_counts':counts,'principal_total_operations':sum(counts.values())}


def register_audit():
    files=['split_116_positive.json','split_116_positive_certificate.json'];total=0
    p=Poly.var
    for filename in files:
        body=json.loads((R/'generated'/filename).read_text());named=body['named_nodes'];nodes=body['nodes']
        fixed={}
        for rec in body['coefficient_recipes']:
            expr=Poly(0)
            for term in rec['terms']:
                val=Poly(term['coefficient'])
                for port,ex in zip(('beta','K0','MC','MF'),term['powers']):val*=p(port)**ex
                expr+=val
            fixed[rec['name']]=expr
        layout=json.loads((R/'data/split_code.json').read_text());kernels=json.loads((R/'data/split_kernels.json').read_text())
        ex={
            'b':p('b'),'B':p('base_scale')*p('b')**2,
            'ell':sum(p('B')**e for e in layout['weights']),
            'targets':sum(p('B')**e for e in layout['targets']),
            'N0':p('B')**117,'mask':p('N0')-1-(p('b')-1)*p('ell'),
            'Tcode':p('mask')+(p('B')-2)*p('targets')*p('N0'),
            'Usource':p('ell')+p('g'),
            'Gsource':p('D2')*p('Usource')**2+p('D1')*p('Usource')+p('D0'),
            'Jcode':2*p('Gsource')+p('targets'),'Scode':p('g')+p('Jcode')*p('N0'),
            'L':p('b')*p('B')**2279,'N':p('threshold_scale')*p('b')*p('B')**1201,
            'R':(p('Scode')+p('Tcode'))*p('L')+p('L')-1-p('Scode'),
            'capbase':p('b')*p('B')**116,'Gcap':32*p('capbase'),
            'U':p('N')**2*p('w'),'Y':p('N')**2*p('s'),'M':p('R')*p('Y'),
            'P':2*p('M')**2*p('U'),'K':p('R')+1+p('h')*(p('P')-1),
            'A':p('M')*(p('U')+1),'B1':2*p('R')+1,'W1':p('b')*p('w'),
            'C':p('C'),'J':4*p('A')-5,
            'Q':3*p('W1')*p('C')-2*(p('W1')**2-1),
            'D':(p('A')**2-1)*p('C')**2+1,'k':p('i')*p('J')*p('C'),
            'E':p('k')*p('D')*p('C'),'F':(p('A')**2-1)*p('E')**2+1,
            'G':p('A')+p('F')*(p('C')*p('D')+1-p('A')),
            'H':p('C')+p('F')*(p('B1')+(p('j')-1)*p('C')),
            'GH':p('G')*p('H'),'I':p('GH')**2-p('H')**2+1,
            'V0':p('P')*p('K'),'a0':p('V0')**2-p('K')**2+1,'a1':p('D')*p('F')*p('I'),
            'margin':p('K')**2*(4*p('capbase')-p('g'))-16*p('capbase')*(p('C')-p('K')*p('Y'))**2,
            'Tpair':p('k')*(8*p('D')**2-4*p('D')-1),'V1':p('Tpair')*p('GH'),
            'Omega':p('J')*p('margin'),'E0':p('J')*(p('n')+p('W1')**2)+p('Q'),
            'Theta':p('E0')-p('Omega')*(p('V0')+p('V1')),
            'F9':p('inner')**2-256*p('Omega')**4*p('a0')*p('a1')}
        for degree,kernel in enumerate(kernels['kernels']):
            expr=Poly(0)
            for term in kernel['terms']:
                coefficient=Poly(0)
                for co in term['coefficient']:
                    v=Poly(co['coefficient'])
                    for port,e in zip(('beta','K0','MC','MF'),co['powers']):v*=p(port)**e
                    coefficient+=v
                expr+=coefficient*p('B')**term['exponent']
            ex['D'+str(degree)]=expr
        if body['degree_certificate_form']:
            ex.update(dferror=(8*p('D')+1)*p('k')**2-64*p('D'),
                      Delta1=p('dferror')*p('GH')**2+64*p('D')*p('F')*(p('H')**2-1),
                      inner=p('E0')**2-2*p('E0')*p('Omega')*(p('V0')+p('V1'))+p('Omega')**2*(p('K')**2-1+p('Delta1')+2*p('V0')*p('V1')))
        else:ex['inner']=p('Theta')**2-p('Omega')**2*(p('a0')+64*p('a1'))
        require(set(named)<=set(ex),'unexpected named register')
        for name in named:
            wanted=ex[name];stops={named[v]:p(v) for v in wanted.names() if v in named and v!=name};memo={}
            def run(i):
                if i in stops:return stops[i]
                if i in memo:return memo[i]
                node=nodes[i];kind=node['kind']
                if kind=='literal':out=Poly(node['value'])
                elif kind=='variable':out=p(node['name'])
                elif kind=='fixed':out=fixed.get(node['name'],p(node['name']))
                else:
                    a,b=run(node['left']),run(node['right']);out=a+b if kind=='add' else a-b if kind=='sub' else a*b
                memo[i]=out;return out
            require(run(named[name])==wanted,'literal register polynomial '+filename+' '+name);total+=1
    return {'status':'PASS','exact_local_register_identities':total,'circuits':files,
            'primary_certificate_equivalence':'Shared source/ratio registers agree with literal formulas; five universal identities establish the changed final expression.'}

def source_calibration():
    from fractions import Fraction as F
    import math
    data=json.loads((R/'data/split_code.json').read_text())
    kernels=json.loads((R/'data/split_kernels.json').read_text())
    require(hashlib.sha256((R/'data/split_code.json').read_bytes()).hexdigest()=='abbedad94a3e619d71d61551c9cd76db5dd9ec35e67bd8382a18deb90fb8f38e','frozen split layout')
    require(hashlib.sha256((R/'data/split_kernels.json').read_bytes()).hexdigest()=='445de50798fe3c22a195d9e643b5684f0224c7130b56a316bcb29681a58dd02a','frozen split kernels')
    # In the worst b=1,M=1 case, B/(B-1)<=4096/4095.
    require(F(86,4096)*F(4096,4095)<F(1,32),'four-base-word range source constant')
    require(F(993,4096)<F(1,4),'signed coefficient bound')
    require(F(3,64)+F(1,64)+F(2,64)<1,'source block bound with Z>64')
    require(2*17079501+2*1201*2134939==2418*2134939-22,'threshold fixed exponent')
    require(2+4*1201==2*2418-30,'threshold variable exponent')
    require(1929+116-2027==18 and 1929+2*116-1719==442,'unconditional source dominance gaps')
    cases=0
    for u in range(1,9):
        L=1<<u
        for S in range(L):
            for T in range(L-S):
                rank=(S+T)*L+L-1-S
                carry=S.bit_count()+T.bit_count()-(S+T).bit_count()
                require(rank.bit_count()==u+T.bit_count()-carry,'top-bit-free population identity')
                require((carry==0)==((S&T)==0),'no-carry condition')
                cases+=1
    maskcases=0
    for k in range(6):
        b=1<<k;nu=8+2*k;B=1<<nu;N0=B**117
        ell=sum(B**e for e in data['weights']);targets=sum(B**e for e in data['targets'])
        mask=N0-1-(b-1)*ell;Tc=mask+N0*(B-2)*targets
        require(mask.bit_count()==117*nu-31*k,'low mask population including b=1')
        require(Tc.bit_count()==139*nu-31*k-22,'full mask population including b=1')
        maskcases+=1
    stresses=0
    for ports in [(3,5,2,4),(31,127,10,45)]:
        scalar=[[(r['exponent'],sum(t['coefficient']*math.prod(p**e for p,e in zip(ports,t['powers']))for t in r['coefficient']))for r in kernel['terms']]for kernel in kernels['kernels']]
        M=1+max(abs(c)for kernel in scalar for e,c in kernel)
        for b in [1,2,3,4,8]:
            B=4096*M*b*b;N0=B**117;Z=B**2162;L=b*B**2279
            ell=sum(B**e for e in data['weights']);targets=sum(B**e for e in data['targets'])
            D0,D1,D2=[sum(c*B**e for e,c in kernel)for kernel in scalar]
            mask=N0-1-(b-1)*ell;Tc=mask+N0*(B-2)*targets
            require(0<=mask<N0 and Tc>0,'unconditional mask positivity')
            cap=4*b*B**116
            for g in [1,b*B**116,cap-1,cap,cap*cap]:
                U=ell+g;Gs=D2*U*U+D1*U+D0;J=2*Gs+targets;S=g+N0*J
                require(4*Gs>B**1929*U*U and S>0,'unconditional positive packed source')
                rank=(S+Tc)*L+L-1-S
                require(rank>=L-1>=8 and rank>=b,'unconditional rank contract')
                if g<cap:
                    require(U<6*b*B**116,'correct g<4b branch bound')
                    require(32*2*Gs<Z and 64*targets<Z and 64*(B-2)*targets<Z,'bounded source constants')
                    require(S+Tc<B**2279<=L,'halved-block separation')
                    if b==1:require((g&mask)!=0,'excluded b=1 mask branch')
                stresses+=1
    return {'status':'PASS','exact_threshold_identity':True,'top_bit_free_population_cases':cases,'mask_population_cases_including_b1':maskcases,'source_bound_stress_cases':stresses,'uses_correct_soundness_range':'0<g<4b B^116; U_source<6b B^116'}

result={'status':'PASS','source_calibration':source_calibration(),'universal_identities':identities(),'registers':register_audit(),'independent_degree':leading_audit(),
        'mathematical_review':'INDEPENDENT_SOURCE_REVIEW.md','scope':'Independent mathematical review and checks; no builder/auditor imports; inherited compiler/Jones contracts not re-proved.'}
(R/'INDEPENDENT_SOURCE_CHECK.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
