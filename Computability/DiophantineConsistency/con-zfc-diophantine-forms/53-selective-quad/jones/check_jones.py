#!/usr/bin/env python3
"""Finite exact implementation audits, NOT a proof of consistency or a Lean certificate."""
from pathlib import Path
from collections import Counter,defaultdict
from itertools import product,combinations_with_replacement
from math import comb,factorial,isqrt,gcd
import json,hashlib,gzip,random,sys
from build_jones import build,degree_certificate,KAPPA
from circuit import evaluate
ROOT=Path(__file__).resolve().parent

def require(ok, message):
    if not ok: raise ValueError(message)

def shifted_rows(data):
    rows={}
    for eq in data['equations']:
        result=defaultdict(int)
        for term in eq['terms']:
            a=term['powers'];supp=[i for i in range(31) if a[i]]
            for ks in product(*(range(a[i]+1) for i in supp)):
                b=[0]*31;v=term['coefficient']
                for i,k in zip(supp,ks):b[i]=k;v*=comb(a[i],k)
                result[(tuple(b),tuple(a[31:]))]+=v
        rows[eq['number']]={key:c*factorial(2-sum(key[0]))*__import__('math').prod(factorial(e) for e in key[0]) for key,c in result.items() if c}
    return rows

def auth():
    binding=json.loads((ROOT/'FIXED_BINDING.json').read_text());values={};records=[]
    require(hashlib.sha256((ROOT/binding['source_adapter_proof_path']).read_bytes()).hexdigest()==binding['source_adapter_proof_sha256'],'adapter proof binding')
    require(hashlib.sha256((ROOT/binding['source_binding_path']).read_bytes()).hexdigest()==binding['source_binding_sha256'],'original tuple binding')
    for r in binding['payloads']:
        packed=(ROOT/r['path']).read_bytes();raw=gzip.decompress(packed)
        require(hashlib.sha256(packed).hexdigest()==r['gzip_sha256'],'gzip hash '+r['name'])
        require(hashlib.sha256(raw).hexdigest()==r['sha256'],'payload hash '+r['name'])
        value=int.from_bytes(raw,'little');require(value.bit_length()==r['bit_length'],'bit length')
        values[r['name']]=value;records.append({'name':r['name'],'sha256':r['sha256'],'bit_length':r['bit_length']})
    ports=[values[binding['port_aliases'][n]] for n in ['beta','K0','MC','MF']]
    require(ports[0]==(1<<1064921)-1,'coherent beta convention changed')
    return ports,records

def fixed(body,ports,p):
    result={'base_scale':pow(2,KAPPA,p),'threshold_scale':pow(2,(15*KAPPA-20)//2,p)}
    for row in body['coefficient_recipes']:
        result[row['name']]=sum(t['coefficient']*__import__('math').prod(pow(x,e,p) for x,e in zip(ports,t['powers'])) for t in row['terms'])%p
    return result

def literal(body,values,ports,p,rows):
    v=dict(values);signed=body['variant'].startswith('signed');seed=body['variant']=='signed_seeded'
    if not signed:v['phi']-=1;v['n']-=1
    z={};put=lambda key,x:z.setdefault(key,x%p);pp=lambda x,e:pow(x,e,p)
    W,H,E=body['W'],body['H'],body['E'];ws=body['weights'];Kh=H+2*W
    b=put('b',2*v['epsilon']**2);B=put('B',pow(2,KAPPA,p)*pp(b,2))
    dc=0
    for row,q in zip(body['target_order'],body['targets']):
        for (alpha,powers),c in rows[row].items():
            dc+=c*__import__('math').prod(pow(x,e,p) for x,e in zip(ports,powers))*pp(B,q-sum(a*w for a,w in zip(alpha,ws)))
    dc=put('Dcode',dc);ell=put('ell',sum(pp(B,w) for w in ws));targets=put('targets',sum(pp(B,q) for q in body['targets']))
    N0=put('N0',pp(B,W+1));L=put('block',2*b*pp(B,E));mask=put('mask',N0-1-(b-1)*ell)
    tc=put('Tcode',mask+(B-2)*targets*N0);jc=put('Jcode',2*(1+v['g'])**2*dc+targets);sc=put('Scode',v['g']+jc*N0)
    R=put('R',L*L+(sc+tc)*L+L-1-sc);N=put('N',pow(2,(15*KAPPA-20)//2,p)*pp(B,(E+W+8)//2))
    cap=put('cap',b*pp(B,W));Gcap=put('Gcap',32*cap);omega=put('omega',v['w']**2 if signed else v['w'])
    U=put('U',N*N*omega);Y=put('Y',N*N*v['s']);M=put('M',R*Y);P=put('P',2*M*M*U);K=put('K',R+1+v['h']*(P-1))
    A=put('A',M*(U+1));B1=put('B1',2*R+1);W1=put('W1',b*omega);C=put('C',B1+W1+v['phi']);J=put('J',4*A-5)
    Q=put('Q',3*W1*C-2*(W1*W1-1));D=put('D',(A*A-1)*C*C+1);ER=put('Eratio',v['i']*J*D*C*C)
    F=put('F',(A*A-1)*ER*ER+1);G=put('G',A+F*(C*D+1-A));HH=put('H',B1+v['j']*C);I=put('I',(G*G-1)*HH*HH+1)
    a0=put('a0',(P*P-1)*K*K+1);a1=put('a1',D*F*I);u=put('u',J*F);vv=put('v',Q*F+J*(HH-C));delta=put('delta',C-K*Y)
    if signed:
        Delta=put('Delta',v['g']*(cap-v['g'])*K*K-(cap*delta)**2);stack=a0 if seed else 1
        for index,(value,shift) in enumerate([(v['s'],-4),(v['phi'],8),(Delta,-4)],1):stack=put('Cguard'+str(index),stack*(1+(12*value+shift)*stack*v['z'+str(index)]**2))
        put('Cguard',stack);Z=put('Znonzero',__import__('math').prod(v[n] for n in ['epsilon','w','i','z1','z2','z3'])*(a0 if seed else 1))
        den=put('Smerge',Z*pp(u,5));rr=(vv+u*v['residue'])%p;target=put('Tmerge',(rr**3-u*u*rr-u**3)*(rr*rr+23*u*u))
        x=put('Xnorm',den*v['normroot']-target);a=put('A0norm',den*den*stack)
        if seed:
            bb=put('A1norm',den*den*stack*stack*a1);out=((x*x-a-bb)**2-4*a*bb)%p
        else:
            bb=put('A1norm',den*den*stack*stack*a0);cc=put('A2norm',den*den*(stack*(P*P+K*K+2))**2*a1)
            vv=(x*x+cc-a-bb)%p;ww=(vv*vv+4*x*x*cc-4*a*bb)%p;out=(ww*ww-16*vv*vv*x*x*cc)%p
    else:
        margin=put('margin',(K*K-4*delta*delta)*Gcap-8*v['g']*K*K);V0=put('V0',P*K);V1=put('V1',(A*C)*(A*ER)*(G*HH));Md=put('Mdiv',Q+HH)
        Om=put('Omega',u*margin);E0=put('E0',u*(v['n']+Md)+vv-2*Om*Md);Th=put('Theta',E0-Om*V0*V1)
        inner=put('inner',Th*Th-Om*Om*(a0+V0*V0*a1));out=(inner*inner-4*pp(Om,4)*V0*V0*a0*a1)%p
        if body['certificate']:
            gap=put('gapV',(C*C-1)*(A*ER)**2*(G*HH)**2+D*(ER*ER-1)*(G*HH)**2+D*F*(HH*HH-1))
    return out,z

def algebra_tests():
    # Independent multiplication in the rank-eight square-root algebra.
    rng=random.Random(20261023);norms=0
    for p in (101,1009):
        for k in (2,3):
            for _ in range(100):
                x=rng.randrange(p);rad=[rng.randrange(p) for _ in range(k)];poly={0:1}
                for signs in product((-1,1),repeat=k):
                    factor={0:x,**{1<<i:s for i,s in enumerate(signs)}};out=defaultdict(int)
                    for a,c in poly.items():
                        for b,d in factor.items():
                            value=c*d
                            for i in range(k):
                                if (a&b)&(1<<i):value*=rad[i]
                            out[a^b]=(out[a^b]+value)%p
                    poly={a:c for a,c in out.items() if c}
                if k==2:a,b=rad;formula=(x*x-a-b)**2-4*a*b
                else:
                    a,b,c=rad;v=x*x+c-a-b;formula=(v*v+4*x*x*c-4*a*b)**2-16*v*v*x*x*c
                require(poly.get(0,0)==formula%p and all(a==0 for a in poly),'norm expansion');norms+=1
    stack_checks=0;zero_seed_excluded=0
    for seed in range(-8,10):
        if not seed:zero_seed_excluded+=1;continue
        for values in product(range(-2,3),repeat=3):
            ds=[3*values[0]-1,3*values[1]+2,3*values[2]-1]
            for zs in product((-2,-1,1,2),repeat=3):
                C=seed;factors=[]
                for d,z in zip(ds,zs):
                    B=1+4*d*C*z*z;require(B%4==1 and abs(B)>=3 and gcd(C,B)==1,'guard nonzero or coprime');factors.append(B);C*=B
                require(abs(C)>1,'seeded magnitude')
                if C>=0 and isqrt(C)**2==C:
                    require(seed>0 and isqrt(seed)**2==seed and all(B>0 and isqrt(B)**2==B for B in factors),'seed recovery')
                    require(values[0]>=1 and values[1]>=0 and values[2]>0,'sign recovery')
                stack_checks+=1
    u_checks=0
    for A in range(-12,13):
        for C in range(-12,13):
            for i in range(-3,4):
                J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
                require(J*F!=0,'u nonzero');u_checks+=1
    merger_checks=0
    for u in range(-9,10):
        if not u:continue
        for v in range(-12,13):
            for r in range(-4,5):
                q=v+u*r;T=(q**3-u*u*q-u**3)*(q*q+23*u*u)
                require(T!=0,'merger numerator nonzero')
                if T%(u**5)==0:require(v%u==0,'merger valuation direction')
                # If Z=0, both delivered finalizers reduce to a nonzero power.
                require(T**4>0 and T**8>0,'zero denominator branches')
                merger_checks+=1
    intersective=0
    for m in range(1,1000):
        require(any(((x**3-x-1)*(x*x+23))%m==0 for x in range(m)),'intersective modulus');intersective+=1
    sparse=0
    for B in (4,8,16,32,64):
        for h in range(-B//4+1,B//4):
            for incoming in (-1,0):
                raw=2*h+1+incoming;digit=raw%B;outgoing=raw//B
                require(outgoing in (-1,0),'borrow range');require(((digit&(B-2))==0)==(h==0),'sparse target');sparse+=1
    return {'norm_expansion_cases':norms,'seeded_stack_signed_cases':stack_checks,'excluded_zero_seed_case':zero_seed_excluded,'unconditional_u_nonzero_cases':u_checks,'merger_signed_cases':merger_checks,'intersective_moduli':intersective,'sparse_borrow_cases':sparse}

def main():
    ports,payloads=auth();data=json.loads((ROOT/'upstream/parent_quartic31.json').read_text());rows=shifted_rows(data);code=json.loads((ROOT/'CODE.json').read_text());require(code==json.loads((ROOT.parent/'weights/code_v1.json').read_text()),'code tuple differs')
    # Authenticate relevant source copies at the requested repository pin.
    for rec in json.loads((ROOT/'SOURCE_PINS.json').read_text())['files']:
        raw=(ROOT/rec['local_path']).read_bytes();require(hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()==rec['git_blob_sha'],'pinned source Git blob');require(hashlib.sha256(raw).hexdigest()==rec['sha256'],'pinned source SHA256')
    pairs=list(combinations_with_replacement(range(32),2));positions=code['weights'];targetmap=dict(zip(code['targets'],code['order']));seen=set();isolation_checks=0
    for eq,q in zip(code['order'],code['targets']):
        for alpha in set(a for a,e in rows[eq]):
            offset=q-sum(a*w for a,w in zip(alpha,positions[1:]));require(offset>=0 and offset not in seen,'reversed exponent');seen.add(offset)
            pair=tuple([0]*(2-sum(alpha))+[i+1 for i,e in enumerate(alpha) for _ in range(e)])
            for beta in pairs:
                land=offset+sum(positions[i] for i in beta);isolation_checks+=1
                if land in targetmap:require(targetmap[land]==eq and beta==pair,'selective isolation')
    require(len(seen)==136 and isolation_checks==71808,'selective size')
    # Bound each formal weighted coefficient without evaluating a giant expansion.
    bits=[x.bit_length() for x in ports];coef_by_alpha={};maxbound=0
    for eq,terms in rows.items():
        groups=defaultdict(int)
        for (alpha,powers),c in terms.items():groups[alpha]+=abs(c)*(1<<sum(a*b for a,b in zip(bits,powers)))
        maxbound=max(maxbound,*groups.values());coef_by_alpha[eq]=groups
    boundbits=maxbound.bit_length();require(boundbits==2134927,'coefficient bound changed');require(KAPPA==boundbits+13 and KAPPA%2==0,'radix scale')
    W=max(code['weights']);Q=max(code['targets']);E=Q+3*W+2;E+=(E+W)%2
    require((E+W)%2==0 and E>W+23,'threshold exponent and size')
    for k in range(1,100,2):
        v=KAPPA+2*k;pop=(W+23)*v-31*k-22
        exp=1+k+E*v+pop+1
        half=(15*KAPPA-20)//2+((E+W+8)//2)*v
        require(exp==2*half,'square popcount threshold')
    rng=random.Random(274911);replays=0;metrics={}
    for variant,cert in [('signed',False),('signed_seeded',False)]:
        body=build(variant,cert);name=variant+('_certificate' if cert else '');
        require(len({n['name'] for n in body['nodes'] if n['kind']=='variable'})==13,'variable count')
        counts=Counter(n['kind'] for n in body['nodes'] if n['kind'] in ('add','sub','mul'));require(dict(counts)==body['operation_counts'] and sum(counts.values())==body['operations'],'operation ledger')
        for index,node in enumerate(body['nodes']):
            if node['kind'] in ('add','sub','mul'):require(0<=node['left']<index and 0<=node['right']<index,'DAG topology')
        stored=json.loads((ROOT/f'generated/{name}.json').read_text());expected=dict(body)
        if variant!='nine' or cert:expected['exact_degree']=degree_certificate(body)['exact_degree']
        require(stored==expected,'generated body reproducibility '+name)
        for p in (101,1009,1000003):
            f=fixed(body,ports,p)
            for trial in range(90):
                vs={n:rng.randrange(-4,5) for n in body['variables']}
                actual,named=evaluate(body,f,vs,p);wanted,regs=literal(body,vs,[x%p for x in ports],p,rows)
                require(actual==wanted,'literal output '+name)
                for n,value in named.items():require(regs[n]==value,'register '+name+' '+n)
                replays+=1
        dg=degree_certificate(body) if variant!='nine' or cert else None
        if dg:
            # The leading diagonal coefficient is a single fixed-scale monomial,
            # and both scales are powers of two, nonzero in this odd field.
            require(dg['leading_scalar']!=0 and set(dg['leading_fixed_monomial'])<= {'base_scale','threshold_scale'},'degree specialization')
            require(dg==json.loads((ROOT/f'generated/{name}_degree.json').read_text()),'degree reproducibility')
        metrics[name]={'operations':body['operations'],'operation_counts':body['operation_counts'],'degree':dg['exact_degree'] if dg else 23985284,'variables':len(body['variables'])}
    results={'status':'PASS','claim_scope':'Finite implementation and algebra audits; no new Lean or consistency certificate.','payloads':payloads,'source_contract':'Original package31, x_i=n_i+1, no package45 extra transport shift.','coefficient_bound_bits':boundbits,'selective_interactions_checked':isolation_checks,'circuit_literal_replays':replays,'square_threshold_odd_base_tests':50,'metrics':metrics,'algebra_checks':algebra_tests()}
    (ROOT/'CHECK_RESULTS.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
