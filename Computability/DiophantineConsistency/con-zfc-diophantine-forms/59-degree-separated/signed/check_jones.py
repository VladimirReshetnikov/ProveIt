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
    result={'base_scale':pow(2,KAPPA,p),'threshold_scale':pow(2,body['threshold_scale_exponent'],p)}
    for row in body['coefficient_recipes']:
        result[row['name']]=sum(t['coefficient']*__import__('math').prod(pow(x,e,p) for x,e in zip(ports,t['powers'])) for t in row['terms'])%p
    return result

def literal(body,values,ports,p,rows):
    v=dict(values);signed=body['variant'].startswith('signed');seed=body['variant']!='signed';coprime=body['variant'].startswith('signed_coprime');crt=body['variant'].endswith('_crt')
    if not signed:v['phi']-=1;v['n']-=1
    z={};put=lambda key,x:z.setdefault(key,x%p);pp=lambda x,e:pow(x,e,p)
    W,H,E=body['W'],body['H'],body['E'];ws=body['weights'];Kh=H+2*W
    b=put('b',2*v['epsilon']**2);B=put('B',pow(2,KAPPA,p)*pp(b,2))
    if 'split' in body['variant']:
        kernels=json.loads((ROOT/'split/split_kernels.json').read_text());dd=[]
        for row in kernels['kernels']:
            val=0
            for term in row['terms']:
                co=sum(t['coefficient']*__import__('math').prod(pow(x,e,p) for x,e in zip(ports,t['powers'])) for t in term['coefficient'])
                val+=co*pp(B,term['exponent'])
            dd.append(put('D'+str(row['degree']),val))
        ell=put('ell',sum(pp(B,w) for w in ws));targets=put('targets',sum(pp(B,q) for q in body['targets']))
        US=put('Usource',ell+v['g']);GS=put('Gsource',dd[2]*US*US+dd[1]*US+dd[0]);pad=put('positivity_pad',pp(B,body['positivity_pad_exponent']));gp=put('Gplus',GS+pad)
        N0=put('N0',pp(B,W+1));L=put('block',pp(B,E)*(1 if body.get('compact_calibration') else 2*b));mask=put('mask',N0-1-(b-1)*ell)
        tc=put('Tcode',mask+(B-2)*targets*N0);jc=put('Jcode',2*gp+targets);sc=put('Scode',v['g']+jc*N0)
        R=put('R',L*L+(sc+tc)*L+L-1-sc);N=put('N',pow(2,body['threshold_scale_exponent'],p)*pp(b,body['threshold_b_power'])*pp(v['epsilon'],body.get('threshold_epsilon_power',0))*pp(B,body['threshold_B_power']))
    else:
        dc=0
        for row,q in zip(body['target_order'],body['targets']):
            for (alpha,powers),c in rows[row].items():
                dc+=c*__import__('math').prod(pow(x,e,p) for x,e in zip(ports,powers))*pp(B,q-sum(a*w for a,w in zip(alpha,ws)))
        dc=put('Dcode',dc);ell=put('ell',sum(pp(B,w) for w in ws));targets=put('targets',sum(pp(B,q) for q in body['targets']))
        N0=put('N0',pp(B,W+1));L=put('block',pp(B,E)*(1 if body.get('compact_calibration') else 2*b));mask=put('mask',N0-1-(b-1)*ell)
        tc=put('Tcode',mask+(B-2)*targets*N0);jc=put('Jcode',2*(1+v['g'])**2*dc+targets);sc=put('Scode',v['g']+jc*N0)
        R=put('R',L*L+(sc+tc)*L+L-1-sc);N=put('N',pow(2,body['threshold_scale_exponent'],p)*pp(B,(E+W+8)//2))
    cap=put('cap',b*pp(B,W));Gcap=put('Gcap',32*cap);omega=put('omega',v['w']**2 if signed else v['w'])
    U=put('U',N*N*omega);Y=put('Y',N*N*v['s']);M=put('M',R*Y);P=put('P',2*M*M*U);K=put('K',R+1+v['h']*(P-1))
    A=put('A',M*(U+1));B1=put('B1',2*R+1);W1=put('W1',b*omega);C=put('C',B1+W1+v['phi']);J=put('J',4*A-5)
    Q=put('Q',3*W1*C-2*(W1*W1-1));D=put('D',(A*A-1)*C*C+1);ER=put('Eratio',v['i']*J*D*C*C)
    F=put('F',(A*A-1)*ER*ER+1);G=put('G',A+F*(C*D+1-A));HH=put('H',C+F*(B1+v['j']*C) if crt else B1+v['j']*C);I=put('I',(G*G-1)*HH*HH+1)
    a0=put('a0',(P*P-1)*K*K+1);a1=put('a1',D*F*I);u=put('u',J if crt else J*F);vv=put('v',Q if crt else Q*F+J*(HH-C));delta=put('delta',C-K*Y)
    if signed:
        Delta=put('Delta',v['g']*(cap-v['g'])*K*K-(cap*delta)**2);stack=a0 if seed else 1
        for index,(value,shift) in enumerate([(v['s'],-4),(v['phi'],8),(Delta,-4)],1):stack=put('Cguard'+str(index),stack*(1+(12*value+shift)*stack*(a1 if coprime and index==3 else 1)*v['z'+str(index)]**2))
        put('Cguard',stack);Z=put('Znonzero',__import__('math').prod(v[n] for n in ['epsilon','w','i','z1','z2','z3'])*(a0 if seed else 1))
        den=put('Smerge',Z*pp(u,5));rr=(vv+u*v['residue'])%p;target=put('Tmerge',(rr**3-u*u*rr-u**3)*(rr*rr+23*u*u))
        x=put('Xnorm',den*v['normroot']-target);a=put('A0norm',den*den*stack)
        if seed:
            bb=put('A1norm',den*den*a1*(1 if coprime else stack*stack));out=((x*x-a-bb)**2-4*a*bb)%p
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

def coprime_crt_tests():
    stack_count=0; square_count=0; zero_spectator_count=0
    for seed in range(-9,10):
        if not seed:continue
        for spectator in range(-9,10):
            for values in product(range(-1,2),repeat=3):
                ds=(3*values[0]-1,3*values[1]+2,3*values[2]-1)
                for zs in product((-2,-1,1,2),repeat=3):
                    C=seed; factors=[]
                    for k,(d,z) in enumerate(zip(ds,zs)):
                        B=1+4*d*C*(spectator if k==2 else 1)*z*z
                        require(B%4==1 and B!=0 and gcd(B,C)==1,'new guard coprimality')
                        factors.append(B); C*=B
                    require(C!=spectator,'raw radicands coincide')
                    require(gcd(factors[2],spectator)==1,'spectator coprimality')
                    if C>=0 and isqrt(C)**2==C:
                        require(seed>0 and isqrt(seed)**2==seed,'square seed recovery')
                        require(all(B>0 and isqrt(B)**2==B for B in factors),'square factor recovery')
                        require(values[0]>=1 and values[1]>=0,'first two sign guards')
                        if spectator>0:require(values[2]>0,'last sign guard after bootstrap')
                        if spectator==0:zero_spectator_count+=1
                        square_count+=1
                    stack_count+=1
    # Nonvacuous constructive Pell witnesses, including a zero spectator that
    # demonstrates why the source-positivity bootstrap in the proof is needed.
    pell_cases=0
    for spectator in (0,1,4,9,16):
        seed=1;C1=9;C2=2601;d3=2
        if spectator==0:
            B3=1;C3=C2
            require(isqrt(C3)**2==C3 and C3!=spectator,'explicit zero spectator branch')
        else:
            n=d3*C2*spectator
            a0=isqrt(n);m=0;den=1;a=a0
            p0,p1=1,a;q0,q1=0,1
            while p1*p1-n*q1*q1!=1:
                m=den*a-m;den=(n-m*m)//den;a=(a0+m)//den
                p0,p1=p1,a*p1+p0;q0,q1=q1,a*q1+q0
            if q1%2:p1,q1=p1*p1+n*q1*q1,2*p1*q1
            z3=q1//2;B3=1+4*d3*C2*spectator*z3*z3;C3=C2*B3
            require(B3==p1*p1 and isqrt(C3)**2==C3,'Pell completeness witness')
            q=isqrt(C3)+isqrt(spectator)
            require((q*q-C3-spectator)**2-4*C3*spectator==0,'constructive raw norm')
        pell_cases+=1
    # CRT identities are checked at arbitrary signed inputs, not only at ratio solutions.
    crt_count=0
    for A,C,i,j,B1 in product(range(-3,4),range(-3,4),(-2,-1,1,2),range(-3,4),(-3,1,4)):
        J=4*A-5;D=(A*A-1)*C*C+1;E=i*J*D*C*C;F=(A*A-1)*E*E+1
        H=C+F*(B1+j*C)
        quotient=(A*A-1)*i*i*J*J*D*D*C**3
        j_old=1+quotient*B1+F*j
        require(H==B1+j_old*C,'CRT exact polynomial reparameterization')
        require(F!=0 and (H-C)%F==0,'automatic F divisibility')
        require(gcd(J,F)==1,'J F coprimality')
        crt_count+=1
    # Positivity lemma: S=A(g+t)^2+g+N0*T with A>=2N0, 0<=t<N0.
    positivity_count=0
    for N0,D,T,t,g in product(range(2,8),range(1,5),range(1,4),range(1,8),range(-30,31)):
        if t>=N0:continue
        S=2*N0*D*(g+t)**2+g+N0*T
        require(S>0,'unconditional Scode positivity')
        positivity_count+=1
    # Abstract two-radical identity checked exactly over signed rationals.
    identity_count=0
    from fractions import Fraction
    for qnum,qden,C,B in product(range(-5,6),range(1,5),range(-8,9),range(-8,9)):
        q=Fraction(qnum,qden)
        norm=(q*q-C-B)**2-4*C*B
        if norm==0 and C!=B:
            require(q!=0,'raw norm root nonzero')
            r0=(q*q+C-B)/(2*q);r1=q-r0
            require(r0*r0==C and r1*r1==B,'rational square recovery identity')
            require(r0.denominator==r1.denominator==1,'integer square roots')
            identity_count+=1
    return {'signed_guard_cases':stack_count,'square_stack_cases':square_count,'constructive_pell_cases':pell_cases,
       'zero_spectator_square_cases':zero_spectator_count,'crt_identity_cases':crt_count,
       'unconditional_source_positivity_cases':positivity_count,
       'rational_square_recovery_cases':identity_count}

def split_size_checks():
    cases=0
    ws=json.loads((ROOT/'split/split_code.json').read_text())['weights']
    qs=json.loads((ROOT/'split/split_code.json').read_text())['targets']
    for coeff in (1,2,3):
        for b in (2,4,8):
            B=8192*coeff*b*b;N0=B**117;ell=sum(B**w for w in ws);targets=sum(B**q for q in qs)
            d2=B**1929//2;d0=-2*coeff*B**1719
            for padexp in (2161,2162):
                pad=B**padexp
                for sign in (-1,1):
                    d1=sign*2*coeff*B**2027
                    a=2*N0*d2;bb=2*N0*d1+1;cc=N0*(2*d0+2*pad+targets)-ell
                    floor=-bb//(2*a)
                    for U in (floor-1,floor,floor+1,floor+2,0):
                        require(a*U*U+bb*U+cc>0,'split signed S positivity at worst-case quadratic minimizer')
                        cases+=1
                g=b*B**116-1;U=ell+g
                maxg=2*coeff*(B**1929*U*U+B**2027*U+B**1719)
                J=2*(maxg+pad)+targets;S=g+N0*J
                mask=N0-1-(b-1)*ell;T=mask+N0*(B-2)*targets;L=(1 if padexp==2161 else 2*b)*B**2279
                require(0<mask<N0 and S+T<L,'split sharp block upper bounds')
                if padexp==2161:require(64*J<B**2162 and 32*S<B**2279 and 64*T<B**2279,'compact sharpened block bounds')
                else:require(S<3*B**2279 and T<B**2279,'scaled split block upper bounds')
                cases+=1
    return {'conservative_quadratic_and_block_cases':cases,'range':'toy coefficient majorants 1,2,3; b 2,4,8; pad exponents2161 and2162; universal proof remains in section.tex'}

def main():
    ports,payloads=auth();data=json.loads((ROOT/'upstream/parent_quartic31.json').read_text());rows=shifted_rows(data);code=json.loads((ROOT/'CODE.json').read_text());require(hashlib.sha256((ROOT/'CODE.json').read_bytes()).hexdigest()=='53cfdccbb252fd3f6ebe87ae0bb9dad8b2fdfc8c6168f668029add30ed339e25','pinned selective code')
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
    import importlib.util
    spec=importlib.util.spec_from_file_location('split_audit',ROOT/'split/verify_split.py');splitmod=importlib.util.module_from_spec(spec);spec.loader.exec_module(splitmod)
    split_result=splitmod.audit();require(KAPPA>=split_result['coefficient_bound_power_of_two']+13,'split radix coefficient floor');(ROOT/'SPLIT_CHECK_RESULTS.json').write_text(json.dumps(split_result,indent=2)+'\n')
    splitbody=build('signed_coprime_split_crt')
    for k in range(1,100,2):
        nu=KAPPA+2*k
        actual=1+k+splitbody['E']*nu+(splitbody['W']+23)*nu-31*k-22+1
        predicted=2*(splitbody['threshold_scale_exponent']+splitbody['threshold_b_power']*k+splitbody['threshold_B_power']*nu)
        require(actual==predicted,'split parity-tuned square threshold')
    for k in range(1,100,2):
        require(2418*KAPPA+4805*k-21==2*(8*KAPPA-10+1201*(KAPPA+2*k))+(k-1),'compact parity-tuned threshold')
    rng=random.Random(274911);replays=0;metrics={}
    for variant,cert in [(v,False) for v in ['signed','signed_seeded','signed_coprime','signed_coprime_crt','signed_coprime_split_crt','signed_coprime_compact_split_crt']]:
        body=build(variant,cert);name=variant+('_certificate' if cert else '');
        require(len({n['name'] for n in body['nodes'] if n['kind']=='variable'})==13,'variable count')
        binding=json.loads((ROOT/'generated'/body['coefficient_binding']).read_text())
        require(binding['additional_fixed_leaves']['base_scale']['exponent']==body['base_scale_exponent'] and binding['additional_fixed_leaves']['threshold_scale']['exponent']==body['threshold_scale_exponent'],'variant fixed-scale binding')
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
    results={'status':'PASS','claim_scope':'Finite implementation and algebra audits; no new Lean or consistency certificate.','payloads':payloads,'source_contract':'Original package31, x_i=n_i+1, no package45 extra transport shift.','coefficient_bound_bits':boundbits,'selective_interactions_checked':isolation_checks,'circuit_literal_replays':replays,'square_threshold_odd_base_tests':50,'metrics':metrics,'algebra_checks':algebra_tests(),'coprime_crt_checks':coprime_crt_tests(),'split_source_checks':split_result,'split_size_checks':split_size_checks()}
    (ROOT/'CHECK_RESULTS.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results,indent=2))
if __name__=='__main__':main()
