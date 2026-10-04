#!/usr/bin/env python3
"""Fresh bounded evidence; frozen predecessors are read only as inert bytes/data."""
import argparse
import hashlib
import json
import math
from pathlib import Path

BASE = Path('/home/codex/.codex/worktrees/2a71/Proofs/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue')
DEPENDENCIES = {
    'complete83_shared_projection_scout.json': 'dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c',
    'complete83_shared_projection_math.md': '1a9923b7202bef2e5a640b3b27c942423b9d9829d9fc6e7f4b55fa5c4d91053c',
    'complete83_even_radix_boundary.md': 'eba3e2944154dd7ff28e5b20d5e32e8ee6a0138b515c8e5f3846979dadaaa8dc',
    'complete83_dyadic_zero_offset_exclusion.md': 'afa5bf412a150d61deb91e0c5b1eaa17f7f9423c254a93fd1d699221a285adc1',
}

def need(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def vp(n, p):
    need(n != 0, 'valuation of zero')
    n = abs(n)
    answer = 0
    while n % p == 0:
        answer += 1
        n //= p
    return answer

def factv(n,p):
    result = 0
    while n:
        n //= p
        result += n
    return result

def source_check(raw):
    packet=json.loads(raw)['packet']
    rows=packet['source']
    need(len(rows)==83, '83 rows')
    rowmap={r[0]:r for r in rows}
    names=['Bm1','Jrep','w','s','F','Z','alpha','twice_cell_bits','x','inner_bits','MC','MF','Kconstant','transport_quotient']
    zero=(0,)*len(names)
    def const(x): return {} if x==0 else {zero:x}
    def var(name):
        e=list(zero); e[names.index(name)]=1
        return {tuple(e):1}
    def add(a,b,sign=1):
        out=dict(a)
        for e,c in b.items(): out[e]=out.get(e,0)+sign*c
        return {e:c for e,c in out.items() if c}
    def mul(a,b):
        out={}
        for ea,ca in a.items():
            for eb,cb in b.items():
                e=tuple(x+y for x,y in zip(ea,eb)); out[e]=out.get(e,0)+ca*cb
        return {e:c for e,c in out.items() if c}
    env={x:var(x) for x in names}
    used=set()
    def get(x):
        if type(x) is int: return const(x)
        if x not in env:
            name,op,a,b=rowmap[x]
            aa,bb=get(a),get(b)
            env[x]=mul(aa,bb) if op=='*' else add(aa,bb,1 if op=='+' else -1)
            used.add(x)
        return env[x]
    one=const(1)
    q=add(mul(env['Bm1'],env['Jrep']),one)
    q2=mul(q,q)
    C=add(add(add(add(q,env['F'],-1),env['Z'],-1),env['alpha'],-1),mul(env['twice_cell_bits'],env['x']),-1)
    R=add(mul(add(add(q2,env['Z'],-1),mul(q,env['F']),-1),add(q2,one,-1)),mul(add(env['MC'],mul(q,env['MF'])),env['Jrep']))
    transport=add(add(mul(add(env['Kconstant'],env['w']),C),add(q,env['F'],-1)),mul(add(q,one,-1),env['transport_quotient']),-1)
    expected={'q':q,'wn2':mul(q,env['w']),'sn2':mul(mul(q2,q),env['s']),
              'marked_rhs':C,'W':add(C,env['Z'],-1),
              'odd_index':add(mul(env['twice_cell_bits'],env['x']),env['inner_bits']),
              'r_lhs':R,'norm_transport':transport}
    for name,value in expected.items(): need(get(name)==value,'exact outer identity '+name)
    Dmask=add(env['Bm1'],env['MC'],-1)
    residue=add(add(env['Z'],mul(Dmask,env['Jrep']),-1),one,-1)
    quotient=add(add(add(add(add(add(mul(q2,q),q,-1),mul(env['Z'],q),-1),mul(q2,env['F']),-1),env['F']),mul(env['MF'],env['Jrep'])),one)
    need(add(R,residue,-1)==mul(q,quotient),'exact packed-index residue and polynomial quotient')
    return {'complete_source_rows':len(rows),'formal_bound_outputs':sorted(expected),
            'additional_exact_relation':'R-(Z-Dmask*J-1)=q*(q^3-q-Z*q-q^2*F+F+MF*J+1)',
            'bound_ancestor_rows':len(used),'bound_ancestor_names':sorted(used),
            'method':'fresh exact symbolic normalization of selected data rows over actual supplied ports; no predecessor helper execution'}

def prime_tests():
    primes=[3,5,7,11,13,17]
    cases=0; branches={}; resonant=0; cancellation=0
    transcript=[]
    for r in range(25,402,2):
        cc=[math.comb(2*r,r+j) for j in range(3)]
        for p in primes:
            c=vp(cc[0],p)
            need(c==factv(2*r,p)-2*factv(r,p),'factorial carry count')
            for b in range(1,4):
                for z in range(1,2*p):
                    if z%p==0: continue
                    X=p**b*z
                    value=cc[0]+cc[1]*X+cc[2]*X*X
                    N=(r+1)*(r+2)+r*(r+2)*X+r*(r-1)*X*X
                    denominator=(r+1)*(r+2)
                    need(denominator*value==cc[0]*N,'exact common-denominator identity')
                    actual=vp(value,p)
                    need(actual==c+vp(N,p)-vp(denominator,p),'valuation identity')
                    tie=False
                    if (r+1)%p==0:
                        d=vp(r+1,p); e=0; order=1; delta=b-d; branch='r+1'
                        need(c>=d,'linear low-digit carries')
                        if delta==0:
                            eta=(r+1)//p**b
                            F=eta*(r+2)+r*(r+2)*z+r*(r-1)*p**b*z*z
                            need(N==p**d*F,'linear normalized identity')
                            need(actual==c+vp(F,p),'linear exact valuation')
                            need((actual>c)==((eta-z)%p==0),'linear first lift')
                            tie=True
                    elif (r+2)%p==0:
                        d=vp(r+2,p); e=vp(r-1,p); order=2; delta=2*b+e-d; branch='r+2'
                        need(c>=d-(1 if p==3 else 0),'quadratic low-digit carries')
                        if delta==0:
                            eta=(r+2)//p**d; zeta=(r-1)//p**e
                            F=(r+1)*eta+r*eta*p**b*z+r*zeta*z*z
                            need(N==p**d*F,'quadratic normalized identity')
                            need(actual==c+vp(F,p),'quadratic exact valuation')
                            kval=2 if p==3 else 6
                            need((actual>c)==((eta-kval*z*z)%p==0),'quadratic first lift')
                            if p==3: need(e==1 and d==2*b+1,'exceptional 3 branch')
                            else: need(e==0 and d==2*b,'large odd prime branch')
                            tie=True
                    else:
                        branch='regular'; delta=0
                        need(actual==c,'regular central valuation')
                    if branch!='regular' and not tie:
                        need(actual==c+min(0,delta),'unique-minimum exact value')
                    branches[branch+('_tie' if tie else '')]=branches.get(branch+('_tie' if tie else ''),0)+1
                    if tie:
                        resonant+=1
                        cancellation+=int(actual>c)
                    for a in range(1,b+1):
                        if c<3*a and actual>=3*a:
                            linear=((r+1)%p==0 and vp(r+1,p)==b and (r+1-X)%p**(b+1)==0)
                            quadratic=((r+2)%p==0 and vp(r+2,p)==2*b+vp(6,p) and (r+2-6*X*X)%p**(2*b+vp(6,p)+1)==0)
                            need(linear or quadratic,'central-deficiency obstruction')
                    cases+=1
                    transcript.append([r,p,b,z,actual])
    return {'r_odd_interval':[25,401],'primes':primes,'v_p_X_values':[1,2,3],
            'unit_z_range':'1 <= z < 2p, p does not divide z','cases':cases,'branches':branches,
            'resonant_cases':resonant,'first_extra_cancellations':cancellation,
            'transcript_sha256':sha(json.dumps(transcript,separators=(',',':')).encode())}

def lift_tests():
    cases=[]
    for p,r,b in [(3,29,1),(5,29,1),(7,55,1),(3,133,1),(5,223,1),(7,145,1)]:
        c=vp(math.comb(2*r,r),p)
        if (r+1)%p==0:
            kind='linear'; d=vp(r+1,p); need(d==b,'linear tie')
            eta=(r+1)//p**d
            def fun(z): return eta*(r+2)+r*(r+2)*z+r*(r-1)*p**b*z*z
        else:
            kind='quadratic';d=vp(r+2,p);e=vp(r-1,p);need(d==2*b+e,'quadratic tie')
            eta=(r+2)//p**d;zeta=(r-1)//p**e
            def fun(z): return (r+1)*eta+r*eta*p**b*z+r*zeta*z*z
        roots=[z for z in range(1,p) if fun(z)%p==0]
        need(len(roots)==(1 if kind=='linear' else 2),'unit root count')
        lifted=[]
        for initial in roots:
            z=initial
            for precision in range(1,7):
                options=[z+t*p**precision for t in range(p) if fun(z+t*p**precision)%p**(precision+1)==0]
                need(len(options)==1,'unique next lift')
                z=options[0]
            X=p**b*z
            M2=sum(math.comb(2*r,r+j)*X**j for j in range(3))
            need(vp(X,p)==b and vp(M2,p)>=c+7,'lifted valuation')
            lifted.append({'initial_unit':initial,'unit_mod_p7':z,'M2_valuation':vp(M2,p)})
        cases.append({'p':p,'r':r,'b':b,'central_valuation':c,'kind':kind,'lifts':lifted})
    return {'precision':7,'examples':cases,'scope':'local prime-power polynomial only; no compiler, transport or exponential-offset tuple asserted'}

def truncation_tests():
    odd_tests=0; full_tests=0
    for q in range(4,42,2):
        for r in range(3,36,2):
            cc=[math.comb(2*r,r+j) for j in range(r+1)]
            for w in [1,2,5]:
                X=q*w
                mod=2*q**3
                full=sum(cc[j]*pow(X,j,mod) for j in range(r+1))%mod
                cubic=sum(cc[j]*pow(X,j,mod) for j in range(4))%mod
                need(full==cubic,'full even-radix truncation')
                full_tests+=1
                for p in [3,5,7,11,13,17,19]:
                    if q%p: continue
                    a=vp(q,p); m=p**(3*a)
                    quadratic=sum(cc[j]*pow(X,j,m) for j in range(3))%m
                    need(full%m==quadratic,'odd-prime quadratic truncation')
                    odd_tests+=1
    return {'even_q_range':[4,40],'odd_r_range':[3,35],'w_values':[1,2,5],
            'full_four_term_cases':full_tests,'odd_prime_three_term_cases':odd_tests}

def transport_tests():
    cases=0
    for q in range(4,42,2):
        m=q-1
        for C in range(q-1):
            g=math.gcd(C,m)
            for F in range(1,q-1):
                for K in [0,7]:
                    roots=[w for w in range(m) if ((K+w)*C-F)%m==0]
                    need(bool(roots)==(F%g==0),'transport gcd compatibility')
                    need(not roots or len(roots)==g,'transport root count')
                    for w in roots:
                        positive_w=w or m
                        t=((K+positive_w)*C+q-F-1)//m
                        need(t>0,'positive transport quotient for K>=0')
                    cases+=1
    return {'q_even_range':[4,40],'C_range':'0..q-2','F_range':'1..q-2','K_values':[0,7],
            'cases':cases,'scope':'transport congruence only; other source constraints not synthesized'}

def family_tests():
    cases=[]
    for d in range(2,13):
        B=2**d
        for family,oddpart,period in [('Bplus1',B+1,2*d),('2Bminus1',2*B-1,d+1)]:
            left=oddpart;primes=[];p=3
            while p*p<=left:
                if left%p==0:
                    primes.append(p)
                    while left%p==0:left//=p
                p+=2
            if left>1:primes.append(left)
            q=B*(B+1)//2 if family=='Bplus1' else B*(2*B-1)
            J=B//2+1 if family=='Bplus1' else 2*B+1
            need(q==(B-1)*J+1,'family radix')
            for p in primes:
                a=vp(q,p)
                need(B%p!=1,'coprime radix denominator')
                for n in [1,2,p,p*p]:
                    # Evaluate the normalized difference by modular powers only.
                    expected=a+vp(n,p)
                    residue=(pow(2,period*n,p**(expected+1))-1)%p**(expected+1)
                    need(residue!=0 and vp(residue,p)==expected,'exact family X valuation')
                    cases.append([d,family,p,n,a,expected])
                if family=='Bplus1':need((2*J-1)%p==0,'family J half')
                else:need((J-2)%p==0,'family J twice')
    return {'d_range':[2,12],'checks':len(cases),
            'transcript_sha256':sha(json.dumps(cases,separators=(',',':')).encode()),
            'scope':'symbolic radix-family arithmetic; no compiled table or source zero generated'}

def receipt():
    deps={}
    for n,pin in DEPENDENCIES.items():
        raw=(BASE/n).read_bytes();need(sha(raw)==pin,'dependency pin '+n)
        deps[n]={'sha256':pin,'bytes':len(raw)}
    return {'schema':'complete83-odd-prime-boundary-v1','helper_sha256':sha(Path(__file__).read_bytes()),
            'dependencies':deps,'source_binding':source_check((BASE/'complete83_shared_projection_scout.json').read_bytes()),
            'prime_classification':prime_tests(),'lifts':lift_tests(),'truncation':truncation_tests(),
            'transport':transport_tests(),'radix_families':family_tests(),'scope':{'frozen_program_execution':False,'compiler_execution':False,
              'full_source_reconstruction':False,'new_circuit_rows':0,'full_positive_zeros_materialized':0,
              'universal83_claim':False,'finite_checks_are_not_all_size_proof':True}}

def main():
    ap=argparse.ArgumentParser();group=ap.add_mutually_exclusive_group(required=True)
    group.add_argument('--output');group.add_argument('--expect');args=ap.parse_args()
    result=receipt()
    if args.output:
        with open(args.output,'x') as f: json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
    else:
        expected=json.loads(Path(args.expect).read_text())
        need(result==expected,'receipt mismatch')
    print(json.dumps({'status':'PASS','source_outputs':len(result['source_binding']['formal_bound_outputs']),
                      'prime_cases':result['prime_classification']['cases'],
                      'lift_examples':len(result['lifts']['examples']),
                      'transport_cases':result['transport']['cases']},sort_keys=True))
if __name__=='__main__':main()
