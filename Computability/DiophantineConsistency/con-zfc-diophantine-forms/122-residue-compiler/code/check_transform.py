#!/usr/bin/env python3
"""Check new macro-to-quadratic identities and finite Pell digit regressions.

No import of the builder or inherited verifier.  Sparse ring arithmetic is
shared only with the independently authored literal checker in this folder.
"""
from pathlib import Path
from math import comb,gcd
import argparse,json
from check_independent import add,mul,scale,var,replace,rowdict,need,read

def atom(a):
    return {():a[1]} if a[0]=='c' else var(a[1])

def check(directory):
    d=Path(directory)
    tr=read(d/'TRANSFORM.json')
    meta=read(d/'raw/raw_audit_input.json')
    gates={int(k):int(v) for k,v in meta['gates'].items()}
    bylabel={r['label']:r for r in meta['rows'] if r.get('gate') is None}
    names={v['name']:['v',i] for i,v in enumerate(meta['variables'])}

    def unfold(poly,stops):
        stops={a[1] for a in stops if a[0]=='v'}
        memo={}
        def value(v):
            if v in stops or v not in gates:
                return var(v)
            if v in memo:
                return memo[v]
            row=rowdict(meta['rows'][gates[v]])
            need(row.get((v,))==1,'nonmonic gate in macro expansion')
            rest=scale({m:c for m,c in row.items() if m!=(v,)},-1)
            need(all(j<v for m in rest for j in m),'non-triangular macro gate')
            memo[v]=replace(rest,{j:value(j) for m in rest for j in m})
            return memo[v]
        return replace(poly,{v:value(v) for m in poly for v in m})

    identities=[]
    def prove_row(label,expected,stops):
        actual=unfold(rowdict(bylabel[label]),stops)
        wanted=unfold(expected,stops)
        need(actual==wanted,'macro row mismatch: '+label)
        identities.append(label)

    def prove_value(a,expected,stops,label):
        need(unfold(atom(a),stops)==unfold(expected,stops),'macro value mismatch: '+label)
        identities.append(label)

    W,A,Z=tr['scale'];L=tr['scale_lower']
    c=lambda n:{():n}
    p=lambda a:atom(a)
    ap=add(p(W),c(1));wz=mul(p(W),p(Z))
    prove_row('shared.last_norm_lower',add(mul(p(L),p(L)),mul(wz,wz),scale(mul(mul(ap,ap),mul(wz,wz)),-1),c(-1)),[W,L,Z])
    slack=names['shared.A_slack']
    prove_value(A,add(p(L),p(slack)),[L,slack],'cofinal_A=L+slack')
    atoms={tuple(a) for item in tr['exact_powers'] for a in (item['base'],item['exponent'],item['output'])}
    prove_row('shared.frame_definition',add(p(W),c(-2),*(scale(p(a),-1) for a in sorted(atoms))),[W]+[list(a) for a in atoms])
    rd=tr['radix'];q=rd['radix'];b=rd['root_base'];M=rd['common_root_modulus'];hq=rd['root_quotient'];N=rd['modulus']
    prove_value(b,add(p(q),c(1)),[q],'root_base=q+1')
    prove_row('modular.common_root',add(scale(mul(p(A),p(b)),2),scale(mul(p(b),p(b)),-1),c(-1),scale(mul(p(M),p(hq)),-1)),[A,b,M,hq])
    for request in tr['modular_requests']:
        X,Y=request['pair'];den=request['den'];quot=request['quotient'];rem=request['remainder'];rs=request['remainder_slack'];mod=request['modulus'];label=request['label']
        stops=[X,Y,A,b,den,quot,rem,rs,mod]
        expected=add(p(X),mul(p(b),p(Y)),scale(mul(p(A),p(Y)),-1),scale(p(rem),-1),scale(mul(p(mod),p(quot)),-1))
        if request['kind']=='exact':
            out=request['output'];stops.append(out)
            expected=add(expected,scale(mul(p(den),p(out)),-1))
            os=names[label+'.modular_oslack']
            prove_row(label+'.digit_bound',add(p(q),scale(p(out),-1),scale(p(os),-1),c(-1)),[q,out,os])
        prove_row(label+'.modular_digit',expected,stops)
        prove_row(label+'.remainder_bound',add(p(den),scale(p(rem),-1),scale(p(rs),-1),c(-1)),[den,rem,rs])
        factor=q if request['kind']=='exact' else N
        prove_value(mod,mul(p(den),p(factor)),[den,factor],label+'.actual_modulus')
    for request in tr['power_derivations']:
        out,n,prev=request['output'],request['base'],request['previous_output']
        prove_value(out,mul(p(n),p(prev)),[n,prev],'adjacent_power_product')
        prove_value(request['exponent'],add(p(request['previous_exponent']),c(1)),[request['previous_exponent']],'adjacent_exponent')
    recipe=tr['root_modulus_recipe']
    if recipe['kind']=='N_times_dominant_denominator':
        exponent=recipe['exponents'][0]
        power=next(v for v in tr['exact_powers'] if v['base']==q and v['exponent']==exponent)
        den=power['output']
        prove_value(M,mul(p(N),p(den)),[N,den],'dominant_modulus=N*q^(x+1)')
        prove_value(exponent,add(p(names['x']),c(1)),[names['x']],'dominant_exponent=x+1')
        allowed=[]
        t=meta['amplification']['t'];x=names['x'];y=names['y']
        for e in [t]:
            allowed.append(unfold(p(e),[t,x,y]))
        allowed.extend(unfold(add(p(e),c(1)),[t,x,y]) for e in (t,x,y))
        need(all(unfold(p(r['k']),[t,x,y]) in allowed for r in tr['modular_requests']),'unexpected lower digit index')
    return {'checked_new_ring_identities':len(identities),'identities':identities,
        'exact_power_graphs':len(tr['exact_powers']),'modular_numerator_requests':len(tr['modular_requests']),
        'status':'all new literal macro identities passed'}

def pell_digits():
    cases=0;exact=0;divisibility=0;parity=0
    for q in range(2,15):
        b=q+1
        for N in range(1,q+1):
            if q%N:
                continue
            for e in range(2,6):
                M=N*q**e
                g=gcd(2*b,M)
                need((b*b+1)%g==0,'cofinal linear congruence impossible')
                reduced=M//g
                residue=((b*b+1)//g)*pow((2*b)//g,-1,reduced)%reduced
                A=residue+reduced*(1+(b//reduced))
                need(A>=b and (2*A*b-b*b-1)%M==0,'bad cofinal root')
                X,Y=1,0
                for n in range(1,13):
                    X,Y=A*X+(A*A-1)*Y,X+A*Y
                    R=X+(b-A)*Y
                    need(R>0 and R%M==pow(b,n,M),'Pell residue identity failed')
                    cases+=1
                    for k in range(e+1):
                        if any(comb(n,j)>=q for j in range(min(k,n)+1)):
                            continue
                        den=q**k
                        if M%(q*den)==0:
                            need((R//den)%q==(comb(n,k) if k<=n else 0),'exact digit failed')
                            exact+=1
                        if M%(N*den)==0:
                            need((R%(N*den)<den)==((comb(n,k) if k<=n else 0)%N==0),'divisibility digit failed')
                            divisibility+=1
                parity+=g==2
    return {'Pell_residue_cases':cases,'exact_digit_cases':exact,'divisibility_digit_cases':divisibility,
        'noninvertible_factor_two_cases':parity,'status':'all finite regression cases passed'}

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('directory',type=Path);p.add_argument('--output',type=Path)
    a=p.parse_args();out={'literal_transform':check(a.directory),'finite_regressions':pell_digits()}
    text=json.dumps(out,indent=2)+'\n'
    if a.output:a.output.write_text(text)
    print(text)
