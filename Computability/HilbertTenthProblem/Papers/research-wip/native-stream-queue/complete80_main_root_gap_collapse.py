#!/usr/bin/env python3
"""Fresh data-only complete-source scout; no predecessor imports or execution."""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from math import comb, gcd
from pathlib import Path
import random

NAMES = ['complete84_scaled_strong_output.py','complete84_scaled_strong_output.json','complete84_scaled_strong_output.md','complete75_half_binomial_compiler.md','pell_kernel_half_binomial42.md','review_complete74_asymmetric_scale_math.md','complete80_first_index_deletion_collapse.md','complete75_gamma_dominance_elimination102.md','complete84_actual_modulus_scout.md','complete84_joint_root_cut.md']
PINS = {'complete84_scaled_strong_output.py': '8b4dd58c849ae79751f1be6638f1b9e3f9072a714c5479eadf1039f10d0c7737', 'complete84_scaled_strong_output.json': '8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf', 'complete84_scaled_strong_output.md': '01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade', 'complete75_half_binomial_compiler.md': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117', 'pell_kernel_half_binomial42.md': '0df596859d84aa1cf1d4636457937274e8fdac0c1f8da3196962d911be232992', 'review_complete74_asymmetric_scale_math.md': 'a7f8d64389597c5a8fff93bad1f023dfc440d736bb9d77f2acd549e758aa0b58', 'complete80_first_index_deletion_collapse.md': 'a6fb0955f6a19a7564a3070cbf5bdc4e76a6a39a572b46a4d8f656ae9113a575', 'complete75_gamma_dominance_elimination102.md': '1f72fa26022dd6d27e2000d6a57428907fb5766480b0f20bdf52949b1845c3d7', 'complete84_actual_modulus_scout.md': '068c5efb6d2fc6d011334d4e0cf7384e5d6d048ec64cee1c2161bb126cb173a1', 'complete84_joint_root_cut.md': '79cfda9e870ad63a848fb454266d1bca98f2117393edc57f99108b4c1cce780c'}

def require(ok, why):
    if not ok: raise ValueError(why)

def digest(data): return sha256(data).hexdigest()
def canonical(obj): return json.dumps(obj,sort_keys=True,separators=(',',':')).encode()

def run(source, env):
    e=dict(env)
    for name, op, x, y in source:
        a=e[x] if isinstance(x,str) else x
        b=e[y] if isinstance(y,str) else y
        e[name]=a+b if op=='+' else a-b if op=='-' else a*b
    return e

def topo(rows, free):
    todo=list(rows); known=set(free); out=[]
    while todo:
        for j,r in enumerate(todo):
            if all(not isinstance(a,str) or a in known for a in r[2:]):
                require(r[0] not in known,'duplicate producer')
                out.append(r); known.add(r[0]); del todo[j]; break
        else: raise ValueError('cycle or unavailable port')
    return out

def check_live(rows, free):
    producers={r[0]:r for r in rows}; live={'polynomial'}; todo=['polynomial']
    while todo:
        n=todo.pop()
        if n in producers:
            for a in producers[n][2:]:
                if isinstance(a,str) and a not in live: live.add(a); todo.append(a)
    require(live==set(free)|set(producers),'dead source or supplied port')
    return {'rows':len(rows),'ports':len(free)}

def add(a,b,sgn=1,p=None):
    c=[0]*max(len(a),len(b))
    for j,v in enumerate(a): c[j]+=v
    for j,v in enumerate(b): c[j]+=sgn*v
    if p: c=[v%p for v in c]
    while len(c)>1 and not c[-1]: c.pop()
    return c

def mul(a,b,p=None):
    c=[0]*(len(a)+len(b)-1)
    for j,v in enumerate(a):
        for k,w in enumerate(b): c[j+k]+=v*w
    if p: c=[v%p for v in c]
    while len(c)>1 and not c[-1]: c.pop()
    return c

def poly_run(rows,env,p):
    e=dict(env)
    for n,op,x,y in rows:
        a=e[x] if isinstance(x,str) else [x]
        b=e[y] if isinstance(y,str) else [y]
        e[n]=add(a,b,1,p) if op=='+' else add(a,b,-1,p) if op=='-' else mul(a,b,p)
    return e

def pell(a,n):
    # Binary multiplication in Z[sqrt(a^2-1)].
    disc=a*a-1; u,v=1,0; x,y=a,1
    while n:
        if n&1: u,v=u*x+disc*v*y,u*y+v*x
        x,y=x*x+disc*y*y,2*x*y; n//=2
    return u,v

def val2(n):
    require(n>0,'positive valuation argument')
    return (n&-n).bit_length()-1

def component_checks():
    ratios=[]
    for R in (7,11,15,19):
        r=(R-1)//2
        for scale in (1,2,3):
            X=(1<<R)*scale
            M=comb(2*r,r)+sum(comb(2*r,r+j)*X**j for j in range(1,r+1))
            require(M%2==0,'half polynomial integral')
            Y=M//2; a=Y*(X+1); A=a+2; E=X*Y; P=2*X*Y*Y+1
            D,c=pell(A,R); tau,k0=pell(P,r+1); k=2*k0
            eta=c-k*Y; zeta=k-eta
            require(eta>0 and zeta>0,'strict ratio')
            require((k-R-1)%E==0 and k>R+1,'positive first quotient')
            require(tau*tau-X*Y*Y*(X*Y*Y+1)*k*k==1,'first norm')
            require(D*D-(A*A-1)*c*c==1,'main norm')
            require(Fraction(16*r,X+1)<Fraction(1,2),'uniform error bound')
            ratios.append({'R':R,'X':X,'Y_bits':Y.bit_length(),'eta_bits':eta.bit_length(),'zeta_bits':zeta.bit_length(),'h_bits':((k-R-1)//E).bit_length(),'ratio_numerator_sha256':digest(str(c).encode())})
    inputs=[]
    for A in (5,7,13,26,101):
        a=A-2; Delta=A*A-1; H=4*a+3
        previous=0
        for u in range(3,20,2):
            mu,kappa=pell(A,u); numerator=mu-a*kappa-(1<<u)
            require(numerator%H==0 and numerator>0,'positive input rho')
            require((kappa-u)%Delta==0 and kappa>u,'positive input delta')
            g=numerator//H
            require(g>previous,'increasing sampled input quotient'); previous=g
            inputs.append({'A':A,'u':u,'rho':str(g),'delta':str((kappa-u)//Delta)})
    outers=[]
    # These satisfy listed arithmetic mask contracts, not a compiled program.
    for d in (5,7,9):
        B=1<<d; MC=B-2; MF0=4; K=17; b=5
        require(MC.bit_count()+MF0.bit_count()==d,'mask population contract')
        for N in (5,7,9):
            q=1<<(d*N); J=(q-1)//(B-1); t=d*N
            for x in (1,2,3):
                u=2*d*x+b; W=1<<u
                if q<=W+2*d*x+6: continue
                C=W+1; F=4; Z=1; alpha=q-W-2*d*x-6
                R=(q*q-Z-q*F)*(q*q-1)+(MC+q*(MF0+B-1))*J
                TC=MC*J+1; TF=MF0*J-1
                require((Z-1)&TC==0 and F&TF==0,'shifted mask AND')
                require(R%4==3 and R.bit_count()==3*t+2,'index parity/population')
                require(3*q+1<=R<q**4 and R>u,'packed index bounds')
                require(gcd(C,q-1)==1,'odd-exponent inverse')
                wres=(4*pow(C,-1,q-1)-K)%(q-1)
                r=(wres*pow(2,-1,q-1))%(q-1)
                w0=2*q*q*(r+q-1)
                require(w0%(2*q*q)==0 and (K+w0)*C% (q-1)==4,'CRT base')
                tq=((K+w0)*C+q-5)//(q-1)
                require((K+w0)*C+q-F-tq*(q-1)==1 and tq>0,'transport unit')
                rr=(R-1)//2
                require(rr.bit_count()-1==3*t,'half-central valuation')
                outers.append({'d':d,'N':N,'x':x,'q':str(q),'R':str(R),'alpha':str(alpha),'w_base':str(w0),'transport_base':str(tq),'index_population':R.bit_count(),'central_valuation':rr.bit_count(),'half_central_valuation':rr.bit_count()-1,'scope':'Outer arithmetic only; w_base need not meet X>=2^R; no full Pell zero or compiled history materialized.'})
    mod_cases=[]
    for R in (7,11,15,19,23,27):
        r=(R-1)//2
        for t in (1,2,3):
            q=1<<t; X=2*q**3
            M=comb(2*r,r)+sum(comb(2*r,r+j)*X**j for j in range(1,r+1))
            require(M%2==0 and (M//2-comb(2*r,r)//2)%q**3==0,'half polynomial modulus')
            mod_cases.append({'R':R,'t':t,'residue':M//2%q**3})
    return {'ratio_converses':ratios,'positive_input_interfaces':inputs,'outer_contract_samples':outers,'half_polynomial_moduli':mod_cases,'scope':'Independent finite arithmetic supplements; no genuine compiled numeral tuple or complete large positive zero is materialized.'}

def build(root):
    seen={}
    for name,pin in PINS.items():
        data=(root/name).read_bytes(); require(digest(data)==pin,'dependency pin '+name); seen[name]=pin
    parent=json.loads((root/'complete84_scaled_strong_output.json').read_text())['packet']
    old=parent['source']; by={r[0]:r for r in old}
    expected=[['cam2','*','R10a','R12'],['D1','+','wn2','cam2'],['gamma_sum','+','rho','sigma'],['gam','*','gamma_sum','a4m5'],['R14','+','D1','gam']]
    for row in expected: require(by[row[0]]==row,'literal private row')
    remove={r[0] for r in expected}
    for r in old:
        if r[0] not in remove:
            require(not any(a in remove-{'R14'} for a in r[2:] if isinstance(a,str)),'removed external consumer')
    free=[('main_root_gap' if x=='sigma' else x) for x in parent['free']]
    witnesses=[('main_root_gap' if x=='sigma' else x) for x in parent['witnesses']]
    rows=topo([r for r in old if r[0] not in remove]+[['R14','+','exponent_rhs','main_root_gap']],free)
    live=check_live(rows,free); ops=Counter(r[1] for r in rows)
    require((len(rows),ops['*'],ops['+']+ops['-'],len(witnesses))==(80,45,35,18),'complete ledger')
    # No other producer changed. The main factor is the only differing factor.
    for r in rows:
        if r[0]!='R14': require(r==by[r[0]],'unchanged producer')
    rng=random.Random(804535); numeric=[]
    for j in range(48):
        env={n:Fraction(rng.randint(-5,7),rng.randint(1,5)) for n in parent['free']}
        oe=run(old,env)
        child={n:env[n] for n in free if n!='main_root_gap'}
        child['main_root_gap']=oe['R14']-oe['exponent_rhs']
        ce=run(rows,child)
        for n in set(by)-remove: require(oe[n]==ce[n],'full forward row '+n)
        require(oe['R14']==ce['R14'],'root forward identity')
        if oe['a4m5']:
            child['main_root_gap']=Fraction(rng.randint(-7,8),rng.randint(1,5))
            ce=run(rows,child); inv=dict(env)
            inv['sigma']=(ce['R14']-ce['wn2']-ce['R10a']*ce['R12'])/ce['a4m5']-ce['rho']
            ie=run(old,inv)
            require(ie['polynomial']==ce['polynomial'],'full rational inverse')
        numeric.append(digest(str(ce['polynomial']).encode()))
    degree_cases=[]
    factors=parent['factors']; desired=[22,38,32,60,7,2,46]
    for seed,prime in ((101,1000000007),(307,1000000009),(991,1000000033)):
        rng=random.Random(seed); fixed={'Bm1':31,'Kconstant':17,'twice_cell_bits':10,'inner_bits':5,'MC':30,'MF':35}
        env={n:([fixed[n]] if n in fixed else [rng.randint(1,17),rng.randint(1,17)]) for n in free}
        e=poly_run(rows,env,prime)
        require([len(e[n])-1 for n in factors]==desired,'actual factor degrees')
        require(len(e['polynomial'])-1==207,'whole exact degree specialization')
        slopes={n:env[n][-1] for n in free}; Q=31*slopes['Jrep']; k=slopes['eta']+slopes['zeta']
        C=Q-slopes['F']-slopes['Z']-slopes['alpha']-10*slopes['x']
        Tt=slopes['w']*C-slopes['transport_quotient']*Q
        leader=4*pow(Q,124,prime)*slopes['h']*slopes['delta']**4*slopes['i']**4*k**12*slopes['w']**22*slopes['s']**34*Tt*slopes['auxiliary_quotient']**2*slopes['f']**2%prime
        require(e['polynomial'][-1]==leader,'full uniform leader specialization')
        degree_cases.append({'seed':seed,'prime':prime,'factor_degrees':desired,'degree':207,'leading_coefficient':leader,'all_coefficient_sha256':digest(canonical(e['polynomial']))})
    # Explicit raw syntactic bound, distinct from exact cancellation-aware degree.
    deg={n:(0 if n in parent['fixed_numerals'] else 1) for n in free}
    for n,op,x,y in rows:
        a=deg[x] if isinstance(x,str) else 0; b=deg[y] if isinstance(y,str) else 0
        deg[n]=a+b if op=='*' else max(a,b)
    return {'status':'PASS','scope':'Rejected main-root-gap candidate; all-input collapse proved for inherited valid compiler slices. This is not a universal bound. Predecessor files are inert only.','pins':seen,'packet':{'source':rows,'free':free,'witnesses':witnesses,'fixed_numerals':parent['fixed_numerals'],'ordinary_input':'x','witness_domain':'strictly positive integers','output':'polynomial','factors':factors,'ledger':{'M':45,'A':35,'total':80,'witnesses':18},'exact_degree':207,'factor_exact_degrees':desired,'raw_degree_upper':deg['polynomial'],'source_sha256':digest(canonical(rows)),'positive_family_factor_values':[1,1,1,1,1,1,'Delta'],'forward_map':'main_root_gap = X-W+a*(c-kappa)+sigma_old*H','all_ring_identity':'P80(main_root_gap = X-W+a*(c-kappa)+sigma_old*H) = P84','inverse_domain':'H != 0; sigma_old=(mu+main_root_gap-X-a*c)/H-rho; no integer or positive inverse asserted','complete_leader':'4*Q0^124*h*delta^4*i^4*(eta+zeta)^12*w^22*s^34*Ttransport*Taux^2*f^2','nonzero_coefficient':'-4*Bm1^125','nonzero_monomial':'Jrep^125*h*delta^4*i^4*eta^12*w^22*s^34*transport_quotient*auxiliary_quotient^2*f^2'},'structure':{'removed_rows':expected,'added_row':['R14','+','exponent_rhs','main_root_gap'],'liveness':live,'forward_full_source_checks':48,'full_coefficient_degree_cases':degree_cases,'signed_value_hashes':numeric},'components':component_checks()}

def main():
    ap=argparse.ArgumentParser(); ap.add_argument('--root',type=Path,required=True); ap.add_argument('--output',type=Path); ap.add_argument('--expect',type=Path); a=ap.parse_args()
    out=build(a.root); data=json.dumps(out,indent=2,sort_keys=True)+'\n'
    if a.expect:
        # Preserve exact JSON types and values, rather than Python's bool/int equivalence.
        expected=json.loads(a.expect.read_text()); require(canonical(expected)==canonical(out),'exact typed receipt')
    if a.output: a.output.write_text(data)
    print('PASS: complete80 main-root-gap, 45M+35A, 18 witnesses, degree207; no large compiler zero materialized')
if __name__=='__main__': main()
