#!/usr/bin/env python3
"""A false divisibility witness for the weakened 42-operation Pell kernel.

The full 75-operation source is audited but is NOT asserted to have a false
raw-input witness. Large rational-family and auxiliary coordinates are given
by a parametric proof; they are not materialized by this finite checker.
"""
from pathlib import Path
from math import comb, gcd
import argparse
import hashlib
import json
import sympy as sp
import explore_fixed_raw_universal_76 as previous
import explore_base_two_wrong_index_rational as rational
from round37_1980_base_two_pell_regression import pell_power

NAMES=list(previous.NAMES)
CORE=[tuple('ic2' if value=='ic22' else value for value in row)
      for row in previous.CORE if row[0]!='ic22']
SCHEDULE=previous.OUTER+CORE[:1]+previous.TRANSPORT+CORE[1:]+previous.ADAPTER
EQUALITIES=[tuple('ic2' if value=='ic22' else value for value in pair)
            for pair in previous.EQUALITIES]


def source_residuals():
    sources=list(previous.source_residuals())
    c,i=previous.SYM['c'],previous.SYM['i']
    sources[12]=sp.expand(sources[12]-i*i*c**4+i*c*c)
    return sources


def verify_source():
    env=previous.fixed_environment(previous.SYM)
    baseline=previous.previous.previous.previous.previous.bridge.baseline
    bridge=previous.previous.previous.previous.previous.bridge
    baseline.run_schedule(SCHEDULE,env)
    sources=source_residuals();c,j,r,y=(previous.SYM[n] for n in ('c','j','r','y_aux'))
    correction=sources[12]*((j*c-2*r-1)**2-y*y)
    records=[]
    for ix,((left,right),source) in enumerate(zip(EQUALITIES,sources)):
        actual=sp.expand(env[left]-env[right]);adjust=correction if ix==13 else sp.Integer(0)
        sign=1 if sp.expand(actual-source-adjust)==0 else -1
        assert sp.expand(actual-sign*source-adjust)==0,ix
        records.append(dict(index=ix,equality=[left,right],source_sign=sign,
                            source=sp.sstr(source),correction=sp.sstr(sp.expand(adjust))))
    primitives,counts=bridge.verify_primitives(SCHEDULE,env)
    assert len(primitives)==75 and counts=={'*':40,'+':35}
    core_counts={'*':sum(row[1]=='*' for row in CORE),
                 '+':sum(row[1] in ('+','-') for row in CORE)}
    assert len(CORE)==42 and core_counts=={'*':24,'+':18}
    assert len(NAMES)==30 and len(EQUALITIES)==19
    assert len(records[5:15])==10
    assert [ix for ix,(a,b) in enumerate(zip(sources,previous.source_residuals())) if a!=b]==[12]
    old_i=previous.SYM['i']
    assert all(sp.expand(new.subs(old_i,old_i*old_i*c*c)-old)==0
               for new,old in zip(sources,previous.source_residuals()))
    return dict(operations=75,multiplications=40,additions_subtractions=35,
                positive_unknowns=NAMES,equations=19,
                kernel_operations=42,kernel_multiplications=24,kernel_additions_subtractions=18,
                kernel_equations=10,kernel_schedule=[list(row) for row in CORE],
                removed_instruction=['ic22','*','ic2','ic2'],
                positive_completeness_map='i_new=(i_old*c)^2; every other coordinate unchanged',
                all_nineteen_source_residuals_preserved_by_map=True,
                primitive_instructions=primitives,sources=records,
                claim='Exact source count only; no complete75 correctness or false-input claim')


def pell_mod(A,index,modulus):
    Delta=(A*A-1)%modulus
    def mul(x,y):
        return ((x[0]*y[0]+Delta*x[1]*y[1])%modulus,
                (x[0]*y[1]+x[1]*y[0])%modulus)
    out,base=(1,0),(A%modulus,1)
    while index:
        if index&1:out=mul(out,base)
        index//=2
        if index:base=mul(base,base)
    return out


def q_mod(K,h,modulus):
    """Q_h(K), independently evaluated by its degree-two matrix recurrence."""
    def mul(a,b):
        return ((a[0]*b[0]+a[1]*b[2])%modulus,
                (a[0]*b[1]+a[1]*b[3])%modulus,
                (a[2]*b[0]+a[3]*b[2])%modulus,
                (a[2]*b[1]+a[3]*b[3])%modulus)
    out,base=(1,0,0,1),((4*K-2)%modulus,-1%modulus,1,0)
    while h:
        if h&1:out=mul(out,base)
        h//=2
        if h:base=mul(base,base)
    return (out[2]*(4*K-3)+out[3])%modulus


def auxiliary_parameters(A,p,J):
    d,c=pell_power(A,p);Delta=A*A-1
    g=gcd(p,c);modulus=c//g
    assert A>=2 and p>=3 and p%2==1 and J%g==0 and 0<J<c and J%2==1
    sigma=(-1)**((p-1)//2)
    f,R=2*d*d-1,2*Delta*c*d
    i=4*Delta*Delta*d*d;K=R*R
    t=(((-sigma*J-p)//g)*pow(4*p//g,-1,modulus))%modulus
    if (-1)**t!=-sigma:t+=modulus
    index=p+4*p*t
    assert c%2==modulus%2==1 and (-1)**t==-sigma and index%4==p%4
    assert (sigma*index+J)%c==0
    assert K==i*c*c==Delta*(f*f-1) and R>f>2*c
    assert c>2*p and (2*p)%c!=0 and R%(c*c)!=0
    return dict(A=A,p=p,J=J,d=d,c=c,Delta=Delta,f=f,R=R,i=i,K=K,
                gcd_p_c=g,reduced_modulus=modulus,sigma=sigma,t=t,index=index)


def verify_auxiliary():
    modular=[];excluded=[]
    for A in range(2,10):
        for p in range(3,16,2):
            d,c=pell_power(A,p)
            g=gcd(p,c)
            for J in (3,5,7,9,11,15):
                if J>=c:continue
                if J%g:
                    # Since g divides every p+4pt, this residue is unreachable.
                    assert (-(-1)**((p-1)//2)*J-p)%g!=0
                    excluded.append(dict(A=A,p=p,J=J,gcd_p_c=g))
                    continue
                v=auxiliary_parameters(A,p,J);s=v['index'];h=(s-1)//2
                assert q_mod(v['K'],h,c)==(-J)%c
                assert q_mod(v['K'],h,v['f'])==(-c)%v['f']
                assert pell_mod(A,s,v['f'])[1]==((-1)**v['t']*c)%v['f']
                assert q_mod(0,h,c)==(v['sigma']*s)%c
                assert q_mod(1-A*A,h,v['f'])==(v['sigma']*pell_mod(A,s,v['f'])[1])%v['f']
                modular.append(dict(A=A,p=p,J=J,sigma=v['sigma'],
                                    gcd_p_c=g,reduced_modulus=v['reduced_modulus'],
                                    index_bits=s.bit_length(),c_divides_m=False))
    materialized=[]
    for A,p,J in ((2,5,7),(2,7,11),(2,3,9),(4,3,15)):
        v=auxiliary_parameters(A,p,J)
        chi,y=pell_power(v['R'],v['index']);U,rem=divmod(chi,v['R'])
        assert rem==0
        j,jrem=divmod(U+J,v['c']);o,orem=divmod(U+v['c'],v['f'])
        assert jrem==orem==0 and min(U,y,j,o,v['i'])>0
        assert U==j*v['c']-J==o*v['f']-v['c']
        assert v['i']*v['c']**2==v['Delta']*(v['f']**2-1)
        assert v['i']*v['c']**2*(U*U-y*y)==1-y*y
        materialized.append(dict(A=A,p=p,J=J,c=v['c'],f=v['f'],R=v['R'],i=v['i'],
                                 gcd_p_c=v['gcd_p_c'],reduced_modulus=v['reduced_modulus'],
                                 t=v['t'],auxiliary_index=v['index'],U_bits=U.bit_length(),
                                 y_bits=y.bit_length(),all_three_auxiliary_equations=True,
                                 positive_integral_j_o=True))
    return dict(modular_cases=len(modular),noncoprime_modular_cases=sum(v['gcd_p_c']>1 for v in modular),
                excluded_cases=len(excluded),exclusions=excluded,
                both_sigma_signs=sorted({v['sigma'] for v in modular}),
                cases=modular,materialized_auxiliary_cases=materialized,
                scope='Auxiliary block only; the large rational family is not materialized here')


def verify_crt_solvability():
    """Exhaust complete reduced periods, including the prescribed parity."""
    records=[];accepted=rejected=0
    for A in range(2,7):
        for p in (3,5):
            _,c=pell_power(A,p);g=gcd(p,c);modulus=c//g
            if c>5000:continue
            sigma=(-1)**((p-1)//2)
            residues={(sigma*(p+4*p*t))%c for t in range(2*modulus)
                      if (-1)**t==-sigma}
            assert len(residues)==modulus
            assert all(value%g==0 for value in residues)
            for J in range(1,min(c,128),2):
                soluble=((-J)%c in residues)
                assert soluble==(J%g==0)
                if soluble:accepted+=1
                else:rejected+=1
            records.append(dict(A=A,p=p,c=c,gcd_p_c=g,reduced_modulus=modulus,
                                all_parity_adjusted_residues_checked=len(residues)))
    return dict(complete_period_cases=len(records),accepted_J_cases=accepted,
                excluded_J_cases=rejected,cases=records,
                exact_criterion='gcd(p,c) divides J',
                scope='Necessary and sufficient for the prescribed s=p+4pt CRT family, not arbitrary weakened-kernel witnesses')


def verify_large_family_parameters():
    H=86;p=6*H+1;r=3*H+1;J=2*r+1;q=16;D0=q**3;X=1<<p
    numerator=(X+1)**(2*H);denominator=X**H*(1<<(2*H+1))
    Y,remainder=divmod(numerator,denominator)
    direct=sum(comb(2*H,j)*X**(j-H) for j in range(H+1,2*H+1))//(1<<(2*H+1))
    assert direct==Y and 0<5*remainder<denominator
    assert X%D0==Y%D0==0 and Y>=(1<<(4*H))
    assert q*q<=r<q**4 and r%2==1 and p==J-2
    a=Y*(X+1);A=a+2
    assert a>q**6>J and X*Y>r+1 and a>24*H and X+1>144*H
    Amod=A%p;cmod=pell_mod(Amod,p,p)[1]
    assert gcd(p,cmod)==1
    Xmod=pow(2,p,p)
    Ymod=(sum(comb(2*H,j)*pow(Xmod,j-H,p) for j in range(H+1,2*H+1))
          *pow(pow(2,2*H+1,p),-1,p))%p
    assert Ymod==Y%p and (Ymod*(Xmod+1)+2)%p==Amod
    valuation=(comb(2*r,r)&-comb(2*r,r)).bit_length()-1
    assert valuation==r.bit_count()==3<12 and comb(2*r,r)%D0!=0
    return dict(H=H,p=p,r=r,J=J,q=q,scale=D0,X_bits=X.bit_length(),Y_bits=Y.bit_length(),
                Y_two_adic_valuation=(Y&-Y).bit_length()-1,
                A_mod_p=Amod,c_mod_p=cmod,gcd_p_c=gcd(p,cmod),
                binomial_two_adic_valuation=valuation,required_valuation=12,
                rational_fraction_below_one_fifth=True,all_preliminary_size_bounds=True,
                main_and_first_pell_coordinates_materialized=False,
                auxiliary_coordinates_materialized=False,
                proof_supplies_all_ten_positive_kernel_equations=True)


def verify_compiler_mod_three():
    records=[]
    for a in range(2,8):
        for k in range(2,12):
            # Distinct windows, with the chosen tile alphabet size declared separately.
            windows=[tuple((i//(a**j))%a for j in range(9)) for i in range(k)]
            cc=previous.compile_windows(windows,a)
            assert cc.m%2==0 and cc.anchor_unit%2==1
            all_sum=sum((-1)**e for e in cc.positions)
            exceptional=(k%2==0 and a%2==1)
            assert all_sum==(-5 if exceptional else -3)
            mc=(1-sum((-1)**e for e in cc.positions if e!=1))%3
            mf=sum(value*((-1)**e) for e,value in cc.MFpoly.items())%3
            assert mf==1 and mc==(2 if exceptional else 0)
            for N in (2,3,4,5):
                qmod=(-1)**N;repunit=sum((-1)**i for i in range(N))
                residue=((mc+qmod*mf)*repunit)%3
                assert residue==(0 if N%2==0 else (1 if exceptional else 2))
            records.append(dict(a_tiles=a,window_count=k,MC_mod3=mc,MF_mod3=mf,
                                odd_N_packed_r_mod3=(mc-mf)%3))
    return dict(compilers=len(records),cases=records,
                conclusion='An even tile alphabet excludes r=1 mod3 for every N; the complete75 question remains open')


def dependency_hashes():
    here=Path(__file__).resolve().parent
    paths=[here/'explore_fixed_raw_universal_76.py',
           here/'explore_base_two_wrong_index_rational.py',
           here.parent/'1980'/'EXPLORATION_BASE_TWO_WRONG_INDEX_RATIONAL.md']
    return {str(path.relative_to(here.parent)).replace('\\','/'):hashlib.sha256(path.read_bytes().replace(b'\r\n',b'\n')).hexdigest()
            for path in paths}


def verify():
    return dict(status='PASS_WEAKENED42_KERNEL_COUNTEREXAMPLE',source=verify_source(),
                exact_nonauxiliary_cases=[rational.check_case(h) for h in (2,4,8)],
                large_family=verify_large_family_parameters(),auxiliary=verify_auxiliary(),
                crt_solvability=verify_crt_solvability(),
                compiler_mod_three=verify_compiler_mod_three(),dependencies=dependency_hashes(),
                proof='../1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md',
                review='Author and independent complete scoped proof/source reviews pass; fresh exact receipt checks pass',
                dependency_hash_convention='SHA256 after CRLF-to-LF normalization',
                scope='Complete weakened42 kernel failure under q16/r259 prebounds, proved parametrically; full75 compiler/transport/input extension is not asserted and even-alphabet packing excludes this family')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true')
    args=parser.parse_args();result=verify();path=Path(__file__).with_suffix('.json')
    normalized=json.loads(json.dumps(result))
    if args.write:path.write_text(json.dumps(normalized,indent=2)+'\n',encoding='utf-8')
    else:assert normalized==json.loads(path.read_text(encoding='utf-8'))
    print(result['status'],result['source']['operations'],result['source']['multiplications'],result['source']['additions_subtractions'])
    print(result['large_family'])
