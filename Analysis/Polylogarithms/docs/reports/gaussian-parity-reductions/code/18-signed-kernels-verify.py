#!/usr/bin/env python3
"""Reproduce exact checks, interval certificates, reduction tables and rank data."""
from __future__ import annotations
import argparse,json,platform,time
from pathlib import Path
from math import comb
from fractions import Fraction as Q
import sympy as s
from gaussian import *
from full_ds import system,s4_witness

ROOT=Path(__file__).resolve().parents[1]

def json_write(name,value):
    (ROOT/"data"/name).write_text(json.dumps(value,indent=2)+"\n")

def tex(expression):
    text=s.latex(expression)
    # Symbols pi and L have explicit replacements; B/Z subscripts use integer atoms.
    text=text.replace(r"\pi",r"\pi")
    import re
    text=re.sub(r'B_\{(\d+)\}',lambda m:r'\beta('+m.group(1)+')',text)
    text=re.sub(r'Z_\{(\d+)\}',lambda m:r'\zeta('+m.group(1)+')',text)
    text=text.replace('L',r'\log 2')
    return text

def main():
    if not __debug__:
        raise RuntimeError("Run verification without Python -O; assertions must remain enabled.")
    parser=argparse.ArgumentParser();parser.add_argument('--terms',type=int,default=400)
    parser.add_argument('--max-weight',type=int,default=16);parser.add_argument('--rank-max',type=int,default=31)
    args=parser.parse_args();N=args.terms
    if N<16 or not 2<=args.max_weight<=16 or args.rank_max<3:
        parser.error('Use terms >= 16, 2 <= max-weight <= 16, and rank-max >= 3')
    start=time.time();counts={}
    pi,L=atoms();B2=beta_symbol(2);B4=beta_symbol(4);B6=beta_symbol(6)
    Z3=zeta_symbol(3);Z5=zeta_symbol(5)
    expected={
        5:(-64*pi**3*Z3-527*pi*Z5+4096*B6)/2048,
        4:(96*pi**3*Z3-32*pi**2*B4+1581*pi*Z5-8448*B6)/1536,
        3:(-3*pi**3*Z3+64*pi**2*B4-1581*pi*Z5+4608*B6)/1024,
        2:(-14*pi**4*B2+135*pi**3*Z3-1440*pi**2*B4+23715*pi*Z5-69120*B6)/23040,
        1:(-150*pi**5*L+56*pi**4*B2-270*pi**3*Z3+1920*pi**2*B4-675*pi*Z5)/92160,
    }
    for a,rhs in expected.items():assert s.expand(parity_symbol(a,6-a)-rhs)==0
    counts['source_weight_six_exact']=5
    # Six source candidates: the sixth has the certificate 960 R_1 - 224 R_2.
    A5=shuffle_matrix(5);v=s.Matrix([[960,-224]])
    assert v*A5==s.Matrix([[960,736,288,576]])
    products=s.Matrix([s.im(single_symbol(1,1)*single_symbol(4,1)),
                       s.im(single_symbol(2,1)*single_symbol(3,1))])
    assert s.expand((v*products)[0]-(21*B2*Z3-480*B4*L))==0
    counts['source_weight_five_exact']=1
    counts['shuffle_inverse_weights']=0
    for w in range(2,41):
        A=shuffle_matrix(w);m=w//2
        D=s.diag(*[s.Rational(1,2) if 2*p==w else 1 for p in range(1,m+1)])
        Inv=s.Matrix([[(-1)**(j-p)*comb(j-1,p-1) if j>=p else 0
                       for j in range(1,m+1)] for p in range(1,m+1)])
        assert Inv*D*A[:,:m]==s.eye(m)
        counts['shuffle_inverse_weights']+=1
    # Independent verification of the exact inverse-Mellin kernel recursion.
    counts['kernel_recurrences']=0
    for a in range(2,9):
        for b in range(1,9):
            T,K=kernel_exact(a,b);_,prev=kernel_exact(a-1,b)
            assert s.expand(s.diff(K,T)-prev)==0
            counts['kernel_recurrences']+=1
    counts['kernel_base_derivatives']=0
    for b in range(1,9):
        T,K=kernel_exact(1,b)
        result=s.diff(K,T)+T**(b-1)/(s.factorial(b-1)*(1-s.exp(-T)))
        result=result.subs(s.polylog(0,s.exp(-T)),1/(s.exp(T)-1))
        assert s.simplify(result)==0
        counts['kernel_base_derivatives']+=1
    counts['euler_weight_and_sign_cases']=0
    for a in range(1,5):
        for b in range(1,5):
            H=Q(0);values=[]
            for n in range(24):
                if n:H+=Q(1,(2*n-1)**b)+Q(1,(2*n)**b)
                values.append(H/(2*n+1)**a)
            for n in range(1,25):
                diff=values[:n];terms=[]
                while diff:
                    terms.append(diff[0]);diff=[diff[j]-diff[j+1] for j in range(len(diff)-1)]
                assert terms[0]==0 and all(t<0 for t in terms[1:])
                assert sum((v/Q(2**(j+1)) for j,v in enumerate(terms)),Q(0))==euler_sum(values[:n])
                counts['euler_weight_and_sign_cases']+=1
    certs=[];reductions=[];latex=[]
    for w in range(2,17,2):
        latex.append(r'\subsection*{Weight '+str(w)+'}')
        for a in range(1,w):
            b=w-a;rhs=parity_symbol(a,b)
            reductions.append({'weight':w,'a':a,'b':b,'expression':str(rhs),'latex':tex(rhs)})
            terms = rhs.as_ordered_terms()
            chunks = []
            for j in range(0, len(terms), 3):
                line = ''
                for k, term in enumerate(terms[j:j+3], j):
                    t = tex(term)
                    line += t if k == 0 or t.startswith('-') else '+' + t
                chunks.append(line)
            latex.append(r'\begin{align*}g_{'+str(a)+','+str(b)+r'}={}&' +
                         (r'\\'+'\n'+r'&{}').join(chunks) + r'.\end{align*}')
            if w<=args.max_weight:
                lhs_iv=gaussian_interval(a,b,N);rhs_iv=symbolic_interval(rhs,N)
                assert lhs_iv.overlaps(rhs_iv),(a,b)
                # Interval agreement is evidence; the exact parity proof establishes equality.
                certs.append({'a':a,'b':b,'terms':N,'g_interval':lhs_iv.outward(110),
                              'rhs_interval':rhs_iv.outward(110),'intervals_overlap':True})
    counts['parity_interval_checks']=len(certs)
    json_write('even_weight_reductions.json',reductions)
    (ROOT/'data'/'even_weight_tables.tex').write_text('\n'.join(latex)+'\n')
    json_write('gaussian_interval_certificates.json',certs)
    lhs=Interval(Q(0),Q(0))
    for a,c in [(4,576),(3,288),(2,736),(1,960)]:lhs+=c*gaussian_interval(a,5-a,N)
    rhs=symbolic_interval(21*B2*Z3-480*B4*L,N)
    assert lhs.overlaps(rhs)
    json_write('weight_five_certificate.json',{'combination_of_shuffle_rows':[960,-224],
        'row_order':['Li_1(i) Li_4(i)','Li_2(i) Li_3(i)'],
        'coordinates_g14_g23_g32_g41':[960,736,288,576],
        'rhs':str(21*B2*Z3-480*B4*L),'lhs_interval':lhs.outward(105),'rhs_interval':rhs.outward(105)})
    counts['weight_five_interval_checks']=1
    ranks=[]
    for w in range(3,args.rank_max+1,2):
        keys,A,rhs,labels=system(w)
        nong=[j for j,k in enumerate(keys) if k[2:]!=(1,0)]
        ra=len(A.to_DM().to_field().rref()[1]);rb=len(A[:,nong].to_DM().to_field().rref()[1])
        assert ra==5*w-6 and ra-rb==w//2
        ranks.append({'weight':w,'variables':len(keys),'rows':A.rows,'rank':ra,
                      'rank_non_gaussian_columns':rb,'relations_supported_on_gaussian_columns':ra-rb})
    counts['exact_formal_rank_cases']=len(ranks);json_write('formal_rank_data.json',ranks)
    keys,A,rhs,labels,target,witness=s4_witness()
    assert A*witness==s.zeros(A.rows,1) and (target.T*witness)[0]==1
    json_write('s4_linear_module_obstruction.json',{
        'meaning':'Not in the Q-row span of this specified weight-five depth-two matrix; NOT a counterexample to S4.',
        'column_order':keys,'matrix':[[int(x) for x in row] for row in A.tolist()],
        'row_labels':labels,'target':[str(x) for x in target],
        'annihilating_vector':[str(x) for x in witness],
        'matrix_times_vector':'zero','target_dot_vector':'1'})
    counts['s4_formal_obstruction']=1
    # This is a certified enclosure of a conjectured difference, not a proof it is zero.
    S4 = odd_harmonic_interval(4, N)
    S4_rhs = (Q(58, 7)*gaussian_interval(4, 1, N)
              + Q(24, 7)*gaussian_interval(3, 2, N)
              + symbolic_interval(s.Rational(19, 3584)*pi**5-2*B4*L, N))
    assert S4.overlaps(S4_rhs)
    json_write('s4_interval_certificate.json', {
        'status': 'CONJECTURE; exact interval agreement does not prove equality',
        'terms': N, 'lhs': S4.outward(110), 'rhs': S4_rhs.outward(110),
        'difference': (S4-S4_rhs).outward(118),
        'lhs_tail_bound': f'({N}+1)/(81*2**{N})'})
    counts['s4_certified_candidate_checks']=1
    # Derived height-one formula and two additional weight-seven identities.
    for m in range(2,13):
        w=2*m
        value=(m-1)*beta_symbol(w)-sum(zeta_symbol(2*j+1)*beta_symbol(w-2*j-1) for j in range(1,m))
        value-=s.Rational(1,2**(w+1))*(1-s.Rational(2)**(2-w))*pi*zeta_symbol(w-1)
        assert s.expand(value-parity_symbol(w-1,1))==0
    counts['height_one_exact_cases']=11
    A7=shuffle_matrix(7);products=s.Matrix([s.im(single_symbol(p,1)*single_symbol(7-p,1)) for p in range(1,4)])
    extra=[]
    for coeffs in [[525,-31,0],[0,-7,25]]:
        v=s.Matrix([coeffs]);row=v*A7;right=s.expand((v*products)[0])
        assert right.coeff(pi,7)==0
        iv=sum((int(c)*gaussian_interval(a,7-a,N) for a,c in enumerate(row,1)),Interval(Q(0),Q(0)))
        assert iv.overlaps(symbolic_interval(right,N))
        extra.append({'shuffle_coefficients':coeffs,'gaussian_coefficients':[int(x) for x in row],
                      'rhs':str(right),'lhs_interval':iv.outward(100),
                      'rhs_interval':symbolic_interval(right,N).outward(100)})
    counts['weight_seven_exact_and_interval_cases']=2;json_write('weight_seven_identities.json',extra)
    summary={'status':'PASS','counts':counts,'total_check_cases':sum(counts.values()),
             'terms':N,'certified_decimal_output_digits':110,
             'seconds':round(time.time()-start,3),'python':platform.python_version(),
             'sympy':s.__version__,
             'scope':'Analytic proofs are in the article; exact algebra and rational interval calculations are complementary checks, not an independence proof.'}
    json_write('verification_summary.json',summary);print(json.dumps(summary,indent=2))
if __name__=='__main__':main()
