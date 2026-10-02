"""The positive-complement86 candidate accepts every actual compiler input.

The theorem uses Dirichlet primes and irrational rotation. Finite checks below
verify the literal algebra, CRT mechanism, exact prime certificate and actual
rejecting-machine contract; they do not materialize a huge complete Pell zero.
"""
import argparse
from collections import Counter
from fractions import Fraction
from hashlib import sha256
import json
from math import gcd, lcm
from pathlib import Path
import random

import sympy as sp
import complete75_positive_complement86_obstruction as candidate
import complete75_weakened86_all_input_collapse as prime_tools
import complete75_weakened86_rejecting_compiler as rejecting

parent = candidate.parent
pell, pell_mod = parent.pell, candidate.pell_mod


def theorem_contract():
    rows, comparisons, polynomial = candidate.sources()
    return dict(source_sha256=sha256(json.dumps(polynomial).encode()).hexdigest(),
        certificate_operations=len(rows), polynomial_operations=len(polynomial),
        multiplications=48, additions_subtractions=38, positive_witnesses=19,
        exact_degree=203, comparisons=comparisons,
        hypotheses='B=2^d; d positive odd and not divisible by3; b positive odd; '
                   'DC,DR,MC,MF,x positive integers. No mask parity or population condition is needed.',
        width_recipe='Choose a power of5 N with q=B^N>=32 and q>2dx+2; '
                     'Jrep=(q-1)/(B-1). All actual compiler widths also allow N=1 when this input bound holds.',
        conclusion='Every positive input has infinitely many full positive19-coordinate zeros '
                   'of this positive-complement86 source with R>q^4, C=0 and negative input Pell root.',
        existence_dependencies=['Dirichlet primes in a coprime arithmetic progression',
                                'irrational rotation', 'normalized positive auxiliary lift'],
        actual_compiler_counterexample='The frozen rejecting helical compiler at x=1.',
        established_75_87_unchanged=True, giant_witness_materialized=False)


def exponent(D):
    assert type(D) is int and D > 0 and D % 2 and D % 3
    # e=1 mod3D and e=3 mod4; then increase within this exact class.
    e = 1+3*D*((2*pow(3*D, -1, 4)) % 4)
    e += 12*D*max(0, (3*D-e+12*D-1)//(12*D))
    assert e >= 3*D and e % (3*D) == 1 and e % 4 == 3
    return e


def width_audit():
    records = []
    for d in (1, 5, 7, 11, 13, 17, 19, 25):
      for N in (1, 5, 25):
        D=d*N; q=1<<D; M=q*q-1; m=M//3; e=exponent(D)
        assert M == 3*m and m % 3 and gcd(e,D) == 1
        assert gcd((pow(2,e,M)+1)%M,M) == 3
        assert (pow(2,e,9)+1)%9 in (3,6)
        coefficient = (q**3*((1<<e)+1))//3
        assert gcd(coefficient,m) == 1
        s0=(-pow(coefficient,-1,m))%m if m>1 else 0
        Cp=4*coefficient
        assert (Cp*s0+1)%m == (-3)%m
        assert gcd(Cp*s0+1,Cp*m) == 1 and gcd(Cp*m,3) == 1
        z3=((1-Cp*s0)*pow(Cp*m,-1,3))%3
        start=Cp*(s0+m*z3)+1; stride=3*Cp*m
        assert start%3 == 2 and gcd(start,stride) == 1
        records.append(dict(d=d,N=N,D=D,e=e,prime_progression_coprime=True))
    return records


def prime_host():
    # This host satisfies the theorem's arithmetic width conditions. Its masks
    # below are scalar tests, not an exported machine or a full Pell-zero tuple.
    q,D,e,s=32,5,31,1673
    X=1<<e; Y=q**3*s; M=q*q-1; m=M//3
    A=Y*(X+1)+2; H=4*A-5; ell=H//3; T=2*(ell-1)
    assert e==exponent(D) and ell==156969212085403649
    certificate=prime_tools.lucas_certificate(ell)
    nodes=prime_tools.verify_lucas(certificate)
    assert H==3*ell and ell%3==2 and ell>3*M and ell%m==(-3)%m
    assert A%M==M-1 and pow(2,T,H)==1
    assert gcd(T,M)==gcd(H,q*(q-1))==1
    return dict(q=q,D=D,e=e,s=s,X=X,Y=Y,A=A,a=A-2,Delta=A*A-1,
        H=H,E=X*Y,P=2*X*Y*Y+1,M=M,ell=ell,T=T,
        recursive_Lucas_certificate=certificate,verified_prime_nodes=nodes)


def progression(data, mask, Fv, input_term):
    """Exact CRT solution. rho,Z stay fixed; alpha grows with the main index."""
    q,M,H,E,T,e=(data[k] for k in ('q','M','H','E','T','e'))
    assert type(mask) is int and type(Fv) is int and type(input_term) is int
    assert mask>0 and Fv>0 and input_term>0
    assert gcd(T,M)==1 and gcd(H,q*(q-1))==1 and e%4==3
    L=lcm(T,4)
    p0=e+L*((mask-e)*pow(L,-1,M)%M)
    W0=(p0-mask)//M
    modulus=q*(q-1)
    rho=((q-W0-Fv)*pow(H,-1,modulus))%modulus or modulus
    Z=Fv+H*rho
    step=lcm(L,M*modulus,E)
    # A finite exact lift pays all elementary positive coordinates and gamma>rho.
    threshold=max(mask+M*((q-1)*Z+q*(input_term+1)),q**4,
                  data['X']+rho*H,data['X']+1)
    p0+=step*max(0,(threshold-p0)//step+1)
    assert p0>threshold and p0%4==3 and (p0-mask)%M==0
    U,rem=divmod((p0-mask)//M-(q-1)*Z,q)
    assert rem==0 and U>input_term and (Z+U-1)%(q-1)==0
    return dict(p0=p0,step=step,rho=rho,Z=Z,input_term=input_term,
                n_modulus=E//2,n_residue=((p0+1)//2)%(E//2))


def modular_audit(d):
    rng=random.Random(860428); counts=Counter(); examples=[]
    for x,b in ((1,1),(2,3),(3,5),(5,7)):
        u=2*d['D']*x+b; chi,kappa=pell(d['A'],u)
        Fv=chi+d['a']*kappa
        assert (kappa-u)%d['Delta']==0 and kappa>u
        for mask in [1,2,3,4,6,12,d['M'],d['M']+1]+[rng.randrange(1,10**12) for _ in range(24)]:
            rec=progression(d,mask,Fv,2*d['D']*x)
            for z in (0,1,10**8,rng.randrange(10**20)):
                p=rec['p0']+rec['step']*z; q=d['q']; M=d['M']
                W=(p-mask)//M
                U,rem=divmod(W-(q-1)*rec['Z'],q)
                assert rem==0 and U>2*d['D']*x and U+rec['Z']>q
                assert (rec['Z']+U-1)%(q-1)==0
                assert M*((q-1)*rec['Z']+q*U)+mask==p
                assert p%4==3 and p>q**4 and p>d['X']+rec['rho']*d['H']
                assert pow(2,p,d['H'])==d['X']
                assert (2*rec['n_residue']-p-1)%d['E']==0
                n=rec['n_residue']+rec['n_modulus']*(1+rng.randrange(10**20))
                assert (2*pell_mod(d['P'],n,d['E'])[1]-p-1)%d['E']==0
                counts['exact_main_input_transport_first_progression_points']+=1
            counts['independent_mask_input_progressions']+=1
            if len(examples)<4:examples.append(dict(x=x,b=b,mask=mask,**rec))
    # The linear congruence is also tested outside the convenient unit case.
    # It is solvable iff gcd(H,q(q-1)) divides q-W-Fv.
    for q in (4,8,16,32):
      Q=q*(q-1)
      for H in (3,9,15,21,25,31):
       g=gcd(H,Q)
       for W in range(Q):
        Fv=7; target=q-W-Fv
        exists=any((H*r-target)%Q==0 for r in range(Q//g))
        assert exists == (target%g==0)
        counts['CRT_iff_residue_classes']+=1
    return dict(checks=dict(counts),examples=examples,
        scope='Exact congruence and positivity checks for outer coordinates only; '
              'no finite fixture is claimed to include the strict ratios or a full Pell zero.')


def divide(a,b):
    return a/b if isinstance(a,sp.Basic) or isinstance(b,sp.Basic) else Fraction(a)/Fraction(b)


def mapped_values(data, variables):
    B,q,d,b,x,MC,MF,DC,DR,X,Y,rho=(data[n] for n in
        ('B','q','d','b','x','MC','MF','DC','DR','X','Y','rho'))
    p,c,k,first,main,kappa,chi_v,f,i,V,y=variables
    J=divide(q-1,B-1); M=q*q-1; mask=(MC+q*(MF+B-1))*J
    a=Y*(X+1); A=a+2; H=4*a+3; Delta=A*A-1; E=X*Y
    Z=chi_v+a*kappa+rho*H
    U=divide(divide(p-mask,M)-(q-1)*Z,q)
    gamma=divide(main-a*c-X,H)
    return dict(Jrep=J,F=Z+U,alpha=U-2*d*x,zplus=divide(Z+U-1,q-1),
        f=f,h=divide(k-p-1,E),i=i,j=divide(V+p,c),o=divide(V+c,f),
        s=divide(Y,q**3),w=divide(X,q**3),tau_gap=first-X*Y*Y*k,
        eta=c-k*Y,zeta=k*(Y+1)-c,y_aux=y,Z=Z,
        delta=divide(kappa-2*d*x-b,Delta),rho=rho,sigma=gamma-rho,
        B=B,DC=DC,DR=DR,MC=MC,MF=MF,cell_bits=d,inner_bits=b,x=x)


def scalar_factors(data, variables):
    p,c,k,first,main,kappa,chi_v,f,i,V,y=variables
    X,Y=data['X'],data['Y']; a=Y*(X+1); Delta=(a+2)**2-1; L=X*Y*Y
    return [first**2-L*(L+1)*k**2,main**2-Delta*c**2,
            chi_v**2-Delta*kappa**2,Delta**2*i**2*c**4*(V**2-y**2)+y**2,
            1,1,f**2-Delta*i**2*c**4,1]


def literal_audit():
    counts=Counter(); rng=random.Random(864827); poly=candidate.sources()[2]
    variables=sp.symbols('p c k first main kappa chi_v f i V y',nonzero=True)
    records=[]
    for B,q,d,b,X,Y in ((8,64,3,1,11,7),(16,16,4,3,17,5),
                       (32,32,5,5,19,11),(32,1024,5,25,23,13)):
        data=dict(B=B,q=q,d=d,b=b,x=2,MC=7,MF=10,DC=3,DR=5,X=X,Y=Y,rho=2)
        env=parent.eliminated.run(poly,parent.eliminated.fixed_inputs(mapped_values(data,variables)))
        expected=scalar_factors(data,variables)
        for name,want in zip(parent.FACTOR_NAMES,expected):assert sp.cancel(env[name]-want)==0
        assert sp.cancel(env['marked_rhs'])==0 and sp.cancel(env['r_lhs']-variables[0])==0
        assert sp.cancel(env['exponent_rhs']+variables[6])==0
        assert sp.cancel(env['index_rhs']-variables[5])==0
        assert sp.cancel(env['polynomial']-(sp.prod(expected)-1))==0
        counts['symbolic_complete_eight_factor_output_maps']+=1
        for signed in (False,True):
          for _ in range(32):
            values=[rng.randrange(1,10)*(-1 if signed and rng.randrange(2) else 1) for _ in variables]
            mapped=mapped_values(data,values)
            assert mapped==mapped_values(data,list(map(Fraction,values)))
            assert not any(isinstance(v,float) for v in mapped.values())
            env=parent.eliminated.run(poly,parent.eliminated.fixed_inputs(mapped))
            expected=scalar_factors(data,values)
            assert [env[n] for n in parent.FACTOR_NAMES]==expected
            assert env['polynomial']==sp.prod(expected)-1
            counts['exact_rational_complete_source_maps']+=1;counts['signed_maps']+=signed
        records.append(data)
    return dict(checks=dict(counts),contexts=records,
        scope='Exact rational identities use arbitrary signed root placeholders. '
              'Integer positivity and simultaneous unit factors follow from the theorem, not these fixtures.')


def inherited_actual_compiler():
    """Reuse the reviewed complete finite compiler recipe, not its old86 theorem."""
    path=Path(rejecting.__file__).with_suffix('.json')
    saved=json.loads(path.read_text())
    k=saved['window_alphabet']['exact_full_window_count']
    a=saved['window_alphabet']['tile_count']
    layout=rejecting.layout_metadata(k,a)
    assert layout==saved['compiler']['actual_rejecting_layout']
    assert k==12719417040 and a==18 and layout['cell_bits']==5**35
    assert layout['inner_bits']==5**17 and layout['cell_bits']%2 and layout['cell_bits']%3
    machine=rejecting.rejecting_machine()
    assert len(rejecting.tiles(machine))==18
    assert all(machine.delta('start',v)[0]=='loop' for v in machine.alphabet)
    assert all(machine.delta('loop',v)==('loop',v,0) for v in machine.alphabet)
    assert machine.delta('start',1)==('loop',2,0)
    semantic_cases=0
    for x in range(1,33):
        history=rejecting.semantics.unary.history_for(machine,2*x+1,limit=7)
        assert [state for _,_,state in history]==['start']+['loop']*7
        assert all(head==0 for _,head,_ in history)
        semantic_cases+=1
    return dict(frozen_compiler_recipe=layout,
        inherited_finite_recipe_receipt_sha256=sha256(path.read_bytes()).hexdigest(),
        newly_rechecked_machine_invariant=True,new_semantic_traces=semantic_cases,
        false_input=1,ordinary_language='empty set',candidate_language='all positive integers',
        general_compiler_scope='Every actual modified helical compiler has d,b powers of5; '
            'the present arithmetic theorem therefore applies to every positive input on each such slice.',
        scope='The complete window enumeration and compiler proof are reused from the frozen rejecting packet. '
            'Only its machine invariant and compressed layout are rechecked here; its different weakened86 '
            'arithmetic theorem is not used. No giant compiler constants or full zero are materialized.')


def growth_audit():
    count=0
    for A in (3,4,9,21,32):
      for p in range(2,42):
        chi,c=pell(A,p); prev=pell(A,p-1)[1]
        assert c>=2*p and chi-(A-2)*c==2*c-prev>c
        count+=1
    first=0
    for P in (3,5,9,17):
      for n in range(2,34):
        chi,psi=pell(P,n); prev=pell(P,n-1)[1]
        assert chi-(P-1)*psi==psi-prev>0 and psi>n
        first+=1
    return dict(main_projection_growth_cases=count,correct_first_gap_cases=first)


def verify():
    d=prime_host()
    return dict(status='PASS_POSITIVE_COMPLEMENT86_ACTUAL_ALL_INPUT_COLLAPSE',
        contract=theorem_contract(),widths=width_audit(),prime_host=d,
        CRT=modular_audit(d),literal_source=literal_audit(),growth=growth_audit(),
        actual_compiler=inherited_actual_compiler(),
        full_positive_recipe='p on the proved progression; n on its fixed E/2 residue with strict Pell ratios; '
            'rho,Z fixed by CRT; alpha=((p-mask)/M-(q-1)Z)/q-2dx; all other coordinates as in the note.',
        conclusion='This specific86 source accepts every positive input on every actual modified compiler slice, '
            'including x1 for the exact rejecting compiler. Established75/87 results are unchanged.',
        limitations='Existence uses Dirichlet and irrational rotation. Finite source/CRT fixtures are not '
            'numerically materialized complete positive Pell zeros; no claim about all86 circuits is made.')


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=json.loads(json.dumps(verify()));path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(result['status']);print(result['contract']);print(result['CRT']['checks'])
