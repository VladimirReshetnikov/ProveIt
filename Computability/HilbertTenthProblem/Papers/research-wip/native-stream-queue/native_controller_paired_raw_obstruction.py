"""Raw2x filtered controllers: accepting every even x forces all x."""
import argparse
from itertools import product
import hashlib
import json
from pathlib import Path
import sympy as sp
import native_controller_paired_filter71 as prior


def normalization():
    f0,f1,f2,f3,H,q = sp.symbols('F0 F1 F2 F3 H q')
    alpha,beta,gamma,s,u0,cf = sp.symbols('alpha beta gamma s u0 cf')
    original = (s+cf)+(2*cf-u0)*H+u0*f2+gamma*f3+(alpha+u0)*f0+(beta+u0)*f1-q*cf
    centered = s+alpha*f0+beta*f1+gamma*f3
    correction = u0*(f0+f1+f2-H)+cf*(2*H+1-q)
    assert sp.expand(original-centered-correction)==0
    rows = []
    for aligned in (False,True):
        source = prior.source_check(True,aligned)
        last_control = source['sources'][19]['source']
        g0,g1,g2,gap = sp.symbols('g0 g1 g2 gap')
        assert sp.expand(sp.sympify(last_control).subs({g0:alpha,g1:beta,g2:gamma,gap:-s})-centered)==0
        rows.append(dict(operations=source['operations'],equations=source['equations'],
                         positive_witnesses=source['positive_existentials_excluding_x'],
                         source_sha256=hashlib.sha256(json.dumps(source,sort_keys=True).encode()).hexdigest()))
    return dict(original_minus_centered=str(sp.expand(correction)),source_audits=rows,
                source_family='Exact raw2x paired filter, positive four words, zero queues, complete integral carry graph')


def family(N):
    assert N>=2 and N%2==0
    triples = [((3**N-1)//2,[2]*N),
               (3*(3**N-1)//2,[0]+[2]*N),
               (3**(N+1)-1,[1]+[2]*N+[1])]
    for x,digits in triples:
        assert x>0 and x%2==0 and 2*x==prior.word(digits)
    return triples


def outgoing(k,raw,alpha,beta,gamma):
    reads = {0:[(0,0)],1:[(1,0),(0,1)],2:[(1,1)]}[raw]
    result = set()
    for d0,d1 in reads:
        appends = [(0,0)] if d0 else [(1,0),(0,1)]
        for a0,a1 in appends:
            numerator = k+alpha*a0+beta*a1+gamma*d1
            if numerator%3==0:
                result.add(numerator//3)
    return result


def prefixes():
    configs = survivors = nonzero_gamma = zero_gamma_nontrivial = trivial = 0
    states_checked = 0
    maxN = 0
    examples = []
    for alpha,beta,gamma,s in product(range(-4,5),repeat=4):
        G=abs(alpha)+abs(beta)+abs(gamma)
        C=max(abs(s),(G+1)//2);bound=2*C+abs(gamma)
        N=2
        while 3**N<=bound:N+=2
        maxN=max(maxN,N)
        rows=family(N)
        # In C only the leading1 and long2 block are required; the high1
        # makes the supplied ordinary input even and is not needed to infer k*.
        words=[rows[0][1],rows[1][1],rows[2][1][:-1]]
        ends=[]
        for digits in words:
            reached={s}
            for raw in digits:
                reached={nxt for k in reached for nxt in outgoing(k,raw,alpha,beta,gamma)}
                assert all(abs(k)<=C for k in reached)
                states_checked+=len(reached)
            if reached:
                assert len(reached)==1
                assert 2*next(iter(reached))==gamma
            ends.append(reached)
        configs+=1
        if not all(ends):continue
        survivors+=1
        assert 2*s==gamma
        assert alpha==gamma or beta==gamma
        assert gamma==0 or alpha==0 or beta==0
        if gamma:
            assert {alpha,beta}=={0,gamma}
            assert s%abs(gamma)!=0
            # Every variable term of the zero-endpoint source is divisible by gamma.
            nonzero_gamma+=1
            if len(examples)<3:
                examples.append(dict(alpha=alpha,beta=beta,gamma=gamma,s=s,N=N,
                                     conclusion='All three prefixes feasible, but the global endpoint fails modulo abs(gamma)'))
        elif alpha or beta:
            assert s==0 and alpha*beta==0
            for F0,F1 in product(range(1,9),repeat=2):
                assert alpha*F0+beta*F1!=0
            zero_gamma_nontrivial+=1
        else:
            assert s==0
            trivial+=1
    assert trivial==1 and nonzero_gamma and zero_gamma_nontrivial
    return dict(controller_tuples=configs,coordinate_range=[-4,4],prefix_compatible=survivors,
                reachable_prefix_states=states_checked,maximum_chosen_even_N=maxN,
                endpoint_congruence_rejections=nonzero_gamma,
                strict_append_positivity_rejections=zero_gamma_nontrivial,
                remaining_trivial_controllers=trivial,examples=examples,
                scope='Exhaustive bounded prefix tests and exact algebraic endpoint contradictions; no finite test is used as a universality proof')


def aligned_maps():
    count=0;examples=[]
    for ell in range(2,6):
        for x in range(1,21):
            m=ell
            while 3**m<=6*x:m+=ell
            W=3**m;q=W**3;t=3*m;Hm=(W-1)//2
            I0,I1=prior.paired.positive_split(2*x)
            fields=[W*Hm,Hm-I0,I0+W*W*Hm,I1+W*(Hm-I0)]
            assert min(fields)>0 and all(prior.boolean.native_boolean(f,t) for f in fields)
            assert sum(fields[:3])==(q-1)//2 and sum(fields)<q and sum(fields)%2==0
            assert prior.paired.direct_pair((I0,I1),fields,m,t)
            J,remJ=divmod(q-1,3**ell-1);K,remK=divmod(W-1,3**ell-1)
            assert remJ==remK==0 and min(J,K)>0
            count+=1
            if x==1:
                examples.append(dict(ell=ell,x=x,m=m,t=t,W=W,q=q,fields=fields,
                                     initial=[I0,I1],time_blocks=J,width_blocks=K))
    return dict(positive_outer_maps=count,block_lengths=[2,5],ordinary_inputs=[1,20],examples=examples,
                full_extension='By the proved positive paired Boolean converse; huge Pell coordinates not materialized')


def verify():
    families=[]
    for N in range(2,13,2):
        families.append(dict(N=N,ordinary_even_inputs=[x for x,_ in family(N)]))
    return dict(status='PASS_RAW_FILTERED_CONTROLLER_EXPRESSIVENESS_OBSTRUCTION',
                normalization=normalization(),families=families,prefix_tests=prefixes(),aligned_positive_maps=aligned_maps(),
                theorem='Accepting every positive even x forces acceptance of every positive x',
                scope='Raw sum I0+I1=2x and the fixed filter only; optional fixed block alignment; no general decidability claim',
                established_complete_universal_bound=76)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();path=Path(__file__).with_suffix('.json')
    if args.write:path.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(path.read_text())==result,'receipt mismatch'
    print(json.dumps({key:value for key,value in result.items() if key!='normalization'},indent=2))
