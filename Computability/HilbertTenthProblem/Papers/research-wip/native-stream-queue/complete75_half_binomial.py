"""Complete half-binomial75 source and shifted-mask arithmetic audit.

The complete theorem is proved in1980/FIXED_RAW_UNIVERSAL_75_PROOF.md.
Independent full integration reviews pass; this checker supplies source and
finite arithmetic evidence, not a formal proof.
"""
import argparse
from collections import Counter
import json
from pathlib import Path
import sys
import sympy as sp

VERIFICATION = Path(__file__).resolve().parents[2] / 'verification'
sys.path.insert(0, str(VERIFICATION))
import explore_fixed_raw_universal_76 as prior


def source_audit():
    schedule = []
    for name, op, left, right in prior.SCHEDULE:
        if name == 'tr1':
            continue
        if name == 'tauplus1':
            schedule.append(('tau_square', '*', 'tau', 'tau'))
        elif name == 'R9':
            schedule.append(('R9', '-', 'tau_square', 1))
        else:
            schedule.append((name, op, left,
                             'r' if right == 'tr1' else right))
    z = prior.SYM
    env = prior.fixed_environment(z)
    env['MF'] = z['MF'] + z['B'] - 1
    runner = prior.previous.previous.previous.previous.bridge.baseline.run_schedule
    runner(schedule, env)
    q = z['q']; X = z['w']*q**3; Y = z['s']*q**3
    Delta = z['a']**2 + 4*z['a'] + 3
    U = z['j']*z['c'] - z['r']
    sources = [sp.expand(s.subs(z['MF'], z['MF']+z['B']-1))
               for s in prior.source_residuals()]
    sources[5] = sp.expand(((X*Y)**2+X)*(z['k']*Y)**2-z['tau']**2+1)
    sources[13] = sp.expand(Delta*(z['f']**2-1)*(U**2-z['y_aux']**2)
                            - 1 + z['y_aux']**2)
    sources[14] = sp.expand(U-z['o']*z['f']+z['c'])
    correction = sources[12]*(U**2-z['y_aux']**2)
    records = []
    for index, ((left, right), source) in enumerate(zip(prior.EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if index == 13 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, index
        records.append(dict(index=index, equality=[left,right], sign=sign,
                            source=str(source), correction=str(sp.expand(adjust))))
    counts = Counter('M' if op == '*' else 'A' for _,op,_,_ in schedule)
    assert len(schedule) == 75 and counts == {'M':41, 'A':34}
    assert len(prior.NAMES) == 30 and len(prior.EQUALITIES) == 19
    assert env['H17'] == U
    assert sp.expand(env['R11']-z['r']-1-z['h']*X*Y) == 0
    assert sp.expand(env['R9']-z['tau']**2+1) == 0
    assert all(name != 'tr1' for name,*_ in schedule)
    return dict(operations=75, multiplications=41, additions_subtractions=34,
                positive_witnesses=30, equations=19,
                fixed_mask_alias='MF_source=MF+B-1',
                schedule=[list(row) for row in schedule], sources=records,
                unchanged_input_operations=14, strong_auxiliary_square_retained=True)


def packing_audit():
    # Finite arithmetic instances, not compiled universal machines.
    cases = boundaries = valid = rejected = 0
    examples = []
    for d in range(3,7):
        B = 2**d
        for MC in range(2,B,4):
            for MF in range(4,B,8):
                if MC.bit_count()+MF.bit_count() != d:
                    continue
                q=B; J=1; lam=q*q
                Tprime=MC*J+1+q*(MF*J-1)
                assert 0 < Tprime < lam-1
                assert Tprime.bit_count() == d+2
                for Z in range(1,q):
                    for F in range(1,q+1):
                        S=Z+q*F; Sshift=S-1
                        R=(lam-S)*(lam-1)+(MC+q*(MF+B-1))*J
                        assert R == (lam-Sshift)*(lam-1)+Tprime
                        if R <= 0:
                            continue
                        assert 3*q+1 <= R < q**4
                        assert Sshift <= lam
                        target=3*d+2
                        admitted=(R.bit_count() >= target)
                        if Sshift == lam:
                            assert Z == 1 and F == q and R == Tprime
                            assert not admitted
                            boundaries += 1
                        else:
                            masked = (Sshift&Tprime)==0
                            assert R.bit_count() <= target
                            assert admitted == masked
                            assert masked == (((Z-1)&(MC*J+1))==0 and (F&(MF*J-1))==0)
                            if admitted:
                                assert F < q and R >= q*q and R%4 == 3
                                assert ((R-1)//2).bit_count()-1 == 3*d
                                valid += 1
                                if len(examples) < 4:
                                    examples.append(dict(q=q,MC=MC,MF=MF,Z=Z,F=F,R=R,
                                                         population=R.bit_count(),
                                                         half_binomial_valuation=((R-1)//2).bit_count()-1))
                            else:
                                rejected += 1
                        cases += 1
    # Repeated masks test the global +2 independently of one-cell fixtures.
    repeated=0
    for d,MC,MF in ((3,6,4),(4,10,12),(5,26,12),(6,58,12)):
        B=2**d
        assert MC%4==2 and MF%8==4 and MC.bit_count()+MF.bit_count()==d
        for N in range(1,13):
            q=B**N;J=(q-1)//(B-1)
            Tprime=MC*J+1+q*(MF*J-1)
            assert 0<Tprime<q*q-1 and Tprime.bit_count()==d*N+2
            assert (MF*J & -(MF*J)) == 4
            repeated+=1
    return dict(finite_positive_outer_tuples=cases,boundary_rejections=boundaries,
                exact_mask_passes=valid,mask_rejections=rejected,
                repeated_mask_cases=repeated,examples=examples,
                scope='Toy masks only; universal compiler and Pell witnesses require separate proofs')


def verify():
    return dict(status='PASS_COMPLETE_RAW_UNIVERSAL75_SOURCE_AND_PACKING',
                source=source_audit(),packing=packing_audit(),
                proof_status='Complete mathematical proof; three independent full integration reviews PASS; not Lean formalized',
                established_complete_universal_bound=75)


if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');args=parser.parse_args()
    result=verify();receipt=Path(__file__).with_suffix('.json')
    if args.write:receipt.write_text(json.dumps(result,indent=2)+'\n')
    else:assert json.loads(receipt.read_text())==result,'receipt mismatch'
    print(json.dumps({k:v for k,v in result.items() if k!='source'},indent=2))
