"""Audit the literal q-cubed to q-squared deletion from current complete76."""
import argparse
from collections import Counter
from itertools import product
import json
from pathlib import Path
import sys
import sympy as sp

VERIFICATION = Path(__file__).resolve().parents[2] / 'verification'
sys.path.insert(0, str(VERIFICATION))
import explore_fixed_raw_universal_76 as prior
import explore_five_adic_dummy_control as control


def source_audit():
    schedule = [(name, op, 'Lbig' if left == 'n2' else left,
                 'Lbig' if right == 'n2' else right)
                for name, op, left, right in prior.SCHEDULE if name != 'n2']
    env = prior.fixed_environment(prior.SYM)
    runner = prior.previous.previous.previous.previous.bridge.baseline.run_schedule
    runner(schedule, env)
    z = prior.SYM
    sources = [sp.expand(s.subs({z['w']: z['w']/z['q'],
                                 z['s']: z['s']/z['q']}, simultaneous=True))
               for s in prior.source_residuals()]
    assert all(s.is_polynomial(*z.values()) for s in sources)
    U = z['j']*z['c'] - (2*z['r']+1)
    correction = sources[12]*(U**2-z['y_aux']**2)
    records = []
    for ix, ((left, right), source) in enumerate(zip(prior.EQUALITIES, sources)):
        actual = sp.expand(env[left]-env[right])
        adjust = correction if ix == 13 else 0
        sign = 1 if sp.expand(actual-source-adjust) == 0 else -1
        assert sp.expand(actual-sign*source-adjust) == 0, ix
        records.append(dict(index=ix, equality=[left, right], sign=sign))
    counts = Counter('M' if row[1] == '*' else 'A' for row in schedule)
    assert counts == {'M': 40, 'A': 35} and len(schedule) == 75
    assert len(sources) == len(prior.EQUALITIES) == 19 and len(prior.NAMES) == 30
    assert env['wn2'] == z['w']*z['q']**2
    assert env['sn2'] == z['s']*z['q']**2
    assert sp.expand(env['innerC']-(z['DC']+z['B']*z['DR']+z['w']*z['q']**2)*z['C']) == 0
    return dict(operations=75, multiplications=40, additions_subtractions=35,
                equations=19, positive_witnesses=30, schedule=[list(r) for r in schedule],
                sources=records, strong_auxiliary_norm_retained=True)


def compiler_checks():
    examples = [([(0,)*9, (1,)*9], 2),
                ([(0,)*9, (1,)*9, (2,)*9], 3),
                (list(product(range(2), repeat=9))[:3], 2),
                (list(product(range(2), repeat=9))[:100], 2)]
    records = []
    for windows, alphabet in examples:
        c = prior.compile_windows(windows, alphabet)
        K, b, L = len(c.positions), c.radix_bits, c.L
        E = max(c.positions)
        T = sum(v.bit_count() for v in c.DCpoly.values())
        assert all(0 < v < c.R for v in c.DCpoly.values())
        assert K == c.m+1 and K >= 16 and E >= K-1
        assert L > 7*E and L >= 7*K-6
        assert all(v < c.R for v in c.coeff.values()) and len(c.coeff) <= K
        assert T <= 2*K*b+5
        assert c.d-c.m-2*(T+2) >= (3*K-6)*b-K-13 >= 2*K-19 > 0
        assert c.dummy and c.unit_mod5 != 0
        assert max(c.MFpoly.values()) <= c.R//2-2
        assert K*(2*sum(c.coeff.values())+6) <= c.R//2-2
        records.append(dict(alphabet=alphabet, windows=len(windows), native_positions=K,
                            inner_bits=b, cell_length=L, cell_bits=c.d,
                            verification_mask_population=c.m, DC_population=T,
                            population_margin=c.d-c.m-2*(T+2),
                            correction=c.high_correction,
                            full_compiler_q_materialized=False))
    assert {r['correction'] for r in records} == {0, 1}
    return records


def packing_checks():
    cases = 0
    for n in range(2, 5):
        q = 1 << n
        Q = q*q
        for Z in range(1, q):
            for F in range(1, q):
                for MC, MF in ((2, 1), (1, 2), (q//2, q//4)):
                    if Z & MC or Z+MC >= q or F+MF >= q:
                        continue
                    S, M = Z+q*F, MC+q*MF
                    r = (Q-S)*(Q-1)+M
                    assert r == (Q-S-1)*Q+S+M
                    assert r.bit_count() == 2*n+MC.bit_count()+(F+MF).bit_count()-F.bit_count()
                    cases += 1
    q, Z, F, M, G, slot, D = sp.symbols('q Z F M G slot D')
    packed = lambda z, f: (q*q-z-q*f)*(q*q-1)+M
    change = sp.expand(packed(Z+G*slot, F+D*G*slot)-packed(Z, F))
    assert sp.expand(change+G*(q*q-1)*(1+q*D)*slot) == 0
    return dict(population_identity_cases=cases, exact_dummy_change=str(change))


def outer_examples():
    # Illustrative fixed masks, explicitly not a full universal compiler.
    d, N, b, B, R, MC, MF, DC, DR, e = 5, 625, 1, 32, 2, 26, 10, 1, 1, 2
    q = 1 << (d*N)
    Q, qm1 = q*q, q-1
    J = qm1//(B-1)
    M = (MC+q*MF)*J
    rotate = lambda C: (B*C) % qm1
    packed = lambda Z, F: (Q-Z-q*F)*(Q-1)+M
    table = control.subgroup_table(d, N)
    records = []
    for x in (1, 3, 7, 20, 100):
        W = R*B**(2*x)
        C0 = 1+W
        F0 = DC*C0+(DR+1)*rotate(C0)
        r0 = packed(C0-W, F0)
        Gamma = R**e*(Q-1)*(1+q*(DC+B*DR+B))
        target = (2*r0+1-d)*pow(2*Gamma, -1, d*N) % (d*N)
        subset = control.subset_for_target(d, N, target, table)
        D = sum(B**i for i in subset['indices'])
        C, Z = C0+R**e*D, 1+R**e*D
        F = DC*C+(DR+1)*rotate(C)
        r = packed(Z, F)
        alpha = q-C-2*d*x
        assert (B-1)*J == q-1 and C == Z+W
        assert alpha > 0 and C+alpha+2*d*x == q
        assert 0 < Z < C < q and 0 < F < q
        assert Z+MC*J < q and F+MF*J < q
        assert not (Z & (MC*J)) and F & (MF*J)
        assert r == r0-Gamma*D and (2*r+1) % (d*N) == d
        assert Q <= r < Q*Q and r % 2 == 1
        assert r.bit_count() >= 2*d*N and r.bit_count() < 3*d*N
        assert F.bit_count() <= (DC.bit_count()+2)*C.bit_count()
        kR = (B*C-rotate(C))//qm1
        assert B*C-rotate(C) == kR*qm1 and kR >= 0
        assert (DC+B*DR+B)*C == F+(DR+1)*kR*qm1
        assert 3 <= 2*d*x+b < 2*r+1
        records.append(dict(x=x, selected_dummy_bits=len(subset['indices']),
                            q_bits=q.bit_length(), packed_r_bits=r.bit_length(),
                            packed_population=r.bit_count(), weakened_threshold=2*d*N,
                            original_threshold=3*d*N, F_population=F.bit_count(),
                            forbidden_F_bits=(F & (MF*J)).bit_count(),
                            actual_main_exponent_residue=(2*r+1) % (d*N),
                            modulus=d*N, intended_exponent=d,
                            all_outer_bounds=True, full_Pell_coordinates_materialized=False))
    return dict(parameters=dict(B=B, d=d, b=b, N=N, MC=MC, MF=MF, DC=DC, DR=DR),
                examples=records, scope='Illustrative fixed masks; the all-compiler extension is proved separately')


def verify():
    return dict(status='PASS_CURRENT75_SQUARED_SCALE_ALL_INPUT_REFUTATION',
                source=source_audit(), compilers=compiler_checks(), packing=packing_checks(),
                illustrative_outer=outer_examples(),
                theorem='Every fixed complete76 compiler and every positive ordinary input have full positive witnesses after the literal q-cubed scale deletion',
                evidence='Symbolic source, sparse compiler bounds, exact illustrative outer tuples, and a parametric full positive proof',
                scope='Distinct75 source; older auxiliary-scale and input-gap candidates remain open',
                established_complete_universal_bound=76)


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    result = json.loads(json.dumps(result))
    receipt = Path(__file__).with_suffix('.json')
    if args.write:
        receipt.write_text(json.dumps(result, indent=2)+'\n', encoding='utf-8')
    else:
        assert json.loads(receipt.read_text(encoding='utf-8')) == result, 'receipt mismatch'
    print(json.dumps(dict(status=result['status'], operations=result['source']['operations'],
                          compiler_layouts=len(result['compilers']),
                          outer_examples=len(result['illustrative_outer']['examples'])), indent=2))
