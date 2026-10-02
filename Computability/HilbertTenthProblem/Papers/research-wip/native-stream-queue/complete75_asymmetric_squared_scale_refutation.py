"""The literal X=w*q, Y=s*q**2 shortcuts accept every compiled input.

This is a refutation, not an improved universal bound.  The mathematical
construction uses the actual modified compiler and nineteen positive
coordinates.  Finite source, sparse-layout and Pell-component audits are
kept separate from the unmaterialized gigantic compiled zeros.
"""
import argparse
from collections import Counter, defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import random

import sympy as sp
import complete75_asymmetric_scale_tradeoffs as parent
import complete75_half_binomial_compiler as compiler

RETAINED = parent.RETAINED
FACTOR_NAMES = parent.FACTOR_NAMES


def rewrite(old, normalized=True):
    assert type(normalized) is bool
    assert old == parent.source(normalized), 'not the complete canonical asymmetric parent'
    nodes = {n: (op, a, b) for n, op, a, b in old}
    assert nodes['n2'] == ('*', 'Lbig', 'q')
    assert nodes['sn2'] == ('*', 's', 'n2')
    assert nodes['wn2'] == ('*', 'w', 'q')
    assert {n for n, op, a, b in old if 'n2' in (a, b)} == {'sn2'}
    rows = [(n, op, a, 'Lbig' if n == 'sn2' else b)
            for n, op, a, b in old if n != 'n2']
    parent.closure(rows)
    return rows


def source(normalized=True):
    return rewrite(parent.source(normalized), normalized)


def ledger(normalized=True):
    rows = source(normalized)
    count = Counter('M' if op == '*' else 'A' for n, op, a, b in rows)
    assert count == (dict(M=47, A=39) if normalized else dict(M=46, A=41))
    return dict(operations=len(rows), multiplications=count['M'],
                additions_subtractions=count['A'], certificate_operations=len(rows)-1,
                comparisons=1, positive_witnesses=19,
                status='REFUTED: all positive inputs on every actual modified compiler slice')


def theorem_contract():
    return dict(
        compiler='complete75_half_binomial_compiler.compile_windows followed by new_constants',
        hypotheses='Any fixed actual modified complete75 compiler and any positive ordinary input x.',
        conclusion='Both guarded squared-scale sources have a full positive integer nineteen-coordinate zero, with all eight factors equal to one.',
        scales='X=w*q and Y=s*q^2; q=B^N with N a sufficiently large power of five.',
        limits='Exact finite witness recipe and mathematical existence theorem; no enormous fixed compiler numerals or complete compiled Pell tuple are materialized.',
        sources=[dict(normalized=n, ledger=ledger(n),
                      sha256=hashlib.sha256(json.dumps(source(n)).encode()).hexdigest())
                 for n in (True, False)])


def divide(a, b):
    return a/b if isinstance(a, sp.Basic) or isinstance(b, sp.Basic) else Fraction(a)/Fraction(b)


def mapped_values(data, roots, normalized=True):
    """All nineteen exact coordinates; integrality/positivity is a theorem.

    Root placeholders are c,k,first,main,kappa,mu,f,t,V,y; t is psi_A(m),
    before multiplication by Delta in the ordinary strong coordinate.
    The same rational formulas also support independent off-zero audits.
    """
    assert type(normalized) is bool
    B, q, d, b, x, MC, MF, DC, DR, X, Y, Z, F, W = (
        data[n] for n in ('B','q','d','b','x','MC','MF','DC','DR','X','Y','Z','F','W'))
    c, k, first, main, kappa, mu, f, t, V, y = roots
    J = divide(q-1, B-1)
    R = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
    C = Z+W
    a, E = Y*(X+1), X*Y
    Delta, H = (a+2)**2-1, 4*a+3
    rho = divide(mu-a*kappa-W, H)
    gamma = divide(main-a*c-X, H)
    out = dict(Jrep=J, F=F, alpha=q-F-Z-C-2*d*x,
               zplus=divide((DC+B*DR+X)*C-F, q-1)+1,
               f=f, h=divide(k-R-1, E), i=divide(t if normalized else Delta*t, c*c),
               j=divide(V+R, c), o=divide(V+c, f),
               s=divide(Y, q*q), w=divide(X, q), tau_gap=first-X*Y*Y*k,
               eta=c-k*Y, zeta=k*(Y+1)-c, y_aux=y, Z=Z,
               delta=divide(kappa-2*d*x-b, Delta), rho=rho, sigma=gamma-rho)
    assert set(out) == set(RETAINED)
    return out


def scalar_factors(data, roots, normalized=True):
    c, k, first, main, kappa, mu, f, t, V, y = roots
    X, Y = data['X'], data['Y']
    Delta, L = (Y*(X+1)+2)**2-1, X*Y*Y
    T2 = Delta*Delta*t*t if normalized else Delta*(f*f-1)
    strong = f*f-Delta*t*t if normalized else 1+Delta*Delta*t*t-Delta*(f*f-1)
    return [first*first-L*(L+1)*k*k, main*main-Delta*c*c,
            mu*mu-Delta*kappa*kappa, T2*(V*V-y*y)+y*y,
            1, 1, strong, 1]


def run_mapped(data, roots, normalized=True):
    fixed = {n: data[n] for n in ('B','MC','MF','DC','DR')}
    fixed.update(cell_bits=data['d'], inner_bits=data['b'])
    values = mapped_values(data, roots, normalized)
    return parent.run(source(normalized), dict(values, x=data['x']), fixed)


def source_audit():
    rng, counts, records = random.Random(862026), Counter(), []
    for normalized in (True, False):
        old, rows = parent.source(normalized), source(normalized)
        for case in range(128):
            signed = case >= 64
            values = {n: rng.randrange(-6, 7) if signed else rng.randrange(1, 7)
                      for n in RETAINED+['x']}
            B = (16, 32, 128, 256)[case % 4]
            fixed = dict(B=B, DC=7, DR=11, MC=B-2, MF=12,
                         cell_bits=B.bit_length()-1, inner_bits=5)
            q = (B-1)*values['Jrep']+1
            before = parent.run(old, dict(values, s=Fraction(values['s'], q)), fixed)
            after = parent.run(rows, values, fixed)
            assert all(after[n] == before[n] for n, *_ in rows)
            assert after['wn2'] == values['w']*q and after['sn2'] == values['s']*q*q
            counts['complete_rational_parent_register_identities'] += 1
            counts['signed_parent_identities'] += signed
        bad = [old[:-1], old+[('unused','+',1,1)], parent.source(not normalized)]
        for name in ('wn2', 'sn2', 'norm_linear', 'norm_strong'):
            changed = list(old)
            i = next(i for i, row in enumerate(changed) if row[0] == name)
            changed[i] = (name, '+', 1, 1)
            bad.append(changed)
        for candidate in bad:
            try:
                rewrite(candidate, normalized)
            except AssertionError:
                counts['rejected_callers'] += 1
            else:
                raise AssertionError('noncanonical caller accepted')
        records.append(dict(normalized=normalized, ledger=ledger(normalized),
                            source=rows, every_gate_live=True,
                            source_sha256=hashlib.sha256(json.dumps(rows).encode()).hexdigest()))
    return dict(records=records, checks=dict(counts),
                identity='All surviving registers agree with asymmetric parent at s_old=s_new/q over Q; this is not a positive integer zero-set inverse.')


def complete_map_audit():
    symbols = sp.symbols('c k first main kappa mu f t V y', nonzero=True)
    rng, counts = random.Random(1928626), Counter()
    contexts = [dict(B=B,q=q,d=d,b=b,x=2,MC=B-2,MF=12,DC=3,DR=5,
                     X=X,Y=Y,Z=2,F=7,W=11)
                for B,q,d,b,X,Y in ((16,256,4,1,13,5),(32,1024,5,5,17,7))]
    for data in contexts:
        for normalized in (True, False):
            env = run_mapped(data, symbols, normalized)
            factors = scalar_factors(data, symbols, normalized)
            for name, want in zip(FACTOR_NAMES, factors):
                assert sp.cancel(env[name]-want) == 0
            assert sp.cancel(env['polynomial']-(sp.prod(factors)-1)) == 0
            assert sp.cancel(env['marked_rhs']-data['Z']-data['W']) == 0
            assert sp.cancel(env['W']-data['W']) == 0
            assert sp.cancel(env['index_rhs']-symbols[4]) == 0
            assert sp.cancel(env['exponent_rhs']-symbols[5]) == 0
            counts['symbolic_all19_coordinate_eight_factor_output_maps'] += 1
            for case in range(64):
                signed = case >= 32
                roots = [rng.randrange(1,10)*(-1 if signed and rng.randrange(2) else 1)
                         for _ in symbols]
                supplied = mapped_values(data, roots, normalized)
                assert supplied == mapped_values(data, list(map(Fraction, roots)), normalized)
                assert not any(isinstance(v, float) for v in supplied.values())
                actual, want = run_mapped(data, roots, normalized), scalar_factors(data, roots, normalized)
                assert [actual[n] for n in FACTOR_NAMES] == want
                assert actual['polynomial'] == sp.prod(want)-1
                counts['complete_rational_all_factor_output_maps'] += 1
                counts['signed_complete_maps'] += signed
    # These reductions establish simultaneous unit factors once the four
    # independent Pell identities and canonical T^2 relation are supplied.
    D,t,f,V,y,c,k,U,main,mu,kappa,L = sp.symbols('D t f V y c k U main mu kappa L')
    assert sp.expand((1+D*D*t*t-D*(f*f-1))-1).subs(f*f,1+D*t*t).expand() == 0
    assert sp.expand(D*(f*f-1)-D*D*t*t).subs(f*f,1+D*t*t).expand() == 0
    return dict(checks=dict(counts), contexts=contexts,
                coordinate_order=RETAINED, factor_order=FACTOR_NAMES,
                expected_factors_at_constructed_integer_witnesses=[1]*8,
                scope='All literal retained factors and the complete product are audited; random/symbolic placeholders are not full positive Pell zeros.')


def compiler_audit():
    examples = [([(0,)*9,(1,)*9],2), ([(0,)*9,(1,)*9,(2,)*9],3),
                ([(0,)*9,(0,)*8+(1,),(1,)*9],2),
                ([(0,)*9,(0,1)*4+(0,),(1,0)*4+(1,),(1,)*9],2)]
    records = []
    for windows, alphabet in examples:
        cc = compiler.compile_windows(windows, alphabet)
        K, b, T = len(cc.positions), cc.radix_bits, sum(v.bit_count() for v in cc.DCpoly.values())
        assert K == cc.m+1 and K >= 16 and cc.L > 7*max(cc.positions)
        assert T <= 2*K*b+5
        margin = cc.d-K-2*(T+2)
        assert margin >= (3*K-6)*b-K-14 >= 2*K-20 > 0
        assert compiler.baseline.is_five_power(cc.d) and cc.extra_dummy > 1
        assert cc.extra_dummy in cc.positions and cc.extra_dummy not in cc.coeff
        assert max(cc.DCpoly)+max(cc.positions) < cc.L and cc.H+max(cc.positions) < cc.L
        field = defaultdict(int)
        for e in cc.positions:
            for j,v in cc.DCpoly.items(): field[e+j] += v
            field[e+cc.H] += 1
            field[e] += 1
        assert max(field) < cc.L and max(field.values()) <= cc.R//4-1
        assert all(field[e]+2*int(e in cc.positions) <= cc.R//4+1
                   for e in set(field)|set(cc.positions))
        assert 0 not in cc.MFpoly and cc.MF_native_poly[0] == 4
        assert max(cc.MF_native_poly.values()) <= cc.R//2-2
        dc5 = sum(v*pow(2,b*e,5) for e,v in cc.DCpoly.items())%5
        dr5 = pow(2,b*cc.H,5)
        unit = pow(2,b*cc.extra_dummy,5)*3*(2*dc5-dr5)%5
        assert unit != 0
        records.append(dict(windows=len(windows),alphabet=alphabet,K=K,b=b,L=cc.L,
                            d=cc.d,T=T,MC_population=cc.d-K,density_margin=margin,
                            Gamma_mod5=unit,modified_masks_export='new_constants(cc)',
                            full_numeral_export_performed=False))
    # Verify the actual exporter contract without evaluating huge numerals.
    from types import SimpleNamespace
    fixed = dict(B=512,DC=17,DR=8,MC=446,MF=48,cell_bits=9,inner_bits=1)
    stub = SimpleNamespace(constants=lambda:fixed,radix_bits=1,extra_dummy=6)
    out = compiler.new_constants(stub)
    assert out == {**fixed,'MC':318,'MF':52} and fixed['MC'] == 446
    return dict(actual_sparse_layouts=records,exporter_stub_checked=True,
                rejecting_program_recipe='complete75_weakened86_rejecting_compiler.md sections1-3; only its independent empty-language machine and exact modified compiler recipe are used.')


def packing_control_audit():
    rng, counts = random.Random(86252), Counter()
    q,C,F,W,MC,MF,J,B,DC,DR,Dummy,Zbit = sp.symbols('q C F W MC MF J B DC DR Dummy Zbit')
    packed = lambda C,F: (q*q-(C-W)-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
    Gamma = Dummy*(q*q-1)*(1+q*(DC+B*DR+B))
    assert sp.expand(packed(C+Dummy*Zbit,F+(DC+B*DR+B)*Dummy*Zbit)-packed(C,F)+Gamma*Zbit) == 0
    for d,N in ((1,125),(5,625),(25,3125)):
        table = compiler.control.subgroup_table(d,N)
        for target in [0,1,d*N-1]+[rng.randrange(d*N) for _ in range(61)]:
            result = compiler.control.subset_for_target(d,N,target,table)
            assert result['modular_sum'] == target
            counts['constructive_five_adic_targets'] += 1
    for bits in (4,5,7,9):
        q0 = 1 << bits
        for _ in range(128):
            z = rng.randrange(1,q0)
            low = rng.randrange(1,q0)&~(z-1)
            if not low or z-1+low >= q0: continue
            ff, high = rng.randrange(1,q0//3), rng.randrange(1,q0//3)
            S, T = z-1+q0*ff, low+q0*high
            assert 0 < S < S+T < q0*q0
            R = (q0*q0-S)*(q0*q0-1)+T
            assert R.bit_count() == 2*bits+low.bit_count()+(ff+high).bit_count()-ff.bit_count()
            counts['shifted_population_identities'] += 1
    for q0 in (16,32,64,256,1024):
        assert Fraction(q0*q0,3)+Fraction(q0,6) < q0*q0-1
        assert 2*(q0*q0-1) > q0*q0 > 3*q0+1
        counts['explicit_main_index_lower_margin'] += 1
    return dict(checks=dict(counts),exact_dummy_identity=True,
                actual_target='(R_initial-d)*Gamma^(-1) mod(d*N), giving R=d mod(d*N); no factor2 or index offset')


def component_audit():
    pell = parent.normalized_parent.pell
    counts, records = Counter(), []
    for p in (3,7,11,15,19):
        r,X = (p-1)//2, 1 << p
        M = sum(int(sp.binomial(2*r,r+j))*X**j for j in range(r+1))
        Y = M//2
        assert M%2 == 0 and (Y&-Y).bit_length()-1 == p.bit_count()-2
        a,E,P = Y*(X+1),X*Y,2*X*Y*Y+1
        A,H,D = a+2,4*a+3,(a+2)**2-1
        main,c = pell(A,p); first,khalf = pell(P,r+1); k = 2*khalf
        eta,zeta,g = c-k*Y,k*(Y+1)-c,first-X*Y*Y*k
        assert min(eta,zeta,g) > 0
        assert g == pell(P,r+1)[1]-pell(P,r)[1]
        assert (k-p-1)%E == 0 and (k-p-1)//E > 0
        assert first*first-X*Y*Y*(X*Y*Y+1)*k*k == 1
        assert main*main-D*c*c == 1
        records.append(dict(p=p,X=X,Y_bits=Y.bit_length(),c_bits=c.bit_length(),
                            first_main_ratio_coordinates_positive=True,compiled_zero=False))
    for A in range(2,8):
        p = 3; D = A*A-1; c = pell(A,p)[1]
        f,t = pell(A,2*c*p); assert t%(c*c) == 0
        T = D*t; chi,y = pell(T,p); V,rem = divmod(chi,T); assert rem == 0
        o,rem = divmod(V+c,f); assert rem == 0
        j,rem = divmod(V+p,c); assert rem == 0
        assert min(t,o,j,y) > 0 and f*f-D*t*t == 1
        assert T*T*(V*V-y*y)+y*y == 1 and V == o*f-c == j*c-p
        assert 1+D*D*t*t-D*(f*f-1) == 1
        counts['normalized_and_ordinary_canonical_auxiliary_blocks'] += 1
    for A in (3,4,6,9,13):
        a,H,D = A-2,4*A-5,A*A-1
        for p in (7,11,15,19):
            main,c = pell(A,p); X = 1 << p; zp = main-a*c
            for u in range(3,p,2):
                mu,kappa = pell(A,u); W = 1 << u; zu = mu-a*kappa
                assert (kappa-u)%D == 0 and (zu-W)%H == 0 and (zp-X)%H == 0
                assert (zu-W)//H > 0 and (zp-X)//H > (zu-W)//H
                assert zp-zu > c > X and mu*mu-D*kappa*kappa == 1
                for j in range(2,p+1):
                    chi,psi = pell(A,j); oldchi,oldpsi = pell(A,j-1)
                    assert chi-a*psi-(oldchi-a*oldpsi)-psi == (2*A-3)*oldpsi > 0
                counts['positive_input_shared_gamma_components'] += 1
    return dict(checks=dict(counts),first_main_components=records,
                scope='Separate exact finite Pell components; not simultaneous full compiled zeros.')


def scalar_outer_fixture():
    B,N,x = 16,5,1
    q,J,t,u = B**N,(B**N-1)//(B-1),4*N,9
    W,Z,MC,MF,DC,DR = 1 << u,1,6,12,3,5
    C = Z+W; K = DC+B*DR
    seed = (q*q-Z)*(q*q-1)+(MC+q*(MF+B-1))*J
    e = seed%t; F = ((K+pow(2,e,q-1))*C)%(q-1)
    R = (q*q-Z-q*F)*(q*q-1)+(MC+q*(MF+B-1))*J
    alpha = q-F-Z-C-8
    assert alpha > 0 and R%t == e and R%4 == 3
    assert ((K+pow(2,R,q-1))*C-F)%(q-1) == 0
    assert (Z-1)&(MC*J+1) == 0 and F&(MF*J-1)
    assert 2*t+2 <= R.bit_count() < 3*t+2
    return dict(B=B,N=N,q=q,J=J,x=x,b=1,DC=DC,DR=DR,MC=MC,MF=MF,
                W=W,Z=Z,C=C,F=F,alpha=alpha,R=R,R_population=R.bit_count(),
                Y_valuation=R.bit_count()-2,
                scope='Scalar mask contract only: q^2 divides canonical Y but q^3 does not; neither actual compiled constants nor Pell integers are materialized here.')


def verify():
    return dict(status='PASS_COMPLETE75_ASYMMETRIC_SQUARED_SCALE_REFUTATION',
                theorem=theorem_contract(),literal_source=source_audit(),
                complete_coordinate_map=complete_map_audit(),compiler=compiler_audit(),
                packing_and_control=packing_control_audit(),pell_components=component_audit(),
                scalar_outer=scalar_outer_fixture())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--write',action='store_true')
    args = parser.parse_args()
    result = json.loads(json.dumps(verify()))
    path = Path(__file__).with_suffix('.json')
    if args.write: path.write_text(json.dumps(result,indent=2)+'\n')
    else: assert result == json.loads(path.read_text()), 'receipt mismatch'
    print(result['status'])
    print([r['ledger'] for r in result['literal_source']['records']])


if __name__ == '__main__':
    main()
