#!/usr/bin/env python3
"""Modified native masks for the proposed half-binomial complete75.

Compiler interface only: no kernel theorem or complete75 claim is made here.
Default compares the saved receipt; --write regenerates it.
"""
from itertools import product
from pathlib import Path
import argparse
import json
import random
import sys
import sympy as sp

VERIFY = Path(__file__).resolve().parents[2] / 'verification'
sys.path.insert(0, str(VERIFY))
import explore_fixed_raw_universal_76 as baseline
import explore_five_adic_dummy_control as control


def compile_windows(windows, alphabet_size):
    """Return the old sparse layout with the stronger radix and new metadata.

    MC and MF cached properties retain their baseline meanings. The NEW masks
    are specified by new_mask_formulas() and MF_native_poly; callers must not
    silently use the old properties as source constants.
    """
    cc = baseline.compile_windows(windows, alphabet_size)
    K = len(cc.positions)
    mass = (K + 2) * (2 * sum(cc.coeff.values()) + 6)
    target = max(4 * mass + 8, 2 * cc.mu + 4, 16)
    cc.radix_bits = baseline.next_five_power((target - 1).bit_length())
    cc.R = 1 << cc.radix_bits
    cc.d = cc.radix_bits * cc.L
    cc.extra_dummy = cc.dummy[0]
    cc.MF_native_poly = dict(cc.MFpoly)
    assert 0 not in cc.MF_native_poly
    cc.MF_native_poly[0] = 4
    cc.unshifted_mass_bound = mass
    assert cc.extra_dummy + 1 < max(cc.positions)
    assert mass <= cc.R // 4 - 2
    return cc


def new_constants(cc):
    """Materialize the NEW fixed numerals only on an explicit caller request.

    MF is the native MF_old+4 expected by complete75_half_binomial.py;
    that source creates its fixed alias MF_source=MF+B-1. The returned
    dictionary is fresh, and the sparse compiler's baseline caches remain
    unchanged. Actual numerals can be enormous; ordinary verification does
    not call this exporter on the large compiler layouts.
    """
    values = dict(cc.constants())
    values['MC'] -= 2 << (cc.radix_bits*cc.extra_dummy)
    values['MF'] += 4
    return values


def new_mask_formulas():
    q, Z, F, J, B, MC, MF = sp.symbols('q Z F J B MC MF')
    S = Z - 1 + q * F
    low, high = MC * J + 1, MF * J - 1
    T = low + q * high
    source = (q*q - Z - q*F) * (q*q - 1) + (MC + q*(MF+B-1))*J
    shifted = (q*q - S) * (q*q - 1) + T
    difference = sp.expand(source - shifted)
    assert sp.expand(difference - q*((B-1)*J-(q-1))) == 0
    # Verify the lazy export independently with a small materialized stub.
    from types import SimpleNamespace
    old = dict(B=512, DC=17, DR=8, MC=446, MF=48,
               cell_bits=9, inner_bits=1)
    stub = SimpleNamespace(constants=lambda:old, radix_bits=1, extra_dummy=6)
    exported = new_constants(stub)
    assert exported['MC'] == 318 and exported['MF'] == 52
    assert old['MC'] == 446 and old['MF'] == 48
    assert all(exported[key] == old[key] for key in old if key not in ('MC','MF'))
    return dict(native_MC='MC_old - 2*R^e_dummy',
                native_MF='MF_old + 4', source_MF='MF_native + B - 1',
                effective_export='new_constants(cc); MF denotes the new native mask, not the source alias',
                shifted_word=sp.sstr(S), low_mask=sp.sstr(low),
                high_mask=sp.sstr(high), packed_mask=sp.sstr(T),
                source_rewrite_residual=sp.sstr(difference))


def verify_layout(cc):
    old = baseline.verify_compiler(cc)
    E = max(cc.positions)
    support = set(cc.positions)
    expanded = support | {cc.extra_dummy + 1}
    v1, v2 = cc.anchors[2:]
    clean = aligned = spill = 0
    for shift in range(cc.L):
        assert not all((target-shift) % cc.L in expanded
                       for target in (cc.T1, cc.T2))
        clean += 1
        low_targets = all((target-shift) % cc.L in support
                          for target in (v1, v2))
        assert low_targets == (shift == 0)
        aligned += 1
        odd_spill = (cc.extra_dummy + shift + 1) % cc.L
        assert not (v1 == odd_spill and v2 == odd_spill)
        spill += 1
    # Extra dummy weight2 has zero coefficient at EVERY old tested field.
    dummy_basis = 0
    for target in cc.MFpoly:
        for site in range(3):
            actual = (cc.DCpoly.get(target-cc.extra_dummy, 0) if site == 0
                      else int(target-cc.extra_dummy == cc.H) if site == 1
                      else int(target == cc.extra_dummy))
            assert actual == 0, (target, site, actual)
            dummy_basis += 1
    # Every residue has either no odd contribution, a low native lane,
    # or the single spilled upper-dummy lane. No integer field is allocated.
    residue_cases = 0
    for ell in range(cc.radix_bits):
        if ell < cc.radix_bits - 1:
            rotation_bound = 3 << ell
            assert rotation_bound <= 3 * cc.R // 4
            for low, upper in product((0, 1), repeat=2):
                value = (low + 2*upper) << ell
                assert (value & 1) == (low if ell == 0 else 0)
                residue_cases += 1
        else:
            rotation_bound = cc.R // 2 + 1
            for low, spill_bit in product((0, 1), repeat=2):
                value = (low << ell) + spill_bit
                assert (value & 1) == spill_bit
                residue_cases += 1
        assert cc.unshifted_mass_bound + rotation_bound <= cc.R - 2
    assert max(cc.DCpoly) + E < cc.L
    assert min(cc.DCpoly) > 0 and cc.H > 0
    assert min(cc.MFpoly) > 0
    assert cc.radix_bits >= 5
    # New mask population and valuations, represented sparsely.
    native_MC_population = cc.d - cc.m - 1
    native_MF_population = cc.m + 1
    assert native_MC_population > 0
    assert native_MC_population + native_MF_population == cc.d
    assert cc.extra_dummy > 1 and cc.extra_dummy not in cc.coeff
    assert baseline.is_five_power(cc.d)
    # Fresh weighted evaluator: the baseline helper assumes Boolean inputs
    # and must not be reused for the new digit2/3 at the dummy position.
    def field(rows):
        out = {}
        for site, row in enumerate(rows):
            for exponent, value in zip(cc.positions, row):
                if not value:
                    continue
                contributions = (cc.DCpoly.items() if site == 0
                                 else ((cc.H, 1),) if site == 1
                                 else ((0, 1),))
                for degree, coefficient in contributions:
                    target = exponent+degree
                    out[target] = out.get(target, 0)+value*coefficient
        assert max(out, default=0) < cc.L
        assert max(out.values(), default=0) <= cc.R-2
        return out
    position = cc.positions.index(cc.extra_dummy)
    native_checks = 0
    rng = random.Random(7500+len(cc.windows)+cc.a)
    for _ in range(100):
        rows = [[rng.randrange(2) for _ in cc.positions] for _ in range(3)]
        for row in rows:
            row[position] = rng.randrange(4)
        actual = field(rows)
        assert cc.mask_ok(actual) == cc.truth(rows)
        assert actual.get(0, 0) == rows[2][cc.positions.index(0)]
        native_checks += 1
    for states in product((None, 0, 1), repeat=3):
        for fill in range(4):
            rows = [list(cc.bits(state)) for state in states]
            for row in rows:
                row[position] = fill
            actual = field(rows)
            assert cc.mask_ok(actual) == cc.truth(rows)
            assert actual.get(0, 0) == int(states[2] == 0)
            assert actual.get(0, 0) & 6 == 0
            if states[2] != 0:
                assert actual.get(0, 0) & 3 == 0
            native_checks += 1
    old.update(new_mask_population=cc.d,
               new_MC_population=native_MC_population,
               new_MF_population=native_MF_population,
               extra_dummy=cc.extra_dummy,
               expanded_support_size=len(expanded),
               extra_dummy_zero_test_coefficients=dummy_basis,
               expanded_clean_band_checks=clean,
               aligned_anchor_support_checks=aligned,
               single_odd_spill_exclusions=spill,
               rotation_bit_cases=residue_cases,
               weighted_four_valued_dummy_triples=native_checks,
               mass_margin='unshifted <= R/4 - 2; rotated <= max(3R/4,R/2+1)',
               new_MF_two_adic_valuation=2,
               original_cached_masks_are_not_new_source_constants=True)
    return old


def toy_masks(d):
    """Small binary-mask geometry, not an actual compiler layout."""
    B = 1 << d
    # Start0, End3 and ignored dummy6. Original permitted bits0,6.
    MC0 = B-1-(1 << 0)-(1 << 6)
    MF0 = (1 << 4) + (1 << 5)
    assert MC0.bit_count() + MF0.bit_count() == d
    return B, MC0-2*(1 << 6), MF0+4


def verify_small_masks():
    cases = origins = canonical = boundary = 0
    for d in (9, 10, 11):
        B, MC, MF = toy_masks(d)
        assert MC % 2 == 0 and MF % 8 == 4
        for N in (1, 2, 3, 4):
            q = B**N
            J = (q-1)//(B-1)
            low, high = MC*J+1, MF*J-1
            T = low+q*high
            assert 0 < T < q*q-1
            assert low < q and 0 < high < q
            assert low.bit_count() == N*MC.bit_count()+1
            assert high.bit_count() == N*MF.bit_count()+1
            assert T.bit_count() == d*N+2
            # First-cell old MF survives; new low mask inserts the origin.
            old_high = (MF-4)*J
            assert high & old_high == old_high
            assert high & 7 == 3
            for cell in range(1, N):
                assert (high >> (d*cell)) & 7 == 4
            allowed_low = [j for j in range(d*N) if not (low >> j) & 1]
            allowed_high = [j for j in range(d*N) if not (high >> j) & 1]
            rng = random.Random(75000+d*10+N)
            for _ in range(100):
                zm = sum(rng.randrange(2) << j for j in allowed_low)
                f = sum(rng.randrange(2) << j for j in allowed_high)
                if not f:
                    f = 1 << allowed_high[-1]
                Z = zm+1
                assert Z & 1 and (Z-1) & low == 0
                assert Z & (MC*J) == 0
                assert Z < q and f < q
                S = zm+q*f
                idx = (q*q-S)*(q*q-1)+T
                source = (q*q-Z-q*f)*(q*q-1)+(MC+q*(MF+B-1))*J
                assert idx == source
                assert idx.bit_count() == 3*d*N+2
                assert idx % 2 == 1
                canonical += 1
                origins += 1
            assert T.bit_count() < 3*d*N+2  # Z=1,F=q boundary
            boundary += 1
            cases += 1
    # General inverse-population identity, independently of compiler masks.
    inverse = equality = 0
    for n in range(2, 9):
        lam = 1 << n
        for S in range(1, lam+1):
            for T in range(1, lam-1):
                idx = (lam-S)*(lam-1)+T
                threshold = n+T.bit_count()
                assert idx.bit_count() <= threshold
                exact = idx.bit_count() == threshold
                assert exact == (S < lam and (S & T) == 0)
                inverse += 1
                equality += exact
    return dict(mask_pairs=cases, masked_population_cases=canonical,
                origin_recoveries=origins, excluded_packing_boundaries=boundary,
                exhaustive_inverse_population_cases=inverse,
                inverse_equalities=equality,
                scope='Small arithmetic masks plus full inverse identity through 8-bit lambda; not actual compiler words')


def verify_control():
    q, C, F, W, MC, MF, J, B, rho, zbit = sp.symbols('q C F W MC MF J B rho zbit')
    DC, DR, P = sp.symbols('DC DR P')
    packed = lambda c, f: (q*q-(c-W)-q*f)*(q*q-1)+(MC+q*(MF+B-1))*J
    gamma = rho*(q*q-1)*(1+q*(DC+B*DR+P))
    difference = sp.expand(packed(C+rho*zbit, F+(DC+B*DR+P)*rho*zbit)-packed(C,F))
    assert sp.expand(difference+gamma*zbit) == 0
    targets = 0
    for d, N in ((1, 125), (5, 625)):
        table = control.subgroup_table(d, N)
        modulus = d*N
        for target in range(modulus):
            result = control.subset_for_target(d, N, target, table)
            assert result['modular_sum'] == target
            targets += 1
    # Sample target equation at unit Gamma, now no factor2 in its inverse.
    actual_indices = 0
    for modulus in (125, 3125):
        for gamma0 in range(1, 31):
            if gamma0 % 5 == 0:
                continue
            for R0, target in product(range(9), repeat=2):
                y = (R0-target)*pow(gamma0, -1, modulus) % modulus
                assert (R0-gamma0*y-target) % modulus == 0
                actual_indices += 1
    return dict(exact_dummy_change=sp.sstr(difference), gamma=sp.sstr(gamma),
                target='(Ridx_initial - d*h) * Gamma^(-1) modulo d*N',
                subset_targets=targets, direct_index_residue_checks=actual_indices,
                canonical_extra_dummy_upper_bit_zero=True,
                uses_existing_Boolean_control_dummy=True)


def verify():
    alphabets = [([(0,)*9, (1,)*9], 2),
                 ([baseline.previous.previous.previous.cyclic_window([1,0,0],i,1) for i in range(3)],2),
                 (list(product(range(2), repeat=9))[:100],2),
                 ([(0,)*9,(1,)*9,(2,)*9],3),
                 (list(product(range(2), repeat=9))[:3],2)]
    layouts = [verify_layout(compile_windows(windows, a)) for windows,a in alphabets]
    assert {row['high_correction'] for row in layouts} == {0, 1}
    return dict(status='PASS_PROPOSED75_HALF_BINOMIAL_COMPILER_INTERFACE',
                formulas=new_mask_formulas(), layouts=layouts,
                masks=verify_small_masks(), control=verify_control(),
                scope='Compiler and mask interface only; complete75 depends on separate kernel, bridge and source audits',
                proof='complete75_half_binomial_compiler.md')


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--write', action='store_true')
    args = parser.parse_args()
    result = verify()
    path = Path(__file__).with_suffix('.json')
    normalized = json.loads(json.dumps(result))
    if args.write:
        path.write_text(json.dumps(normalized, indent=2)+'\n', encoding='utf-8')
    else:
        assert normalized == json.loads(path.read_text(encoding='utf-8'))
    print(json.dumps({'status':result['status'], 'layouts':len(result['layouts']),
                      'masks':result['masks'], 'control_targets':result['control']['subset_targets']}))
