#!/usr/bin/env python3
"""Finite native-geometry certificate for the power-of-two determinant guard.

The universal soundness/completeness arguments are in proofs/DETERMINANT_GUARD.md.
This verifies their fixed finite hypotheses; it does not prove Con(ZFC).
"""

import itertools
import json
from fractions import Fraction
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def main():
    here = Path(__file__).resolve().parent
    tiles = json.loads((here / "coefficients/wang943_tiles.json").read_text())
    require(len(tiles) == 943, "wrong native tile count")
    require(tiles[0] == [2, 435, 3, 1], "wrong native Start tile")
    rho = 1 << 121
    L = 8801
    coeff = {}
    for i, tile in enumerate(tiles):
        coeff[i] = 1 + sum(
            (((label + 512) >> j) & 1) << (10 + 2 * (10 * t + j))
            for t, label in enumerate(tile)
            for j in range(10)
        ) + sum(1 << (10 + 2 * j) for j in range(40, 44))
    for t, off in enumerate([1020, 1000, 980, 960]):
        for j in range(10):
            coeff[off + 2 * j] = 1 << (10 + 2 * (10 * t + j))
    for e, j in [(1095, 40), (1096, 41), (2195, 42), (3296, 43)]:
        coeff[e] = 1 << (10 + 2 * j)
    coeff[1063] = coeff[1064] = 0
    require(len(coeff) == 989, "support size mismatch")
    c0 = coeff[0]
    require(c0 == 105534389824824194647382298625, "c0 mismatch")
    require(1 << 96 <= c0 < c0+1 <= 3*(1 << 95), "c0 balancing interval")
    require(3*(1 << 95) < 1 << 97 < rho, "c0 radix upper bounds")
    require(rho >= 8 and 121*L >= 4, "balancing size hypotheses")
    c_support = sorted(coeff)
    require(c_support[-2:] == [2195, 3296], "C top support mismatch")
    dc = {40: 1, 41: 1, 1100: 1, 2200: 1}
    for e, a in coeff.items():
        for target in [4393, 5495]:
            dc[target-e] = dc.get(target-e, 0) + a
    dc = {e: a for e, a in dc.items() if a}
    require(max(dc) == 5495 and dc[5495] == c0, "DC top mismatch")
    require(max(dc) + max(c_support) == 8791 < L, "F top mismatch")
    top_pairs = [(e, f) for e in dc for f in c_support if e+f == 8791]
    require(top_pairs == [(5495, 3296)], "leading convolution not unique")
    M = 991 * (2 * sum(coeff.values()) + 6)
    require(4*M+8 < rho, "native carry bound failed")
    require(sum(dc.values()) == 4+2*sum(coeff.values()), "DC coefficient mass")
    require(3*sum(dc.values())+6 < M, "direct canonical carry majorant")
    require(1+max(c_support) < 8791, "DR contribution reaches top")
    require(max(c_support) < 8791, "temporal contribution reaches top")
    scale_f_exp, scale_c_exp = 1113, 666104
    require(1 << scale_f_exp >= 2, "F scale too small for sign implication")
    require(1 << scale_c_exp >= 2, "C scale too small for sign implication")
    require(121*8791+scale_f_exp == 121*L-97, "F scale exponent identity")
    require(121*3296+scale_c_exp == 121*L-1, "C scale exponent identity")
    # Exact rational bounds for canonical U/q, V/q, and the determinant.
    require(Fraction(1 << 96, 1 << 97) == Fraction(1, 2), "U lower factor")
    require(Fraction(3, 4)*Fraction(16, 15) == Fraction(4, 5), "U upper factor")
    require(Fraction(1, 2)*Fraction(9, 8)*Fraction(16, 15) == Fraction(3, 5), "V upper factor")
    require(1-Fraction(9+3+1, 25) == Fraction(12, 25) > 0, "strict determinant margin")
    # Exact bitlength proof for the new squared contribution and total [J^4].
    # beta=2^d-1, D=2^e, MF=beta+MF_native, 0<MF_native<beta.
    # Contribution > (15/16)^8 2^(4(d+e)) > 2^(4(d+e)-1).
    # Contribution <= 2^(4(d+e))-2^(4d+3e), while the other two
    # nonnegative terms sum to < 2^(4d+1). Since 3e>1, no extra bit arises.
    d, e = 121*L, scale_c_exp
    require(d >= 4 and e >= 4, "coefficient bitlength lower bounds")
    require(2*15**8 > 16**8, "coefficient bitlength lower factor")
    require(3*e > 1, "coefficient bitlength upper separation")
    j4_bits = 4*(d+e)
    require(j4_bits == 6924100, "J^4 coefficient bitlength")
    # Reconstruct the source34 high mask from its literal bounded recipe,
    # making the mask bound and the actual coefficient calculation explicit.
    mu = 1022 + sum(1 << (10+2*j) for j in range(44))
    mask_digits = {0: 4, 4393: mu, 5495: mu, 2195: 1, 3296: 1}
    for j in range(10):
        mask_digits[1000+2*j] = 1
        mask_digits[1021+2*j] = 1
    for k in range(8792, 8799):
        mask_digits[k] = (1 << 119)-1
    mask_digits[8799] = (1 << 27)-1
    require(all(0 <= value < rho for value in mask_digits.values()), "mask radix bound")
    require(max(mask_digits) < L-1, "mask top bound")
    native_mf = sum(value << (121*k) for k, value in mask_digits.items())
    beta = (1 << d)-1
    require(0 < native_mf < beta, "actual source34 native MF bound")
    shifted_mf = beta+native_mf
    beta2 = beta*beta
    beta4 = beta2*beta2
    contribution = beta4*((1 << e)-1)**4
    total_j4 = contribution+beta4+beta2*(beta-shifted_mf)**2
    require(contribution.bit_length() == j4_bits, "actual squared contribution bitlength")
    require(total_j4.bit_length() == j4_bits, "actual total J^4 bitlength")
    # Independent finite diagnostic only; the note proves the real lemma.
    cases = 0
    for u, v, w in itertools.product(range(-20, 21), repeat=3):
        guard = u*v-w*w
        if guard > 0:
            q_scaled = u+v+w
            require(u*v > 0 and q_scaled*u > 0, "sign diagnostic")
            require(2*abs(q_scaled) > abs(u)+abs(v), "strict sum diagnostic")
        cases += 1
    result = {
        "status": "PASS",
        "source_commit": "9cca523d9f27ad39d52993f4065cbd7e58f8bdd4",
        "source_tuple": "mixed-parity-unrounded-1064921",
        "c0": str(c0),
        "c0_bit_length": c0.bit_length(),
        "rho_log2": 121,
        "base_log2": 1064921,
        "C_top": 3296,
        "C_next": 2195,
        "DC_top": 5495,
        "F_top": 8791,
        "F_top_pairs": top_pairs,
        "carry_majorant_bit_length": M.bit_length(),
        "scale_F_log2": scale_f_exp,
        "scale_C_log2": scale_c_exp,
        "fixed_guard_scales": {"scale_F": "2^1113", "scale_C": "2^666104"},
        "guard": "U*V-(q-U-V)^2",
        "c0_balancing_interval": "2^96 <= c0 < c0+1 <= 3*2^95",
        "canonical_U_interval": "q/2 <= U < 4*q/5",
        "canonical_V_interval": "q/2 <= V < 3*q/5",
        "canonical_guard_lower_bound": "G > (12/25)*(q/2)^2",
        "squared_guard_J4_contribution": "beta^4*(2^666104-1)^4",
        "total_quartic_J4_coefficient": "beta^4*(2^666104-1)^4 + beta^4 + beta^2*(beta-MF)^2",
        "J4_coefficient_bit_length": j4_bits,
        "actual_J4_bitlength_check": "PASS for reconstructed source34 high mask",
        "coefficient_height_scope": "lower bound from one coefficient; no maximum-height claim",
        "native_hypotheses": "all finite leading-support and carry checks pass",
        "finite_sign_diagnostics": cases,
        "proof_scope": "finite hypotheses only; see the universal mathematical proof",
    }
    (here / "certificates/DETERMINANT_GUARD_CHECK.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
