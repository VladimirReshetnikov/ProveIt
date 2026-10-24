# Pinned baseline audit

Repository: VladimirReshetnikov/ProveIt, commit `cfbf118b4ad9b2c651fe96b571d9415261766328`.

This is a reading audit of literal JSON/formula definitions and proofs, not a rerun of every archived verifier or a full independent proof of native semantic calibration.

## Critical baseline correction

Latest numbered package 75's comparisons are against an older arrival; its 34-integer sextic is not the current minimum. Sibling integrated packages 69 and 71 already achieve 38/4, 32/6, and 27/8. The ten incoming ZIPs improve much further. Comparing only the newest directory or root README would produce false novelty claims.

## Completed unrestricted-integer frontiers observed

| Variables | Degree | Source | Comments |
|---:|---:|---|---|
| 37 | 4 | Structural_Reductions_Round11; Joint_Guards; pell_congruences | Residue orientation plus calibrated determinant/cone |
| 30 | 6 | Structural_Reductions_Round11/positivity | Full literal packet; extra root shifts and reduced rows |
| 25 | 8 | Joint_Guards/joint | Shared positivity plus projections |
| 23 | 10 | Polynomial_Shears/integer/forms/centered23_degree10.json | 11 squared rows |
| 23 | 12 | Several | Dominated in variables/degree by 23/10, but costs may differ |
| 22 | 14 | centered-pell-norms; radical-guard-descent | Ordinary strong row reduces auxiliary row before elimination |
| 21 | 16 | Polynomial_Shears; saturation-and-projection | Transport pivot applied to shared guards |
| 20 | 20 | Polynomial_Shears; saturation-and-projection; pell_congruences | Some have rank register |
| 19 | 28 | pell_congruences/transport/degree28_19.json | CRT quotient elimination |
| 18 | 32 | pell_congruences/transport/degree32_18.json | CRT quotient elimination and transport pivot |
| 17 | 88 | pell_congruences/transport/degree88_17.json | Five SOS rows, CRT quotient elimination |
| 10 | 1,081,125 | Polynomial_Shears/norm10/integer10_sixterm.json | 521 live binary operations; different high-degree finalizer |
| 10 | 1,114,252 | Polynomial_Shears/norm10/integer10_cubic.json | 487 operations |
| 10 | 1,179,788 | Polynomial_Shears/norm10/integer10_linear.json | 484 operations |
| 10 | 1,245,324 | Structural_Reductions_Round11/lucas_h1868 | 480 operations |

Earlier 13-,14-,15-,16-integer high-degree forms remain in the repo. A new 16-integer moderate-degree equation would not be the first 16-integer representation or improve the ten-integer fewest-variable bound.

## Positive-domain frontiers observed

| Variables | Degree | Operations | Source |
|---:|---:|---:|---|
| 9 | 1,628,768 | 434 | saturation-and-projection/nine/saturated_positive.json |
| 9 | 1,103,950 | 1,074 | saturation-and-projection/nine/saturated_radical_positive.json |
| 9 | 1,158,228 | 726 | pell_congruences/nine_full_radical |
| 9 | 1,379,730 | 478 | integrated71 |
| 10 | 1,152 | 131 | radical-residue/ten_positive/generated/p10_positive.json |
| 11 | 211 | 112 | Polynomial_Shears/positive11 |
| 11 | 277 | 111 | several; cost tradeoff |
| 12 | 78 | 101 | Structural_Reductions_Round11/positive |
| 13 | 28 | 98 | integrated72 |
| 13 | 30 | 92 | integrated73 |
| 14 | 24 | 101 | integrated72 |

`docs/incoming/report.zip` contains only `report.tex`, claiming 12 positive / degree70 /100 operations via an ordinary strong norm after an early Pell-index lower bound. Its complete displayed P12 and proof appear in the TEX, but referenced data, sections, coefficient seed include files, and circuit are absent from that ZIP. Treat as an existing manuscript-level result rather than a verified delivered endpoint, and do not claim degree78 is the best mathematical claim without mentioning it.

## New combinations worth testing

The radical-residue packet's scaled merger is sound for arbitrary integers once the common-sign guard supplies Q=I²>1 and the first radicand A>0. It replaces independent tau and y by xi with s=[I(2u+k)+xi]/2 and:

    delta=Q-1; Bnum=Q V²-1;
    L=xi²+2I(2u+k)xi+Q(k²-4);
    N=(delta L-4Bnum)²-64 delta Q A Bnum.

The distinct-radicand argument QA != Bnum/(Q-1) follows modulo Q. Rational tau is integral because tau²=A is integral; rational y is integral by adjacent-coefficient Pell descent. This packet applies the merger to an 18-variable pre-CRT parent, yielding17/112 or17/110.

The separate pell_congruences packet already replaces the old two auxiliary quotient coordinates (o,j) by one T through:

    V=f c T-f²R-c,

using the preliminary strong-rank conclusion c|(f²-1), established before either auxiliary quotient is used. Its 17/88 packet still has independent tau and y_gap. Applying the scaled merger to this CRT packet appears to yield a new 16-integer endpoint. The half-centered tau and y_gap can first be restored to original roots; forced parity makes that existence equivalence integral. No current incoming packet inspected combines these two savings.

Potential further route: normalized strong norm permits replacing all f² occurrences before a three-root merger, but extra canonical congruences, signed root separation, parity, and cofinality must be proved. Simply allowing rational f in the ordinary norm is invalid: A=50, Delta=2499, I=51, f=10/7 satisfies I²=Delta(f²-1) with nonintegral f.

## Already covered mechanisms

- Canonical determinant and weighted cone guards, residue orientation, delayed signed-power recovery.
- Shared two-positive guard via dT-(s²-d-T+1)²=Pos(three variables).
- Monic transport pivot alpha->C and F=(K0+W)C-z(q-1).
- Main/strong/auxiliary Pell root centering, half-centering with forced parity.
- Reduction of residuals modulo retained norm equations before projecting variables.
- Adaptive carrier moduli, rational Pell descent, saturation of redundant squared factors.
- Full-radical polynomial majorants and triangular polynomial shears.
- CRT quotient compression of auxiliary congruences.
- Positive ten-variable four-root merger with small rational residues.
- Uncompiled direct certificate proposals: affine/Horn proof flows, inert-prime CRT, Fermat labels, descending coefficient budgets, bounded universal blocks, fixed universal-input sources. None is a completed competing ordinary polynomial endpoint.

## Assurances and caveats shared by packets

New reductions are ordinary proofs intended to formalize in ZFC, composed with inherited native compiler, Pell rank, and K215 refutation calibration. Their code verifies finite identities, coefficient recipes, degrees, counts and hashes. It does not supply a new complete Lean/Rocq proof of the endpoint or an encoded object-ZFC biconditional. Every fixed coefficient tuple must be kept intact, especially MF already shifted. Source34 and source31 share beta=2^1064921-1 while their other ports differ; compact44 instead has beta=2^590069-1. The calibrated determinant adds powers2^1113 and2^666104 to the source34 tuple.

The inherited ordinary calibration theorem is explicitly retained by Polynomial_Shears/calibration. This should be cited as a named mathematical dependency; separate formalization status should not be mistaken for a disproof of the ordinary theorem, or finite tests for its proof.
