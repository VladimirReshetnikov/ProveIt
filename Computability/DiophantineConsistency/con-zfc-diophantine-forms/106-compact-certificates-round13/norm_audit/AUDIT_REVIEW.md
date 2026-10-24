# Independent audit of the fixed norm family

## Result and scope

PASS. The circuit reductions and the restricted optimum in `../norm/PROOF.md` and `../norm/section.tex` are supported by the supplied graphs, actual fixed coefficients, exact identities, and the leading-form argument. No mathematical blocker was found, and no frozen producer file was changed.

The optimum is **1,080,888 only within the family obtained by replacing the final coordinate m by m + R**, where R is any real polynomial in the other nine coordinates and the entire short-guard prefix is fixed. This is not a lower bound for arbitrary ten-variable Diophantine equations, other norm carriers or guards, source encodings, or changes to other coordinates. For the displayed integral shifts, the coordinate translation has an integral polynomial inverse; the real-coefficient extension is a degree statement, not an integer-zero-equivalence claim for every real R.

The audited comparison graphs are the local snapshots pinned in `../norm/SOURCE_PINS.json` to commit `7e533c33819ee1f703b69f2778a767cdc069940d`. This audit authenticated those supplied snapshots; it did not make a new claim about the live upstream repository.

## Counts and unchanged exact degrees

Backward liveness and direct operation recount, without using the producer's count metadata, give:

| Variant | Pinned parent | New graph | Saved | Exact degree |
| --- | ---: | ---: | ---: | ---: |
| Polar | 471 | 467 | 4 | 1,245,324 |
| Linear | 475 | 470 | 5 | 1,179,788 |
| Cubic | 478 | 473 | 5 | 1,114,252 |
| Six term | 512 | 507 | 5 | 1,080,888 |

Each graph has ten unrestricted integer coordinates and twelve fixed integer leaves. The graphs use binary addition, subtraction, and multiplication only. A live binary operation, including a square or scalar product, costs one; leaves and shared reuse cost zero. These are smaller descriptions of the same four polynomials, not lower-degree or fewer-variable results and not circuit-minimality claims.

The announced rewrites are exact identities over the integers. They remove the redundant tc and X adjustments, rewrite G using F = Fm1 + 1, share the S-power chain, share GH in the linear and cubic variants, and factor the six-term shift through E0 = C²xi. The supplied checker proves the common-register identities by induction over earlier common symbolic cut points, then proves the shear and complete norm identities. I inspected that logic and replayed it. Eight independently written local ring identities also pass in the additional audit script, including the identity between polarized and unpolarized norms.

## Exact defects and actual coefficient grounding

An independent expansion over Z[h,B1,C,xi,y], with weights (16384,7942,1,2,1), reproduces all three defect degrees. The unique highest-weight terms are:

| Shift | Degree of a1 minus R² | Highest-weight term |
| --- | ---: | --- |
| Linear | 426,050 | −17592186044416 h²⁶ C⁴⁰ xi¹² y² |
| Cubic | 393,282 | 13194139533312 h²⁴ C⁴⁰ xi¹² y² |
| Six term | 368,449 | 6803228196864 h²² B1 C³⁶ xi¹¹ y |

The actual signed little-endian coefficient payloads, their compressed and raw hashes, and their bit lengths were checked independently. The supplied checker additionally reconstructs all fixed recipes. The supplementary script obtains nonzero leading-coefficient witnesses at primes 1000039 and 1000081, distinct from the verifier's three primes. It uses the substitutions x_i = T and x_i = iT, respectively, in the given coordinate order. These certify degree attainment for the actual supplied coefficients, rather than merely for a generic set of coefficients. This also verifies attainment of all three specialized defect degrees.

The degree calculations are not based on the sheared graphs' naive DAG bound, which correctly remains 1,245,324. Let Z0 = Sigma m − Theta. After translating,

    B_R = Sigma²(R² − a1 − a0) + 2 Sigma R Z0 + Z0².

Here deg Sigma = 81922, deg Theta = 81925, deg R = 229409 for the three shifts, deg a0 = 294382, and deg a1 = 458818. Thus the three bounds on deg B_R are 589894, 557126, and 532293. The first two squared-inner degrees are 1,179,788 and 1,114,252 and strictly dominate the cross term. The six-term squared-inner bound is 1,064,586, strictly below the cross-term degree 1,080,888. Polar has degree 4 deg Sigma + 2 deg a1 = 1,245,324. Nonzero actual-coefficient certificates establish attainment in every case.

## Why the lower bound covers every real polynomial translation

The source degrees g = 2, cap = 233, K = 28548, L = 4220, r = 114189 are exact. In Delta, the first term has degree 57331 while the negative approximation square has degree 66002. Therefore

    (a0)_top = −U²,
    U = 3 cap_top K_top L_top r_top z ≠ 0.

The exact linear defect has degree 426050 < 458818, so

    (a1)_top = V²,
    V = (2AEGH)_top ≠ 0.

Consequently the fixed cross term has highest homogeneous part

    (−4 Sigma⁴ a0 a1)_top = (2 Sigma_top² U V)² ≠ 0

of degree d = 1,080,888. This sign is a structural identity over the reals, not an inference from modular residues or sampled signs.

For every real polynomial R independent of m, B_R is a nonzero polynomial: its m² coefficient is Sigma², which is nonzero. If 2 deg B_R is different from d, the term of larger degree survives. At equality, the degree-d part is the sum of two real polynomial squares, one of which is the displayed nonzero square. It cannot vanish identically. Hence every translated norm has degree at least d, and the six-term example attains d. The proof correctly replaces the inapplicable older odd-degree argument.

## Reproduction and boundaries

Only files listed in the producer's 58-file release whitelist were copied to a clean temporary directory. There, normal and optimized Python checker runs both passed and produced byte-identical results matching `../norm/CHECKS.json`. The clean build reproduced all four delivered graphs byte-for-byte. Each checker run includes 54 common-prefix identities per variant, the final identities, 360 signed modular native-source replays per variant, and rejection of all four final-sign mutations. No upstream program was executed.

Additional checks are in `independent_checks.py` and their receipts in `INDEPENDENT_CHECKS.json` and `INDEPENDENT_CHECKS_OPTIMIZED.json`. Run either `python independent_checks.py` or `python -O independent_checks.py` from this directory; only Python and SymPy are needed. The output also authenticates all 58 entries of the producer's release manifest.

The universal identities and leading-form argument support the new algebraic claims. The modular replays are supplementary transcription tests. This audit does not independently re-prove the inherited source/compiler/refutation calibration, generalized Pell/Lucas reliability, or interpolation theorems, and it is not a new proof-assistant certificate or a proof of Con(ZFC). The statements in the two reviewed documents preserve these boundaries. The earlier 23-integer degree-10 and 20-integer degree-18 points remain prior work.
