# Bounded transseries placement review: 6132faa30

The placement metadata passes. I found no concrete correction in the selected analytic and computational interfaces. This is not certification of either complete manuscript, the supplied software, its numerical outputs, or imported analytic results. Neither package supplies a new ordinary-integer universal polynomial or a paid arithmetic improvement.

The immutable scope is commit `6132faa30bf6e7674158ad43c9178ab730f560e0`, parent `40ad429160b8e756f689f702a28431497f9e9246`. It changes 48 paths: 43 added files, three modified text files and two retired ZIP inputs. The 12,714 inserted lines are mostly full manuscripts and evidence packages; I deliberately did not read all of them.

## Exact metadata and read scope

A fresh metadata program independently authenticated every changed before/after blob and all declared read spans. It confirmed that the two archived inputs at the parent are byte-identical to their arrival at `516049bf9cf4be8d3240cddb04c9adf453cb65e0`:

| Archive | SHA-256 | Members | Exact placed files |
|---|---|---:|---:|
| `complex_transseries_q_cusps (2).zip` | `c82002e6672c463a71d415a025a8b1245f49af3ea211c12bc5273c5beaf4f87d` | 25 | 24 |
| `complex_transseries_reversion (2).zip` | `f6c310cea0dc9be17f758b5af1f7b1c8de6692f0879ab0fd6ff76733e58ba194` | 20 | 19 |

All **45 members** were hashed. All **43 placed files** agree byte-for-byte with their members, including the CRLF CSV. Both archived `MANIFEST.sha256` files validate all **43 other members**; those two ledgers were intentionally omitted from the placement and remain recoverable from Git. There are no unaccounted files under the two new destinations. PDF and PNG checks are byte checks only, without rendering or page-count verification.

I read the complete diffs of `.gitattributes`, `Analysis/Transseries/README.md` and the collection `docs/series-and-transseries/README.md`: **195 diff lines**. The two new packages support the guide's increment from 59 to 61 arrivals and from 37 to 39 checksum ledgers; the other 59 packages and 37 old ledgers were not recertified. The delivered main-source line counts agree with the guide: 2,364 for the action-cone article and 2,740 across the modular-cusp article's ten source files. The reported PDF page counts were not checked.

The following independently read immutable spans total **2,767 lines in 14 spans**. All paths below are under `Analysis/Transseries/docs/series-and-transseries/` unless stated otherwise.

| File | Read lines |
|---|---|
| `Analysis/Transseries/AGENTS.md` | 1–17, full |
| `docs/incoming/README.md` | 1–100 and 426–439 |
| `Action_Cones_Quartic_Boundaries_Complex_Reversion/README.txt` | 1–88, full |
| Same package, `verification/README.txt` | 1–116, full |
| Same package, `complex_transseries_reversion.tex` | 66–880, 1780–2041, 2149–2245 |
| `Modular_Cusp_Reversion_Stokes_Corrections_q_Gamma/README.txt` | 1–95, full |
| Same package, `SOURCES.txt` | 1–47, full |
| Same package, `sections/01_scope.tex` | 1–236, full |
| Same package, `sections/02_reversion.tex` | 1–260, full |
| Same package, `sections/05_flat.tex` | 1–234, full |
| Same package, `sections/08_verification_future.tex` | 1–386, full |

A separate literal TeX metadata scan found 116 distinct labels and 83 reference occurrences in the action-cone package, and 105 labels and 91 references in the modular-cusp package. All extracted references resolve internally, with no duplicate labels. The extracted 34/32 citation occurrences resolve to the respective 18/18 bibliography keys. These syntactic inventories do not enlarge the human mathematical read scope, verify external links, or certify theorem equivalences and priority comparisons in the guide.

## Selected mathematical and computational interfaces

The finite-action cone argument separates properness with multiplicities from finite fibers. I checked the stated proof chain: a separating functional gives a degree bound; rounding a nonnegative real zero relation gives infinitely many bounded images; Dickson's lemma yields the separate finite-fiber criterion. The examples with actions `1,-1` and `1,-sqrt(2)` correctly distinguish the two failures. The completion uses finite coefficient fibers and cofinal weight comparisons; the formal inverse construction is a filtered iteration, not an analytic or machine-code evaluation by itself.

The weighted reversion argument supplies a chosen local inverse under disk norms and derivative bounds. The countable formula uses normal convergence, and the action-tail estimate requires a positive weight exponent to decay. The finite atlas construction groups exact resonances; it explicitly declines bit-complexity claims for arbitrary computable real parameters without equality and ordering information (action source lines 820–824). Effective algorithms and formalization remain a research question at lines 2001–2016. Dense ordering walls are distinguished from Borel singularities and Stokes jumps.

For the modular-cusp exact-core theorem, I checked the stated Rouché uniqueness, finite coefficient extraction, and Cauchy tail argument. The chosen core branch and nonvanishing divided difference are essential hypotheses. The finite-endpoint theorem retains the scale `Q0/t0^2`, with coefficient poles and a correspondingly scaled remainder; the argument does not silently substitute an unscaled error. The residual certificate uses a derivative disk and contraction, which avoids the invalid complex analogue of a global real mean-value estimate.

The flat inverse separates the finite nome roots from logarithm lifts. Its completeness concerns the small-nome region, not every tangential approach to the cusp. The tail proof includes the nonvanishing `H` disk, the coherent logarithm, bounds on both reciprocal denominators, and an explicit restriction when one wants a fixed angular subsector. I found no missing hypothesis in those selected arguments.

The coefficient-generation procedure is finite for a prescribed truncation once the first surviving order is known and the coefficient field operations are available. It is not a general cancellation decision procedure: effective cancellation certificates for arbitrary phase products are expressly left open in `08_verification_future.tex` lines 251–264. The eta/raw-product nonconstancy argument supplies termination of a search in its stated nonzero balanced setting, but does not supply a uniform efficient cancellation bound for every phase product.

Two fresh small checks corroborate specific interfaces. The displayed rational eta-disk majorant at `r=1/20` equals

`1453085886761779950057353 / 19107936887752212855847947`,

which is less than `760463/10^7 < 1/2`, as claimed. Independently enumerated reduced ratios for cutoffs 1 through 20 give the stated wall-count formula; in particular the counts for 3, 6 and 12 are 7, 23 and 91. These checks do not replace the proofs, validate the supplied programs, or audit floating-point calculations.

## Review observation 1: finite truncation versus an effective listing

The action article's lines 651–656 state that proper positive weights make every action cutoff finite and call the resulting tail estimate a “finite computation certificate.” The proved finiteness is sound. It must not be strengthened into a uniform algorithm that lists the full cutoff from arbitrary computable countable weights alone.

For clarity, fix a computable pairing `j=<e,t>` and a fixed effective machine enumeration. Define the positive integer weight `p_j=e+1` if machine `e` halts at exactly step `t`, and `p_j=j+1` otherwise. This sequence is computable by a finite simulation. For every integer `B>=1`, the sublevel `{j:p_j<=B}` has at most `2B` elements: at most `B` ordinary indices and at most one exceptional halting index for each `e<B`. Nevertheless a uniform terminating procedure listing each whole sublevel would decide halting: request the list for `B=e+1`, decode its finitely many indices, and test whether any is the exact halting pair for `e`.

Thus even a computable cardinality bound does not provide an effective bound on the indices that must be searched. A finite truncation implementation needs an effective index cutoff, a supplied finite list with a completeness certificate, or comparable extra information. This observation does not refute the source's mathematical finiteness theorem or an asserted general algorithm: the nearby effectivity discussion already keeps comparison oracles and certified computation separate. I recommend preserving this distinction in any future compiler use rather than relabeling the theorem as a uniform evaluator.

## Limits, credited unresolved claims and arithmetic boundary

The guide attributes a directional Borel-sum counterexample and records that the corresponding conjecture clause was corrected elsewhere. I read that status in the guide, README and `SOURCES.txt`; I did not independently re-prove its contour calculation, audit the corrected monograph, or verify the external resurgence theorems. Likewise I did not audit the quartic asymptotics, optimal Bessel bounds, sine-kernel continuation, eta factor-count construction, cusp modular identities or q-gamma identities outside the declared spans. Guide claims of equivalence to prior theorems, uncited antecedents, historical novelty, and absence of other errors remain attributed claims, not new certifications here.

The standing retention rule was read. No claim is proposed for deletion. The packages retain explicit questions about parameter-uniform inversion, cancellation bounds, coalescence, later sheets, critical charts and effective computation. The reported “three” or “four” eta/Euler factors are counts of analytic product factors, not paid additions/multiplications of an ordinary-integer polynomial. Numerical precision, a finite wall count, a coefficient cutoff and an analytic tail inequality similarly do not determine an arithmetic-circuit count.

No fixed finite integer encoding of arbitrary input computations, sound-and-complete unbounded-history representation, fixed-arity polynomial, or fully paid source is provided by the selected interfaces. The established universal arithmetic constructions and unresolved candidates therefore retain their previous status.

Only the fresh `/tmp/review_transseries_6132faa30.py` was executed; SHA-256 `6cdd6d9828cbcb3d24fc20c05570c702cfd9cac7e7c56cfb5302060807988e78`. Its receipt `/tmp/review_transseries_6132faa30.json` has SHA-256 `47e291e7955857182fdbc11e26cee96f85f0519f1a1960498475b1c34e57ed5f`. Fresh normal and optimized exact replays from `/` passed. It used only read-only Git and in-memory archive inspection plus the two independent bounded mathematical checks. No supplied, archived, frozen or copied predecessor code was run or imported, no TeX or other build was invoked, no external sources were fetched, and no repository or Git mutation occurred.
