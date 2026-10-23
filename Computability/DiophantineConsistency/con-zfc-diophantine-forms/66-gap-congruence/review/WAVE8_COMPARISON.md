# Wave-eight intake and research comparison

Reviewed 23 October 2026 against main `beb0192cb8dc36f78c369c080f2adfbc1887a486` and arrival `7331974b696693a8eed2aa5f0f64f1c19d9569f0`. The six archives are placed as sources 54–59 in `Computability/DiophantineConsistency/con-zfc-diophantine-forms` by the main pin. The arrival pin is used to preserve exact ZIP bytes; placement omits duplicated inherited files. `SOURCE_PINS.json` gives exact paths, Git blob SHA1 and outer SHA256. All six Git blobs, ZIP CRCs and 1,729 declared member hashes pass independent read-only inspection. No incoming program has been executed or imported.

## Claimed exact frontiers and literal operation checks

The table records the incoming authors' exact-degree claims. Independent intake parsed 141 supported literal JSON arithmetic DAGs, found no dead gates, invalid forward references or claimed operation-count discrepancy. This is an operation-structure audit, not an independent proof of all incoming exact degrees or consistency equivalences. Some inherited circuit copies are included in the 141 count. Domains are not interchangeable.

| Package | Domain | Operations / degree | Main contribution |
|---|---|---|---|
| 54 calibrated carry (previous round) | 9 positive | 490 / 9,461,300; 564 / 4,400,764; 598 / 4,399,820 | Selective positivity, calibrated thresholds, refined quotient majorant |
| 54 calibrated carry | 10 integers | 513 / 25,838,224; 554 / 14,699,152; 558 / 14,696,016 | Conditional equal-weight separation |
| 55 congruence norms | 10 integers | 586 / 9,152,284 | Two-root quartic norm, coprime combined square/positivity guard |
| 55 congruence norms | 9 positive | 604 / 6,692,108; 630 / 5,671,669 | Congruence separation, globally shifted positive word |
| 56 free coordinate | 9 positive | 560 / 4,686,812 | Free C, translated quotient sign recovery, shorter leading-block-free carry |
| 56 free coordinate | 15 positive | 73 / 54; 74 / 46 | Gap minimum and regrouped forced unit |
| 57 separated degrees | 9 positive | 499 / 2,628,944 | Separate kernels for degrees 0, 1, 2 |
| 57 separated degrees | 10 integers | 544 / 8,317,400 | Same packed source with signed positivity repair |
| 57 separated degrees | 12 positive | 89 / 258; 94 / 242 | Two quadratic norms, canonical Pell ordinate congruence, factor deflation |
| 57 separated degrees | 13 positive | 83 / 132 | Intermediate low-degree tradeoff |
| 57 separated degrees | 45 integers | quartic | Dyadic/product positivity guards; 28 quadratic residuals |
| 58 integral root | 15 positive | 79 / 30; 88 / 26; 90 / 24 | Monic square carriers recover omitted divisibility |
| 58 integral root | 12 positive | 114 / 629 | Desaturated product, dominated by package 57 |
| 59 degree separated | 9 positive | 473 / 1,910,404 | Three kernels, two elementary row operations, free-C composition |
| 59 degree separated | 10 integers | 533 / 8,469,528 | Three-kernel source with Sun finalizer |
| 59 degree separated | 13 integers | 518 / 11,543,632 | Coprime guard absorbs external radical weight |
| 59 degree separated | 12 positive | 102 / 316 | Ordinary Pell root merger; dominated by package 57 |
| 59 degree separated | 13 positive | 91 / 126 | Lower degree than package 57, higher cost |
| 55 and 59 | 14 positive | 79 / 52 | Auxiliary gap with stronger modulus |

For nine positives, package 59's 473 / 1,910,404 dominates every displayed wave-eight nine-positive point. For ten integers, 533 / 8,469,528 and 544 / 8,317,400 are the incoming low-degree tradeoff; the previous round's 513-gate point remains a cheaper high-degree option. Fifteen-positive short endpoints include inherited 66 / 157 and 75 / 44, package 56's 73 / 54 and 74 / 46, and package 58's 79 / 30, 88 / 26, 90 / 24. No single metric defines a global simplest equation.

## Strong synthesis opportunities

### 1. Replace homogeneous packing, not merely its shift set

Package 59 separates the source by ordinary degree:

G(B,U) = D2(B) U^2 + D1(B) U + D0(B).

Unlike one dummy-coordinate homogenization, degree-one and degree-two labels can coincide without interference. Elementary row operations rho14=r14+r2 and rho15=r15+r3 preserve the zero set and reduce the source to 89 records (7 constant, 39 linear, 43 quadratic). Exactly 22,544 same-degree interactions establish the 22 target identities. The supplied certificate has maximum weight 116, maximum target 2,129, degrees D0=1,719, D1=2,027, D2=1,929 and convolution height 2,161. Its shared positive word U=ell+g enforces all coordinates positive without expanded shifts. A signed source adds only B^2162; completing the square makes its value positive for every real U. These mathematical changes supersede the old task of minimizing shifts within one homogeneous code.

Package 57 independently uses the same architecture with an all-real repair B^1915(U^2+1). Its source certificate and fixed tuple differ. Do not transplant a coefficient leaf or exponent without reconstructing every identity, positivity bound and carry threshold.

### 2. Compose congruence separation with the smaller packed source

Package 55's arithmetic tail appears valuable despite its dominated complete metric. It normalizes b=6t+4, g=bg0, h=bh0 and k=b(3k0+2). Its source must imply X odd, X+1 divisible by b, X divisible by 3, and Y divisible by b. The canonical completeness proof obtains the stronger congruences from actual Lucas indices, not by asserting arbitrary witnesses can be restricted.

Let Q=((P/2)^2-1)K^2+1, r=bQ and a=r+(3Delta-1)(rz)^2. Coprimality and residues 1 modulo 3 force b,Q positive squares and Delta>0 once a is square. The other radicand d=DFI has a/b odd and d/b even identically; hence a != d for every signed assignment. The elementary two-root rational reconstruction lemma then replaces an eight-factor norm by a quartic. This is a potentially strong composition with degree-separated coding, but its source congruences and completeness restrictions must all be re-established.

### 3. Integral-root carriers can beat the older short-degree frontier

Package 58 retains a monic norm:

(q^3(ell+r)+Y)^2 = q^6(ell(ell+k)+1).

Rational-root integrality forces q^3 to divide Y. A second norm forces q to divide X. Thus X,Y can be free inputs rather than high-degree substitutions. Positive canonical Pell gaps supply the reverse witness transformation. Reducing an auxiliary expression modulo a retained index residual lowers degree 26 to 24. This gives a different way to trade a few gates for much smaller degree than merely regrouping product factors.

Package 57's two quadratic norms and known canonical residue y_old=-1 mod Q similarly permit y_old=M*y-1 and exact factor removal. The best twelve-positive input baseline is now degree 242, not 629, 897 or 954. Careful objective comparisons should use this new frontier.

### 4. Possible combination with last round's sharper majorant

Package 59's best nine-positive form already incorporates the free-C and shortened carry improvements of package 56. The last round's refined 2048-scale quotient majorant is not automatically compatible with every free-C parametrization; its unconditional A,C lower bounds, positivity-first argument and positive root-coordinate reconstruction must be checked. Degree comparison should separate the packed source height from the final norm's exact cancellation.

## Formal proof status has advanced, but is not an end-to-end certificate for these new circuits

At main pin, commit `dabf4e39f1039a7f77056517ecbb01d6db1a8ced` formalizes package 52's literal 60 source gates, 22 positive residuals, 136 shifted records, 71 active pairs, selective kernel degree/leader, bounds, low-mask decoding, cofinal completeness bounds, Jones ratio substitution and margin-first finalizer. The updated `MARGIN_FINALIZER.md` states the exact natural-root equivalence under explicit majorant/separation hypotheses and explains rational reconstruction without prior square-root sign assumptions. The new source adapter's assembly, actual native-port calibration, closed replacement equation, and internal object-ZFC equivalence remain open. Earlier closed baseline equations are preserved.

Five directly pinned status/proof documents are retained under `formal/`, each verified against its genuine Git blob. Their status claims are read, not recompiled in this intake. They must not be presented as a kernel certificate for the new wave-eight or round-nine polynomials.

## Reproducible intake

Run the newly authored `check_intake.py` and `check_literal_ledgers.py` from this directory. These scripts only read JSON/ZIP/text and never import incoming modules or execute incoming scripts. `INTAKE_CHECKS.json` and `LITERAL_LEDGER_CHECKS.json` are the resulting receipts. The whole archives are useful local research inputs but need not be duplicated in a final release; retain relevant members with their archive/member identities and license notices.
