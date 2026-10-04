# Independent manuscript and all-page review of Report 58

Date: 4 October 2026 UTC

## Verdict

**PASS.** The final manuscript correctly presents the native three-positive-input certificate and the separately paid one-positive-input transport, with complete positive-domain adapters and both directions of the mathematical argument. The primary counts are **81 witnesses, 44 equations, 344 binary gates** and **85 witnesses, 46 equations, 367 binary gates**, respectively. Both have exact total degree 12. The optional quartic variants and their tradeoffs are stated accurately. No outstanding mathematical, source-attribution, literal-arithmetic, or visual correction is required.

This review binds the final editable source and 19-page PDF:

| Object | SHA-256 |
|---|---|
| `Report58.tex` | `cc1ffd8ce344dcf45d89d40d4ceadff8eb2decc513c595bdf7b4462465864e89` |
| `Report58.pdf` | `af5c8fcda60078976735473b16c027963ce68ee4e1ca58b2581a143fd79b837e` |

The sole editorial issue raised during review was the potentially ambiguous phrase “zero pair” for the Pell initial pair. The author changed it to “zero-index pair (1,0).” Replacing that phrase in the revised source restores exactly the initial source SHA-256 `ce3b007f5e913ecfa61ac375f9cff9cf5d04f7c3b6c56f63f6c84b4f9c8dcc69`, so no other source edit occurred. Only rendered page 10 changed. Its revised rendering was directly reinspected and passes; the other 18 pages are byte-identical to the independently rendered pages already directly inspected.

## Method and independence

I read the complete LaTeX manuscript, the supplied local physical proof, the relevant boundary/arithmetic companion, the pinned Pell theorem statements and constructive proof text, and the independent scientific audit reports. I checked the inherited statements against those actual local dependencies, rather than treating a previous PASS as a substitute for the manuscript proof.

I wrote and inspected a new standard-library exact-algebra program, `check_manuscript_algebra.py`. Its specification is a direct transcription of the manuscript's equation sides O1–O14, P1–P15, and D1–D2 with their stated positive adapters. It parses the four JSON DAGs as inert data. It neither imports nor executes a supplied scientific program. It matches both sides of every equation, expands the complete output, checks its exact sum-of-squares decomposition, verifies the literal assembly tail, computes every coefficient and the degree-12 component, counts raw operations and leaves, and checks graph and polynomial-support liveness. This independently verifies 360 equation sides over the four sources.

The twelve stored full positive-witness assignments were also treated as data and reevaluated with my own raw-gate evaluator and independently expanded polynomials. Every entry is a positive integer; all equations and outputs vanish. Printed geometric and orientation fixtures were recomputed separately with integers and exact fractions.

For visual review, I independently rendered the released PDF at 120 dpi and directly viewed every page 1–19. I then performed a fresh direct TeX compilation of the revised source, using a new format/cache, fixed source-date metadata, three passes, installed system packages/font maps, and disabled shell escape. No supplied build script was executed. The independent revised PDF is byte-identical to the final released PDF. The revised page 10 was directly reviewed; exact page-image comparisons bind every other final page to the earlier direct inspection.

No author emitter, author semantic checker, old source checker, upstream scientific program, physical simulator, trajectory replay, portable scientific replay, or Lean executable was run for this review. The only scientific execution was newly written, inspected exact algebra. Standard typesetting, PDF-rendering, text-extraction, and hashing tools were used for document verification. No frozen science or independent scientific-audit file was changed.

## Mathematical presentation

### Scope and input representation

The native theorem explicitly quantifies 81 independent positive-integer witnesses over three independent positive gap inputs. The paid theorem explicitly quantifies 85 witnesses over one positive external code; its three decoded gaps and natural inner Cantor value are counted. It does not silently identify a native three-input relation with a one-input polynomial.

The domain convention is explicit: naturals include zero, while all final inputs and witness leaves are strictly positive. The paid decoder is total on every positive code and uses two polynomial equations without division primitives or a code-validity promise. The diagonal/offset proof supplies unique decoded gaps, and the manuscript correctly refrains from inferring unique existential witnesses.

The report expressly distinguishes finite input-only polynomial-sign classification from existential integer representation. It makes no real-witness, finite-fold, unique-witness, optimality, undecidability, priority, or new physical-threshold claim. Signed-pair adapters indeed provide infinitely many assignments at any solvable input.

### Physical dependency and coordinate reduction

The inherited machine is precisely identified: five live signals, outgoing ordered section, complete contracted macro, 138 strictly time-separated binary collisions, and the stated matrix. The matrix, normalized forward rotation, critical squared radius, and tangency point agree with the supplied physical proof. Infinite validity is attached to the complete collision word and its strict tie exclusions, not merely to matrix iteration.

The coordinate identities are correct:

- D = g1+g2+g3; A = 3g1−D; B = 3(g1+g2)−2D
- rho²−|omega|² = [4D²−205(A²+B²)]/(1845D²)
- omega/p = [(6A−13B)+i(13A+6B)]/(2D)
- U²+V² = 205(A²+B²)

The forbidden orbit is the **nonnegative inverse** orbit `(3−4i)/5`, including its exponent-zero contact. The natural deficit allows circle equality, while exterior points cannot satisfy O1. The manuscript preserves the physical theorem as an inherited conventional dependency and does not claim to reconstruct or simulate its chronology. The optional uncontracted remark correctly refers to an explicitly closed variant, not to a truncated open phase cycle.

### Domains, primitive fraction, and valuation

The outer count is 7 natural quantities, 6 directly positive quantities, and 8 signed quantities, hence 7+6+16 = 29 positive leaves. A natural is exactly a positive leaf minus one; a signed integer is exactly the difference of two positive leaves. Both maps are surjective onto their intended domains, and all adapters appear in the raw arithmetic.

O2–O5 force a primitive integer triple `(u,v,q)` and the exact positive gcd h. The three-term Bézout proof of the least common positive denominator is complete: any d clearing both coordinates has q dividing du, dv, and a3dq, hence q divides d. No individual-coordinate lowest-terms assumption is used. Negative or zero components are handled. At U=V=0, h=2D and `(u,v,q)=(0,0,1)`; choosing a3=1 supplies the identity.

O6–O8 correctly impose q=5^n r with 5 not dividing r. Positivity of both s and t and s+t=5 gives s in {1,2,3,4}; k remains natural. This proves n=v5(q), rather than merely a lower valuation bound. At q=1, the canonical values n=0, r=1, k=0, s=1, t=4 remain legal. These conditions apply at interior points too, without an uncharged selector.

### Gaussian coefficient extraction and orientation

The binomial congruence in Z[X]/(X²+1), followed by X=b, is valid. With b=4P+1, the difference estimate is

`|dC+b dS| ≤ 2P(1+b) = 8P²+4P < b²+1 = 16P²+8P+2`.

Divisibility therefore forces that difference to vanish, and 2P<b then separately forces dS=dC=0. The four natural slacks impose closed bounds. This is essential at exponent zero, where P=1, b=5, T=1, C=1, S=0. No unsupported bound on the signed quotient kappa is imposed.

The inverse-orbit denominator argument is correct even though the quadratic quotient modulo 5 is not a field: `(3+i)²=3+i` and both coordinates remain nonzero modulo 5 for positive powers. The exact joint denominator is therefore 5^m; exponent zero has denominator 1. Combining this with canonical valuation forces m=n and r=1. The acceptance term is correctly `v+S`, so the accepted forward boundary point is not confused with the rejected inverse orbit.

### Soundness and completeness

The polynomial is a fixed finite sum of residual squares. Integer nonnegativity makes its zero set exactly the simultaneous equation zero set. There is no variable-length conjunction or hidden exponentiation operation.

Soundness derives nonnegative radius deficit, exact powers, primitive denominator, canonical exponent, and unique extracted coefficients before using positive J. A nonzero final square sum means either strict interior or a boundary point outside the forbidden inverse orbit; the inherited physical theorem then gives validity.

Completeness selects the natural deficit, gcd, primitive numerators, signed Bézout coefficients, canonical valuation data, both constructive POWER witness tuples, true Gaussian coefficients, closed-bound slacks, and an integral extraction quotient. The final square sum is strictly positive exactly as required, and every conceptual value admits its positive-leaf adapter. The construction is simultaneous and has no circular assumption about an unproved base or exponent hypothesis.

### POWER subsystem and source specialization

Both actual 15-equation instances printed in Appendix A match the generic formulas, including all signs and the substitution of bases 5 and 3+4b. The common natural exponent is shifted to k0=e+1, and the output is shifted to the target m0=B0 o. This keeps exponent zero in the positive-index branches and recovers o=B0^e by cancellation of the positive base.

The local Pell source has precisely the statements cited at lines 760–766 and 860–864 and the constructive/reverse proof ranges printed in the manuscript. The initial pair is `(1,0)`. P1–P9 encode the nonzero branch of `Pell.matiyasevic`; P10–P15 encode the positive-base, positive-index branch of `Pell.eq_pow_of_pell`. The modulus M is correctly kept distinct from the separate Pell coordinate t.

All domain strengthening is justified in both directions:

- The positive leaves aMinus1 and betaMinus1 give a,beta≥2
- Pell equations with result 1 convert natural truncated subtraction into ordinary integer equalities
- P13 and w≥B0≥2, g>0 imply a>w≥B0 before using the power theorem, so a−B0 has the required natural meaning
- A constructive natural g cannot vanish without forcing a=1
- k0≤y and k0≥1 give y>0; the Pell equations give x,u,s>0; v>0 is explicit in the source
- Divisibility and positivity give qv>0; beta>1 and the congruence give qb>0
- t cannot be zero because t≡k0 modulo 4y with 1≤k0≤y<4y
- All four congruence quotient pairs represent either sign and zero using natural adapters
- Positive Jp imposes the essential strict bound m0<M

Each module has exactly 13 directly positive, 2 shifted-positive, and 11 natural-adapter leaves, totaling 26 including its output. Each literal body has 70 gates. The second base is 16P+7≥23 directly from the positive output leaf, so its lower bound does not depend circularly on the first module's conclusion. The proof is conventional specialization against pinned local text, not a newly kernel-checked Lean development or a new authentication of a remote commit.

## Literal source, ledger, and exact degree

The fresh exact check confirms these complete counts:

| Variant | Inputs | Witnesses | Equations | Multiplications | Additions | Subtractions | Gates | Collected terms |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| Native linear | 3 | 81 | 44 | 136 | 110 | 98 | 344 | 772 |
| Paid one-input linear | 1 | 85 | 46 | 144 | 118 | 105 | 367 | 802 |
| Native quartic | 3 | 80 | 44 | 139 | 109 | 102 | 350 | 775 |
| Paid one-input quartic | 1 | 84 | 46 | 147 | 117 | 109 | 373 | 805 |

The native regional ledger agrees with the actual operations, including multiplication by fixed constants. The literal SOS tail consists of one difference and one self-product per equation, followed by an unweighted chain summing each square exactly once. Its cost is 3E−1. The paid decoder contributes 17 body gates and six additional assembly gates, totaling the advertised increase of four witnesses, two equations, and 23 gates.

The exact full expansion has degree 12 in the independent input and positive-witness leaves. Its entire degree-12 part is

`power5.w^8 power5.g^4 + power_complex.w^8 power_complex.g^4`,

with coefficient +1 for each monomial and no other degree-12 term. This follows both from the P13 leading term `−w^4 g^2` and from independent coefficient collection. The optional quartic guard produces degree-eight SOS terms and does not alter this top form. Replacing s+t=5 with the quartic guard removes one witness and adds exactly six gates, with operation delta (+3 multiplications, −1 addition, +4 subtractions). All inputs and witnesses are graph-live and occur nontrivially in collected polynomial support.

## Evidence claims and attribution

The printed finite challenge counts agree with the included arithmetic receipt: 15,625 gap triples, 606 scaled orientation cases, 820 rational-circle cases, 12,500 denominator/Bézout cases, exhaustive bounded extraction for n=0 through 3, 20,000 code round trips, and 8,000 gap round trips. These larger prior challenge sets were checked as evidence records, not rerun under another checker's authority. This review independently repeated the exact source checks, all twelve complete positive assignments, and the printed coordinate/orientation fixtures.

The stated rejected contact, accepted forward point, accepted eta=−1 and eta=i boundary points, center, and exterior example have the printed values. The malformed-bound example is arithmetically consistent: C=27 at the contact preserves the extraction congruence with kappa=−1 but violates the upper bound by −26 and yields squared output 676. The omitted-Bézout and undercounted-valuation examples yield the claimed false positive acceptance sums 20 and 36. Their guards block them for the reasons given.

The full witness file indeed contains twelve complete positive assignments. Its largest entry has 78 decimal digits. The report does not claim full enormous nonzero-exponent Pell tuples were tested for every orbit challenge; it correctly attributes the all-exponent assertion to the constructive theorem and proof. The discussion of neutral mutations at zero Bézout coefficients is mathematically appropriate.

All sixteen Appendix B pins match the actual included files. All eight entries of `science/sources/SOURCE_PINS.json` match their recorded SHA-256 values and byte lengths. The entire 33-file science tree and 11-file independent-audit tree are byte-for-byte identical to their original frozen roots; details are in `FROZEN_TREE_IDENTITY.json`.

The named physical, arithmetic, and audit dependencies are present and clearly distinguished. The pinned local Pell file and license are present. The bibliography's remote locator is an attribution locator, not represented as newly authenticated. The replay and 33-case portability claims agree with the supplied replay/test/review receipts. This manuscript review does not replace the separate portability/tool-safety review, and it did not execute that replay.

## Optional univariate-sign corollary

The corollary is correct for this specific positive Cantor encoding. Every nonzero univariate real polynomial has an eventually constant sign on the positive tail; the identically zero case is constant too. A finite Boolean combination is therefore eventually constant. The accepted rays `(t,t,t)` and rejected contact rays `(217t,167t,231t)` give unbounded sequences of codes of both outcomes, contradicting eventual constancy. The proof needs no stronger undecidability or lower-bound assertion, and the report explicitly disclaims those interpretations. It is fully compatible with the paid existential integer certificate.

## All-page visual review

Each page below was opened and directly inspected. Final page 10 was reinspected after the sole wording edit; all other final page PNGs are identical to their earlier reviewed versions.

| Page | Material reviewed | Finding |
|---:|---|---|
| 1 | Title, date, abstract, first contents portion | Clean; clear hierarchy and readable counts |
| 2 | Remaining contents | Clean; deliberate contents continuation and consistent folio |
| 3 | Native and paid main theorems, matrix, pairing definition | Clean; long source paths and display formulas remain inside margins |
| 4 | Scope qualifications and physical coordinate identities | Clean; radius/eta formulas and inverse-orbit condition legible |
| 5 | Outer domain table and all fourteen equations | Clean; distinct equation tags and complete domain explanation |
| 6 | Positive adapters, SOS definition, gcd and valuation lemmas | Clean; proof equations and zero-component discussion readable |
| 7 | Valuation proof and bounded Gaussian extraction | Clean; strict comparison and exponent-zero endpoint legible |
| 8 | Inverse-orbit recognition, both theorem directions, Pell pin introduction | Clean; orientation signs and mathematical subscripts legible |
| 9 | Local source hash and all fifteen POWER equations | Clean; all equation tags and domain/count text visible |
| 10 | Precise pinned theorems and integer/congruence adapters | Clean in final revision; zero-index pair (1,0) unambiguous |
| 11 | POWER completeness, zero exponent, paid decoder start | Clean; all crucial positivity and strictness conditions visible |
| 12 | Decoder proof, regional ledger, leading-form proposition | Clean; ledger columns align and top-degree formula is readable |
| 13 | Degree proof continuation, optional tradeoff table, audit scope | Clean; counts and distinction between terms/gates visible |
| 14 | Challenge set, orientation fixtures, adversarial cases, complete witnesses | Clean; table and signed values readable |
| 15 | Witness limits, sign corollary, provenance start | Clean; explicit assurance distinctions remain visible |
| 16 | Reproducibility limits and instantiated POWER appendix start | Clean; long prose wraps normally; appendix tags clear |
| 17 | Both actual POWER instances and namespace clarifications | Clean; long second-base equations fit without overlap |
| 18 | Sixteen source pins and beginning of references | Clean; long paths/hashes wrap within columns without clipping |
| 19 | Remaining references and pinned remote source locator | Clean; locator wraps within margins; consistent final folio |

There are no missing glyphs, black boxes, clipping, text/formula overlap, unresolved references, broken equation tags, or materially unreadable tables. The final compile log has no overfull/underfull box or unresolved-reference warning. The sole package warning states that shell escape is disabled, as intended. The sparse contents continuation and final references page are acceptable consequences of a conventional mathematical report layout and do not obscure content.

## Receipt files and final assurance boundary

- `ALGEBRA_AND_BINDING_RECEIPT.json`: final source/PDF bindings, exact residual and polynomial data, source-pin checks, full positive-witness reevaluations, and page hashes
- `SOURCE_PDF_BINDING_RECEIPT.json`: independent direct compilation and final released-byte equality
- `FROZEN_TREE_IDENTITY.json`: complete byte identity with both original frozen trees
- `REVISED_PAGE_COMPARISON.json`: page-by-page original/final image identity, with only page 10 changed
- `check_manuscript_algebra.py` and `algebra.stdout.json`: newly written inspected algebra and execution result
- `independent-compile-*.log`, `independent-format.log`, and `Report58-independently-compiled.log`: direct typesetting evidence
- `pages/`: the final independently rendered page images

The conclusion is a manuscript-level mathematical and source-specialization audit, independent exact inert-DAG checking, and complete visual review bound to actual PDF bytes. The physical theorem and underlying Pell development remain inherited dependencies. Finite tests and byte identity do not become a fresh formal proof of those dependencies. Within this expressly stated scope, Report 58 passes without an outstanding correction.
