# Review of the twelve-archive batch80 intake

All twelve archives committed at `4e270aa4648c5fd7e18626507531046715976535`
have completed their scoped mathematical/source reviews and executable checks.
The [intake inventory](incoming_substrate_review_4e270aa46_inventory.json)
authenticates all twelve archive hashes and **388 member occurrences**. This
counts each published occurrence, including identical files across editions;
it is not a count of distinct theorems or independent implementations.
The inventory was compared with the exact upstream addition list and all four
review receipts. Original archive bytes remain available in Git after placement.

“Complete” here means the proof/source scope documented in each review plus
its actual replay evidence. It does not mean a proof-assistant certification,
a literature-priority result, PDF visual QA, or a universal-operation improvement.
Root read each frozen review and checker and independently reproduced each saved
receipt. Repairs are separate patches tested on private copies.

## Archive coverage

| Archive | Members | Review | SHA-256 |
|---|---:|---|---|
| `Eager_Tree_Calculus_Research_Package_corrected.zip` | 58 | [Eager Tree Calculus: corrected edition](review_batch80_corrected.md) | `2c053f50027ec632c2773c9d2ec3e2ace9f621eef5c08bebce0ca06c2d0f3dbd` |
| `Reset_Petri_Net_Certificates_corrected.zip` | 87 | [Reset Petri nets: corrected edition](review_batch80_corrected.md) | `8d5b9b1a52c33aeadb8b4200fd9c138bd016f2651ebcfccf1a939e03715486d3` |
| `Sparse_Lattice_Diophantine_Certificates_corrected.zip` | 52 | [Sparse lattice: corrected edition](review_batch80_corrected.md) | `cf9b546baaece745c047f6ce33574d10104f03c9849f4114626a916c1deec1e2` |
| `Three_Mass_Reversible_Computation.zip` | 66 | [Three-mass reversible computation](review_batch80_three_mass.md) | `fd86a8a6b71735ef08ebd7913498603213244484da8b23d81876b10c40ffd1de` |
| `Exact_Targets_Three_Mass_Units.zip` | 38 | [Exact-target cleanup](review_batch80_three_mass.md) | `d69d8df9ee3a2074bcff1ef400853724eafb679ada8b287ef397eb8891965dcc` |
| `Four_Mass_Decidability_Package.zip` | 33 | [Four-mass decidability](review_batch80_low_mass.md) | `0bcc026a8ca7bd4745b82e6f9c2841073e5fb8c639970105690fc40803a780fe` |
| `Single_Unit_Three_Mass_Decidability.zip` | 12 | [Single-unit three-mass: original](review_batch80_low_mass.md) | `25c0d2712b111ba9240fb11b23689b3eded14b059a5a793e33aa515f1c97f646` |
| `Single_Unit_Three_Mass_Decidability (1).zip` | 13 | [Single-unit three-mass: revised attribution](review_batch80_low_mass.md) | `299fef3508423dfe1fc88dc3473a39a40eac7cbfaf5d53c16dc26b9a3d119b12` |
| `Surreal_Well_Orders_Research.zip` | 8 | [Surreal Research](review_batch80_surreal.md) | `8aebf0ab80207a4e2165be6f7a329eff18b90134128b02e65c4732c97c252ee9` |
| `Surreal_Well_Orders_Research (1).zip` | 7 | [Surreal Research(1)](review_batch80_surreal.md) | `36c7f6ac22cd2a665aa078eb99eeffef170cb2d6c0cadab31417562f147d8179` |
| `surreal_well_orders.zip` | 8 | [Surreal lower-case](review_batch80_surreal.md) | `1edf59eaa0febdc0b7c9da581d9a6a65cc2ae88b99c166756ffd58f8aa4d4d5d` |
| `surreal_well_orders (1).zip` | 6 | [Surreal lower-case(1)](review_batch80_surreal.md) | `e48ab1b54681787324fd01953ba093d2b7abe546673ccd0f0a0bcb59e232e33a` |

## What the new results establish

The apparent conflict between mass-three universality and mass-four
decidability disappears once the unit labels and observation are specified.

| Model/interface | Reviewed result | Arithmetic consequence |
|---|---|---|
| Weighted Boolean-channel CA; many distinct weight-one labels | A fixed reversible CA can simulate a fixed universal reversible two-counter source with three conserved units; both radius-one wrappers retain their stated time conventions | Physical mass and radius do not bound the channel alphabet, branch table or Diophantine arity; no numerical universal source table is expanded |
| Exact-target cleanup of that source | First halt after `h` steps becomes first arrival at the whole input-dependent target after `2h+2` source steps | The reverse certificate is uniquely reconstructed from the forward certificate on natural zero sets |
| At most one weight-one label; mass at most three | For each fixed finite CA, sparse timed reachability is uniformly Presburger-definable | Quantifier elimination followed by the canonical compiler gives formula-dependent quartics; external-coordinate bounds do not bound auxiliary arity |
| At most one weight-one label; mass at most four | Exact-target and finite-pattern reachability are decidable; the stationary-frame untimed description is for a fixed input | The binary shuttle has return times `k²+(2d−11)k`, disproving a blanket timed-Presburger extension |
| Surreal/class well-orders | Complementary embedding, interpolation, coding-rank and class-uniformity results under explicit set-theoretic hypotheses | No effective universal machine or scalar Diophantine interface follows from order-embedding universality |

The two mass thresholds are not interchangeable: the universal channel
construction uses many unit labels. The unique-unit theorems also retain
positive integer weights, finite radius/alphabet, a unique quiescent vacuum,
and the specified sparse observations. They do not obstruct general
Diophantine representations or signed/zero-mass-background models.

The useful certificate saving is explicit. With `B` residue-expanded source
branches and external first-halt horizon `h`, the compact exact-target core
keeps `2Bh` natural variables, `3h+1` affine-square slots and `Bh` nonnegative
affine-product slots. Directly certifying the full cleaned source uses
`8(B+1)(h+1)` variables, `6h+7` squares and `4(B+1)(h+1)` products.
These are slot counts, not complete arithmetic-operation totals. The affine
section copies the forward trace into the reverse slots and restores the two
bridges. It is a bijection on natural zero fibers; an explicit off-zero point
maps to a negative bridge coordinate and changes the polynomial value.
The horizon, input encoding, source table, affine evaluation and unbounded
history packing remain to be charged for a fixed-arity universal comparison.

The low-mass canonical corollary also admits the previously proved
[five-witness congruence substitution](presburger_congruence_five.md): after
Presburger quantifier elimination its auxiliary count improves from
`2I+6C+B` to `2I+5C+B`, retaining unique natural witnesses and degree at most
four. Here `C` counts congruences and `B` Boolean gates. No general CA-to-formula
compiler or concrete total saving is emitted by these new packages. The
existence-only congruence variants must not replace a canonical atom while
claiming uniqueness.

## Corrections, variants and validation

The [three corrected editions](review_batch80_corrected.md) implement the
previously identified exact-domain boundaries: eager application validates
both natural codes before cached use; reset helpers reject malformed public
markings/flags and enforce nonnegative initial counters without assertions;
sparse polynomials accept only exact canonical immutable terms. Every original
mathematical report and fixture is preserved. Six targeted normal/optimized
runs and comparisons of actual old/new valid outputs pass. The previously
reviewed unchanged full suites were not redundantly replayed for this revision.

The [three-mass pair](review_batch80_three_mass.md) passes both complete author
replays and 360 independently reconstructed literal core cases, 2,400 natural
assignments, 45 compact/full zero-fiber checks and 7,968 literal cleanup ticks.
Only enumerated metadata fields are normalized in its author receipts; all
sixteen regenerated native example exports are byte-identical. The fixed-target
phrase always means equality with the complete target specified by that input,
not one configuration shared by every input.

The [low-mass trio](review_batch80_low_mass.md) passes nine author invocations
and byte-exact regeneration of every compared export. The independent audit
checks all 8,192 binary local windows and conservation-potential edges,
full sparse orbits, signed first-entry arithmetic, huge exact-time boundaries,
and the literal six-operation timing quartic. The revised single-unit package
changes attribution; its complete mathematical body and executable sources are
unchanged. The same executable replay therefore covers both editions.

The [four surreal variants](review_batch80_surreal.md) are distinct,
complementary developments. All four original finite checkers reproduce their
saved outputs. Independent dyadic interpretations and finite combinatorial
checks support, but cannot prove, their transfinite results. One prose sentence
in Research(1) needs correction: in GBC, changing only the available classes
while fixing the sets and a relation cannot change that relation's internal
well-foundedness. The separate patch distinguishes relation availability from
internal/external well-foundedness and preserves the theorems.

No additional theorem or intended-verifier defect was found in the new
three-mass/exact-target or low-mass packets within the documented review scope.
Literature checks distinguish directly inspected primary statements from
unavailable full texts and do not make current priority claims.

## Current arithmetic frontier and follow-through

This intake leaves the established complete universal **single-polynomial
bound at 87 = 48M+39A**, with 19 positive witnesses and exact degree 169.
The separate **75 = 41M+34A** comparison-system bound also remains unchanged.
The [native Grill example](grill_tag_native_composed205.md) costs
205 operations with an unproved universal decoder; it is not a competing
universal bound. Degree-two external-horizon families and small physical-mass
models must not be compared with the universal polynomial as if their missing
interfaces were free.

The next arithmetic opportunity is to carry the proved unique reverse-history
projection through a fully paid fixed-arity source encoding. It requires a
specific universal source, an ordinary-input loader, unbounded-duration
representation, and a complete gate schedule. The present reviews establish
the projection and its precise domain, not that further construction.

Assembled-report transfers have separate revision boundaries. The [Tree Calculus
Part XIX editorial/source audit](review_tree_typesetting_954261e15.md) and subsequent corrected-code placement are
tracked separately from the original archive proofs. New catalogue and
surreal-collection edits are likewise checked as transfers, rather than
silently inheriting the archive review.
