# Concrete proof plan and dependency boundary

**Landed in the tree (3 November 2026).** At Vladimir's direction the Claude
session took over this lane's source closure. The import closure of
`compact44-symbolic-model-unconditional-iff-prototype` (472 modules) was
promoted into `Lean/DiophantineConsistency/Compact44/`, and the copies
changed only import lines. The new
[`Compact44/IPRAOrdinary12`](../../Lean/DiophantineConsistency/Compact44/IPRAOrdinary12.lean)
gives native, standard and equality-only iPRA endpoints for the shifted
free-J literal. The record, with a per-module source/hash manifest, is
[here](../../reviews/compact44-source-promotion/README.md). The prototype
copies in this directory are retained as historical inputs.

The 94-, 92-, 91-, 90- and 89-operation successors followed:
[`Compact44/IPRAOrdinary12Chain`](../../Lean/DiophantineConsistency/Compact44/IPRAOrdinary12Chain.lean)
holds their endpoints, and [this record](../../reviews/ordinary12-chain-source-promotion/README.md)
covers the promotion of their 87 modules.

Open items:

- the literal-to-payload/PDF binding;
- the compact-tuple package reductions.

New work should import the `DiophantineConsistency.Compact44.*` tree modules.

The initial restricted-J literal is
`ordinary-unit-products/p12_ordinary_degree70.json`, SHA-256
`444c25b68fbfee600ae174cb5bad1931897a55ffe2f9570fd22f3281f6e97010`:
12 positive coordinates and 100 live binary operations. The current smaller
free-J candidate has 12 positive coordinates, 95 operations, and exact degree
70 at its pinned fixed tuple. Its graph hash and source-binding qualifications
are recorded in [the free-J prototype](free-j-prototype/README.md) and its
[independent audit](../../reviews/ordinary12-freej-prototype-independent-audit/README.md).
The two graphs quantify over J differently; a result for the restricted graph
cannot automatically be transferred to the free-J graph. Hashes and finite
checks do not prove the ordinary derivation.

**Port prerequisite.** The fixed compact44 `β=2^590069−1` differs from the
2011 endpoint's `β=2^94517−1`; the remaining three fixed ports must also be
bound as one complete tuple. First construct and verify the exact 12-variable
literal and positive shift over that tuple. Separately establish the needed
native checker/calibration for these particular ports. The old fixed 2011
endpoint is not a substitute, and model-uniform carrier lemmas may be used
only after their hypotheses are checked for the compact44 tuple.

**Residual split, precise target.** Let `A0`, `A1`, `N`, `bn` be the
candidate's exact literal subexpressions and `P=(1+A0)(1+A1)(1+N)-1`.
For every intended arithmetic model and positive valuation prove
`P=0 → A0=0 ∧ A1=0 ∧ N=0`, with signed expressions represented by the
repository's formal-difference pairs. One concrete route is:

1. Prove a 100-row literal-to-scalar identity and establish the exact three
   factors as signed pairs, without cancellation of nonunits or a hidden
   positivity assumption.
2. For `q=1+β(6j+1)`, prove `q` even from the compact44 parity facts. Hence
   `M=q³(q−1)` and `U=q²Y` are even. Independently prove
   `bn=2(1−Q)(n+V)` even. The six compiled finite `ZMod 4` lemmas cover
   the corresponding residue exclusions only; lift them through the signed
   pair residue map, including the exact associativity of `d·bn²·Q`. The
   [bounded model prototype](model-prototype/README.md) proves that the
   generic signed factor `1+AN²−d(2b)²Q` is not the negative unit. Its
   substitution into the restricted-J ordinary merger is supplied by the
   concrete split below; the free-J merger has its own polarized exclusion.
3. From the three-factor product being one, derive magnitude one for each
   factor, then exclude `−1` and conclude each factor is `+1`. The pinned
   `ArithmeticSignedPairs.magnitude_multiply` and `product5_magnitudes`
   may support a three-factor proof by padding with units; the pinned
   `ArithmeticAdaptiveFactorUnits2011.pairEval_residue` and
   `negative_residue` provide a candidate residue bridge. Their current
   declarations assume an `IΣ₁` model and concern different literals;
   applicability to this exact graph and the desired object theory must be
   proved, not inferred from matching names.

The bounded model prototype now compiles a generic signed-pair version of
step 3, plus both generic carrier exclusions and the ordinary factor
exclusion. Their composition uses no carrier exclusion, rank or port
hypotheses, but still assumes an abstract product-equals-one equation. The
[historical literal prototype](literal-prototype/README.md) now checks all
100 graph rows and proves the literal factorization, a separate integer
evaluation identity, and that an internal zero implies product one for the
three concrete signed factor pairs. The
[concrete split prototype](concrete-split-prototype/README.md) binds those
factors to residue exclusions and proves, in an `IΣ₁` model, that each
factor is the positive unit. This model-level result holds for arbitrary
integer ports; it is not compact44 checker calibration or an iPRA proof.

The [95-operation free-J prototype](free-j-prototype/README.md), with a
separate [bounded replay audit](../../reviews/ordinary12-freej-prototype-independent-audit/README.md),
proves the same factor-unit conclusion for its own exact graph using a
polarized ordinary-factor exclusion. Unlike the 100-row graph, its first
variable is a free `J`, not `6j+1`. The ordinary free-J soundness route
handles a possible exceptional factor three using rank growth and the
Mersenne coefficient, rather than deriving `J=1 mod 6` for every zero. That
argument and the rank and checker obligations remain open.

For this free-J route, the earlier suggestion of recovering `J=1 mod 6` is
only a possible restricted-parent bridge, not a required or established
property. The stated ordinary proof instead first derives the carrier
divisibility and window from the two carrier equations and port bounds,
then proves `q⁴∣v` allowing `gcd(q,H)=3`. It uses those facts for the early
Pell rank bounds *before* ordinary norm recovery. Only after ordinary norm
recovery yields the exact rank does it derive `X=2ᴿ` and `q∣3X`; the
Mersenne β argument must then eliminate `q=3·2ᵘ`. Each step still needs its
own formal model proof and, separately, the required object-level bridge.
The proof must not use the later strong norm to justify the early rank.

**Early rank before norm recovery.** With only `A0=A1=0` and the explicit
positive/port hypotheses, construct internal witnesses for the divisions
and Pell indices, proving successively `q³∣Y`, `q−1∣Bt`, `C>0`, the scalar
window `3q<R<q⁴−2`, positivity of `Dstar`, and `q⁴∣v` where `v=k−R−1` is
represented without unjustified natural subtraction. Prove the first and
main Pell index statements and their recurrence congruence, then derive
`p>m1≥24`, `c>(a+2)Δ²`, `c>2R`, and `V>c>1`. The pinned
`ArithmeticPellClassification`, `ArithmeticPellFirstNorm`, recurrence,
divisibility and `ArithmeticAdaptiveRankWindow2011.scalar_rank_window`
are candidates for reuse, subject to exact hypotheses. In particular,
`ArithmeticPellFirstIndex.first_main_indices` already assumes a strong norm
and auxiliary norm; invoking it to prove the *early* bounds before recovering
those norms would be circular.

**Ordinary norm elimination and transport.** From `N=0`, `Q>1`, `bn≠0`
and the early bounds, formalize the adjacent-coefficient rational-integrality
descent inside the intended model. State the signed divisibility explicitly:
obtain an integral signed `i0` satisfying `d·bn·i0=AN`, then obtain the
auxiliary witness and the ordinary strong equation `(ic²)²=Δ(f²−1)`.
Do not assume `Δ∣i`. The pinned
`ArithmeticPellIntegralSolution.integral_solution_tsub`,
`ArithmeticPellIndexDivisibility`, and `ArithmeticPellResidueAux` cover
parts of the subsequent Pell recovery under their stated hypotheses; the
new graph-to-hypotheses bridge and early size estimates remain to be built.
Formalize the displayed ordinary maps in both directions and check every
positivity/divisibility obligation rather than treating rational quotients as
internal integers automatically.

**Object-level conclusion.** An external Lean proof over `ℕ` or an `IΣ₁`
model is not by itself a proof that the required formula is provable in
iPRA. Use a fully specified syntactic bridge for the exact new formula and
the compact44 checker. The pinned `IPRAFullGGTransfer.from_classical` is a
candidate only after supplying its required classical PRA derivation and
checking the translated target; its source explicitly leaves identification
of the translated and chosen native consistency predicates separate. A
matched project replay and independent artifact audit must then check both
directions and the final axiom reports.

**Provider discipline.** Build only against an authenticated historical
parent and separately authenticated fresh sibling seeds; freeze new source
and check actual compiler dependencies and terminal exits. Do not mix the
recently merged `ModelArithmetic`, `ModelCarrierCurrent`,
`ModelCarrierScaled`, `ModelDifferenceRing` or `DiscreteOrderedRingFacts`
objects into that parent: those modules are not in its 1,210-row manifest.
They require a coherent source-current successor closure if used. A
[70-source coexistence pair](../../reviews/ordinary12-coexistence-pair-independent-audit/README.md)
has now passed an independent artifact audit. The two Lean files added by a
later upstream merge are outside that frozen closure; the 70 pinned sources
still matched the workspace at the audit. Package-transitive and dynamic
ancestry, and the original Foundation wrapper exit, retain the audit's
qualifications. The sampled resource monitor is not a hard per-build quota
or a continuously enforced free-space reserve. This pair checks coexistence,
not the missing ordinary-integrality or iPRA theorem.
