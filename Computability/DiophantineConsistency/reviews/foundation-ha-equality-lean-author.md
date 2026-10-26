# Actual Foundation equality theory in HA — author receipt

Author: `circuit_reduction`. This is author review, not independent review.
The complete new main source, checks, preparation driver and freeze driver
were read before execution. The final source and checks were reread before
freeze. Only new owned files and private cache links were written; no frozen
source, vendor file, shared object, umbrella or Git state was changed.

## Frozen source and replay

| File | Lines | SHA256 |
|---|---:|---|
| `Lean/DiophantineConsistency/FoundationHAEquality.lean` | 194 | `56634bbbd2c1cea7dd2959a62dcf7eb6a394915d7908e9b23a89169fbe778cf6` |
| `Lean/DiophantineConsistency/FoundationHAEqualityChecks.lean` | 131 | `60c61fb523de7743dfab010f23a90c2bf547fa5b5ccf56b4457bda9bc06e47e0` |
| `reviews/foundation-ha-equality-dependency-replay.json` | — | `0e1256f899ab80021082845e54f28482c000e05f0760f2b8d833d688c4516a68` |

Snapshot: `e332fbef14fc0505ba1cc5a57a3deb3db184185c`.
Private overlay: `/tmp/foundation-ha-equality-m09zc399`.
Both direct fresh builds passed with `-M6000 -j1` and source-level
`Elab.async false`. Main passed on its first run with no diagnostics.
Checks passed after adding an explicit source-language annotation to two
constructor invocations; all theorem statements and arguments were unchanged.
The superseded failed check source and log are retained, not accepted.

Fresh main object SHA256:
`0535f9287057db0af8e5d00fce9ea6c9024bf87499f8b12678bb31c33ae82264`.
Fresh check object SHA256:
`4f89083871e60baa78a843323968fecc9fbfb3311ee648cdf2c1a2b1e1d82bd4`.
The exact commands, logs, source copies, drivers and prerequisite inventory
are recorded in the replay JSON and `reviews/foundation-ha-equality-author-replay/`.

There are 31 axiom reports. All use only `propext`, `Quot.sound` and, for
proofs depending on the reused Foundation implication equivalence,
`Classical.choice`. The checks explicitly print the axioms of
`LO.FirstOrder.Derivation.imply_doubleNegation`, which already has that
metatheory choice dependency. The target is nevertheless an actual proof in
the unchanged intuitionistic `HA.Derives` calculus: no choice, excluded-middle
or unrestricted double-negation-elimination rule is added to HA. The new
`equality_stable` and `lt_transport` themselves report only `propext` and
`Quot.sound`. No final report contains `sorryAx` or another custom axiom.

## Exact new theorem

```lean
theorem equality_axiom {σ : Sentence ℒₒᵣ}
    (h : σ ∈ Theory.eqAxiom ℒₒᵣ) :
    HA.Proves (FoundationPAHFSyntax.sentence σᴺ)
```

The premise is membership in the existing Foundation equality theory, not
an assumed predicate asserting provability of the desired image. The proof
eliminates that source membership and the actual symbol constructors:

| Source case | Actual source sentence | Target theorem |
|---|---|---|
| reflexivity | `Theory.Eq.refl ℒₒᵣ` | `refl` |
| symmetry | `Theory.Eq.symm ℒₒᵣ` | `symm` |
| transitivity | `Theory.Eq.trans ℒₒᵣ` | `trans` |
| nullary zero | `Theory.Eq.funcExt .zero` | `funcZero` |
| nullary one | `Theory.Eq.funcExt .one` | `funcOne` |
| addition | `Theory.Eq.funcExt .add` | `funcAdd` |
| multiplication | `Theory.Eq.funcExt .mul` | `funcMul` |
| equality relation | `Theory.Eq.relExt .eq` | `relEq` |
| order relation | `Theory.Eq.relExt .lt` | `relLt` |

Every named theorem targets `sentence` of the actual GG image. The source
quantifier counts are respectively 1, 2, 3, 0, 0, 4, 4, 4, 4. For the binary
congruence cases the source matrix compares slots 0 with 2 and 1 with 3.
Its trailing true conjunct is retained, as is the complete empty-conjunction
antecedent in each nullary case. Neither is erased by an undocumented
simplification. Nine independent definitional checks bind these formulas;
a structural negative control proves that dropping the zero-symbol
antecedent changes the literal formula.

## Constructive target proof and binder audit

`equality_stable s t` is an actual HA proof of
`doubleNeg (s=t) -> s=t`, obtained by eliminating the proved object-language
disjunction `s=t or not(s=t)` from `HAEqualityDecidable`. It does not infer
arbitrary formula stability from Lean's classical metatheory.

The source's implication is a classical NNF connective. `translated_imp`
therefore uses the already proved Foundation `imply_doubleNegation`
equivalence through the frozen `FoundationPAHFLogic.intuitionistic_proof`.
It keeps an arbitrary finite target context and discharges no arithmetic
assumption by fiat. No GG recursion has been copied.

For equality-congruence arguments, stable equality recovers the two ordinary
equalities from their GG images. Ordinary Leibniz equality then supplies the
required congruence. In the `<` relation case, the transported body is exactly
`doubleNeg (ltFormula s t)`, where
`ltFormula s t = exists d, shifted(s) + S d = shifted(t)`.
The proof transports this entire double-negated existential twice. It never
extracts its witness or invokes order decidability, order totality, or order
stability. All ambient terms are shifted underneath the temporary equality
hole, and the existing substitution identities remove that hole exactly.

Checks cover a free variable zero together with a distinct high free variable,
nonlinear parameter terms, an undischarged implication assumption retained
in the target context, the order-congruence implication under all three
explicit premises, and two layers of universal closure with surviving free
parameters. These are proof and syntax tests, not standard-natural-number
semantic evaluations.

## Dependency authentication and limits

The exact Foundation import walk remained the same 76 modules as the accepted
arithmetic packet; no genuinely new Foundation module was imported. Those
records remain in the accepted 95-module arithmetic215 trace inventory.
Their source, trace and all four object-companion hashes were rechecked.
The preceding arithmetic authentication already compares their Lake source
and output hashes with the accepted trace receipt; all those pinned receipts
were checked unchanged here.

Sixteen non-Foundation prerequisites were reused under exact source/object
pins: the prior twelve arithmetic/syntax prerequisites, plus the freshly
accepted arithmetic leaf, logical adapter, natural cases and equality
decidability. Compiler and package identities were rechecked. Only the two
new leaves were freshly compiled. This is not a fresh 92-module closure
replay, a broad Foundation rebuild, or a refresh of the native-equation
closure. Existing narrow imports avoid the `Matrix.map` collision.

The nine PeanoMinus order/geometric axioms and general induction transport
remain distinct obligations. This packet proves neither full PeanoMinus nor
full PA proof transfer, no arithmetic totality principle, and no final HA
consistency/equation equivalence. It preserves the existing arithmetic,
syntax, logical-map, negative-stability and GG packets unchanged.
