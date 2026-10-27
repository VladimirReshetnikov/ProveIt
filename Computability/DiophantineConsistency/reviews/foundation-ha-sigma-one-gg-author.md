# Actual Σ1 ordinary/GG comparison inside HA

26 October 2026. Author: `circuit_reduction`. This implements the generic
leaf in [the frozen proposal](../research/ha-sigma-one-gg-proposal.md), without
its later fixed-consistency specialization. Both prior DeltaZero/GG and
finite-DNS packets remain unchanged.

The 224-line `FoundationHASigmaOneGG.lean` proves, for the actual Foundation
syntactic premise `Arithmetic.Hierarchy Σ 1 p`, and arbitrary source
bound/free term environments `bv,fv`,

```text
HA.Proves
  ((formulaAux bv fv pᴺ → doubleNeg (ordinaryAux bv fv p)) ∧
   (doubleNeg (ordinaryAux bv fv p) → formulaAux bv fv pᴺ)).
```

`pᴺ` is the existing Foundation negative translation, and `ordinaryAux` is
the accepted eight-constructor ordinary NNF interpretation. No syntax type,
hierarchy predicate, or negative-translation algorithm was duplicated.
`sigma_one_doubleNeg_relative` gives the same genuine HA derivation under
any finite open context, by actual weakening.

The hierarchy induction retains the exact hypotheses `Γ = Σ` and `s = 1`.
All fourteen actual constructors are covered. Positive atoms are literally
double-negated ordinary atoms; negative atoms use stability only of a literal
negation. Truth and falsity are syntactically negative. Conjunction uses the
accepted finite double-negation pairing lemma. Disjunction preserves the
negative encoding and returns only double-negated ordinary disjunction.

For `exs`, the matrix IH at `liftBound bv,liftFree fv` gives the purely
intuitionistic equivalence
`¬∀¬C ↔ ¬¬∃A` from `C↔¬¬A`. Its proof composes actual quantifier
derivations `not_ex_all_not`, `encoded_ex_forward`, and `all_imp`, whose
eigenvariable rules shift the entire context. No existential witness is
recovered. The distinct `sigma` constructor has a Π0 body: `hs` forces its
numeric level to zero, and only there the accepted level-zero comparison
and actual HA bounded decision supply the base case. The implementation
uses the already polarity-general `hierarchy_zero_equivalence` and
`hierarchy_zero_decidable` directly, avoiding a redundant Π0-to-Δ0 rewrite.
`all`, `pi`, and `dummy_pi` contradict the polarity; `dummy_sigma`
contradicts the level. These are eliminations of syntactic constructors,
not a rule about arbitrary Π1 truth.

In `ball`, the source positive-bound premise gives the exact `Rew.bShift`
form, and `termAux_bShift` retains every ambient parameter. Positivity here
means absence of source bound slot zero, not a positive natural value.
The literal GG guard is `¬(¬¬L∧¬C)`. Its comparison with `L→¬¬A` needs
neither a decision of `A` nor of `L`. Reclosing, finite bounded DNS gives
`¬¬ball T A`; the actual HA order decision then permits transport between
the ordinary NNF universal guard `∀(¬L∨A)` and `ball T A`. The source
guard is never silently treated as a definitionally equal implication.
`bexs` combines the order-atom and matrix comparisons and uses the same
negative-existential lemma; it does not extract a bounded witness from a
double negation.

The 82-line checks pin the exact existing source existential and bounded-all
GG constructors by `rfl`; exercise arbitrary undecided logical matrices;
build a genuine Σ1 derivation for a bounded universal containing an
unbounded existential and a nested bounded existential with a preceding
witness as bound; separately exercise the Π0 `sigma` introduction; use
sparse term environments containing free slot zero; retain shifted finite
contexts; and permit a literal zero bound over an arbitrary Σ1 matrix.
The existential-control statement explicitly retains the outer double
negation without a whole-existential decision premise.

All eleven axiom reports are standard-only. The six public finite logical
helpers use only `propext` and `Quot.sound`. The three hierarchy endpoints
and two source hierarchy certificates additionally inherit `Classical.choice`
from the source/bounded prerequisites. These are metatheoretic dependencies;
the actual `HA.Derives` calculus has not gained a classical rule. No
`sorry`, `native_decide`, model-soundness oracle, or classical PA proof
conversion was added.

I fully read both source files, the actual source hierarchy/GG constructors,
the relevant accepted quantifier rules, and the entire new replay driver
before execution, then reread the final main and reports. Authentication
traversed the current source imports and selected exactly 104 cached
modules, including 76 Foundation modules, 332 cached artifacts, and 34
explicit external package/toolchain boundaries. All 765 distinct inherited
and explicit pins matched before and after execution; no reused client
imports either new leaf. Original author evidence and both accepted root
parent records are retained. The selected root primaries are:

- `FoundationHADeltaZeroGG` at
  `/tmp/foundation-ha-deltazero-gg-root-peer-y5x43g1v/lib`, object
  `f9f8d84acd4726cfacc6f2c7eb1bad8d1f1666fbb54230421ebb09a774042a3a`;
  root record `95816b89f211437e005f4e7b1de5efe82c765b7e0213a8ec3b3d84e33f481d7e`.
- `HABoundedDoubleNegation` at
  `/tmp/ha-bounded-double-negation-root-peer-z7i5h7h7/lib`, object
  `f0e760efed2f33d6b23e19b83266c479212d7a19cc51b011f8f26c3f4ea14344`;
  root record `289f3ee4d80606920ddaa9b13676db66a5ac70d2cd522165913ba2cd7c852ea3`.

Only the two new leaves were freshly compiled with Lean 4.32.0,
`-M6000 -j1 -DElab.async=false`, new nonsymlink outputs, and the 512MiB
reserve. Final main/check PASS took 2.520s/1.879s; main log is empty.
Private primary: `/tmp/foundation-ha-sigma-one-gg-author-poq3tnz4/lib`.
No Foundation/prerequisite build, shared-object overwrite, or increased
resource limit occurred.

Two earlier main failures remain in the complete attempt bundle. The first
needed explicit formula/context type annotations and unfolding of `neg` in
finite hypothesis membership. The second applied `¬A` to `¬¬A` in the
wrong direction in the guard contradiction; reversing that modus-ponens
application fixed the proof. No theorem statement, definition, or premise
was weakened. Both failures have full source snapshots, commands, inputs,
diagnostics and status; neither checks nor prerequisites failed.

Frozen pins:

- Main source: `0cf75cea58c47a8da8d776d12ac55afae46f59e24029244c49cde55bd3f885fc`.
- Checks source: `b91cf49200ee14c1ad0a4d5137eb048e9bce162fe7d5e202cef3bdad93abcdde`.
- Main object: `63c087fe421399605afebff35e4347a296e957860e29a449880dafd553a8b2b0`.
- Checks object: `f32a3417cda2541e51c5a9f0341e41e62d5c40a23f2e7baf5b5f6c899bf71e2c`.
- [Replay summary](foundation-ha-sigma-one-gg-replay.json): `8f088894926e73715eebbe864b6906016a2b2e94e0a6ee50de060377c1f0e78b`.
- [26-file manifest](foundation-ha-sigma-one-gg-replay/FILES.json): `2155c8aecfcf670bff3653a5bca7c0df159e2b58c34e786d6d26238e0a268a21`.

This packet does not identify ordinary interpretation of source NNF
negation with HA negation of the ordinary source. It supplies no positive
Σ1 DNE, Markov principle, unbounded DNS, independent proof-checker
normalization, fixed consistency specialization, or current-equation HA
equivalence. No frozen source, vendor file, shared document, displayed
equation, or Git state was changed.
