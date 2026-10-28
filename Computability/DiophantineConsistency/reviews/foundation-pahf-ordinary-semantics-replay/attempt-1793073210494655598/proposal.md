# Ordinary predicate: closed syntax and standard-natural semantics

This read-only proposal follows the accepted fixed consistency normalization.
It separates a generic syntax/semantics packet from its fixed specialization
and from an optional conditional current-equation proof composition. No Lean
implementation or compiler execution is part of this proposal.

## Smallest generic packet

Suggested new leaf: `FoundationPAHFOrdinarySemantics.lean` plus focused checks,
importing only the already accepted `FoundationHADeltaZero` and
`FoundationPAHFNatSemantics`. Its new content is the missing support and
ordinary interpretation proofs. It neither redefines the eight-constructor
`ordinaryAux` nor proves any new HA derivability or checker equivalence.

Existing definitions and reuse points:

* `FoundationPAHFSyntax.lean:20–49`: `termAux`, `liftBound`, `liftFree`,
  `ltFormula`, and intuitionistic `formulaAux`.
* `FoundationHADeltaZero.lean:21–31`: actual ordinary NNF interpretation.
* `PAHF/PASyntax.lean:206–219,482–502`: term/formula `Free` and
  `Formula.Sentence`. A quantifier changes `Free k` to `Free (k+1)` in its
  body. Formula `bound` does not decrease at binders and is not a substitute
  for a free-variable certificate.
* `FoundationPAHFNatSemantics.lean:23–68`: `eval_termAux`,
  `sat_ltFormula`, `eval_liftBound`, `eval_liftFree`.
* `PAHF/PASyntax.lean:617`: `Formula.Sat_ext_free` gives valuation
  independence once syntactic closedness is proved, for any `PreModel`.

These were read in their actual source ranges. The existing
`ArithmeticExpression.free_term` is specific to its polynomial compiler;
it is not a support theorem for arbitrary Foundation `termAux` environments.
No reusable `ordinaryAux` free-support lemma was found in the selected
sources.

### Support signatures

The following are proposed signatures, not checked declarations. Write
`PTerm = SetTheory.PA.Term`, `F = SetTheory.PA.Formula` and use the already
defined `ordinaryAux` and `ltFormula`:

```lean
theorem free_rename_succ (t : PTerm) (k : Nat) :
  PTerm.Free (k+1) (PTerm.rename Nat.succ t) ↔ PTerm.Free k t

theorem free_termAux {ξ : Type*} {n : Nat}
    (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (t : Semiterm ℒₒᵣ ξ n) (k : Nat)
    (h : PTerm.Free k (termAux bv fv t)) :
  (∃ i, PTerm.Free k (bv i)) ∨ ∃ x, PTerm.Free k (fv x)

theorem free_ltFormula (s t : PTerm) (k : Nat) :
  F.Free k (ltFormula s t) ↔ PTerm.Free k s ∨ PTerm.Free k t

theorem free_ordinaryAux {ξ : Type*} {n : Nat}
    (bv : Fin n → PTerm) (fv : ξ → PTerm)
    (p : Semiformula ℒₒᵣ ξ n) (k : Nat)
    (h : F.Free k (ordinaryAux bv fv p)) :
  (∃ i, PTerm.Free k (bv i)) ∨ ∃ x, PTerm.Free k (fv x)

theorem ordinary_sentence (p : ArithmeticSentence) :
  F.Sentence (ordinaryAux Fin.elim0 Empty.elim p)
```

`free_termAux` is deliberately a one-way support bound: it does not assert
that every supplied environment entry occurs in the source term. Its proof
is structural term induction. `free_rename_succ` is structural PAHF term
induction. The `ltFormula` result unfolds its witness binder: an outside
index `k` becomes `k+1`, so the fresh witness at slot zero cannot be a free
outside variable. The two shifted operand terms give exactly the displayed
support union.

For `free_ordinaryAux`, all eight actual NNF cases are handled. In each
quantifier case, the body hypothesis is at index `k+1`; `Fin.cases` splits
the lifted bound environment. Its new slot zero is impossible, and its
old slots plus all lifted free parameters reduce using `free_rename_succ`.
This retains nested binders, arbitrary source variables and arbitrary PAHF
term parameters. At `n=0, ξ=Empty`, both possible supports are empty,
giving the actual PAHF `Formula.Sentence` predicate.

An immediate generic corollary is valuation independence in every PAHF
`PreModel`, using `Sat_ext_free`; no arithmetic, induction or standardness
assumption is needed for this syntactic result.

### Ordinary standard-Nat semantics

The main proposed semantics theorem is:

```lean
theorem sat_ordinaryAux {ξ : Type*} {n : Nat}
    (p : Semiformula ℒₒᵣ ξ n)
    (bv : Fin n → PTerm) (fv : ξ → PTerm) (ee : Nat → Nat) :
  F.Sat FoundationPAHFNatSemantics.natStructure ee
      (ordinaryAux bv fv p) ↔
    p.Eval (fun i => PTerm.eval natStructure ee (bv i))
      (fun x => PTerm.eval natStructure ee (fv x))

theorem sat_ordinary_sentence (p : ArithmeticSentence) (ee : Nat → Nat) :
  F.Sat natStructure ee (ordinaryAux Fin.elim0 Empty.elim p) ↔
    p.Evalb (M := Nat) ![]
```

The proof is the actual eight-constructor source induction. Atomic equality
uses `eval_termAux`; order uses `sat_ltFormula`; negative atoms use the
same equivalences under negation. Ordinary conjunction and disjunction use
their direct semantic constructors. Universal/existential cases use
`eval_liftBound` and `eval_liftFree`, retaining the old parameter valuation.
This does not duplicate the GG translation or use HA proofs as semantic
oracles. Unlike `sat_formulaAux_GG`, ordinary disjunction and existential
interpretation need no double-negation elimination step.

Estimated size: 120–180 main lines, 45–65 focused check lines. If the support
proof alone grows substantially, it can be frozen separately, but the two
parts are coherent and share the exact literal interpretation. Suggested
checks cover ordinary negated equality/order atoms, the order witness's
fresh slot, nested `all/ex` with a sparse free parameter, empty source
environments and valuation independence. Do not test a stronger false
claim that arbitrary open environments are closed.

## Fixed specialization

After the generic packet is frozen, a small
`FoundationHAConsistencySemantics.lean` plus checks can import it and the
accepted `FoundationHAConsistencyNormalization`. This retains the selected
fixed definitions verbatim: `rho`, `ordinaryRefutation`,
`ordinaryConsistency`, and `FoundationZFCConsistencyNat.sourceSentence`.

Direct applications give `Formula.Sentence ordinaryRefutation` and
`Formula.Sentence ordinaryConsistency`; the latter follows because HA
negation is implication to falsity. Their arbitrary-structure valuation
independence follows from the support certificate, not from standard-Nat
truth or a claim that models have only standard witnesses.

The exact standard-natural binding is:

```lean
F.Sat natStructure ee ordinaryRefutation ↔ rho.Evalb (M := Nat) ![]

F.Sat natStructure ee ordinaryConsistency ↔
  ¬ _root_.SetTheory.BProv LeanProofs.BoundedZFCConsistency.ZFCax_s []
    _root_.SetTheory.Form.fBot
```

Proof: use `sat_ordinary_sentence`, the definition of the outer HA negation,
the accepted literal `source_eq_neg_rho`, the Foundation semantic negation
law (`Semiformula.EvalAux_neg` and the logical homomorphism's `map_neg`,
Foundation `FirstOrder/Basic/Semantics/Semantics.lean:222–239`), and the
accepted `source_nat_iff_no_refutation`. No whole checker is
unfolded or reimplemented. A positive standard-Nat comparison
`Sat ... ordinaryRefutation ↔ BProv ... fBot` is also possible from the
same negative equivalence by classical `not_not` in the Lean metatheory.
If included, its classical nature must be explicit; it is not positive
Σ₁ DNE in the HA calculus. The negative consistency binding itself is the
primary target.

The explicit external proposition is exactly the body of
`DiophantineConsistency.ConZFC` at `Bridge.lean:11`:

```lean
def ConZFC : Prop := ¬ BProv ZFCax_s [] Form.fBot
```

That definition imports `Computability` and the broad `BusyBeaver.ZFC.KEndpoint`.
`Bridge` is not in the authenticated Foundation import union. The smallest
packet should therefore use the same fully qualified BProv proposition
already used by `FoundationZFCConsistencyNat`, and record the exact external
definition body. It must not silently add a broad `Bridge` import or claim
that a theorem mentioning that constant has already been compiled. A future
wide adapter can restate this as `↔ ConZFC` if its mixed import environment
is separately authenticated. No definition relocation is proposed here.

This fixed semantic step uses the already accepted actual C254-to-refutation
standard-convention theorem. It neither gives an HA proof comparing the
positive Foundation predicate with independent BProv/C222/C254 syntax nor
supplies a current-equation PA calibration.

## Optional cheap conditional current proof composition

There is a useful but explicitly conditional actual-HA composition:

```lean
theorem current_iff_ordinary
    (h : Peano ⊢ FoundationHACurrentNoZero2011.classicalSentence 🡘
      FoundationZFCConsistencyNat.sourceSentence) :
  HA.Proves (.and
    (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence
      FoundationHAConsistencyNormalization.ordinaryConsistency)
    (.imp FoundationHAConsistencyNormalization.ordinaryConsistency
      ArithmeticCurrentEquation2011.unsolvabilitySentence))
```

Apply the existing `FoundationHACurrentTransfer.current_iff_translated h`,
then compose its first direction with `gg_to_ordinary` and the reverse with
`ordinary_to_gg`. This is about 8–12 lines and introduces no new assumptions
beyond the displayed missing PA proof. Its sources are already imported by
Normalization. It is optional and does **not** advance the missing PA
arithmetic/machine equivalence by itself. Do not assert that `h` exists or
erase it from the reported scope.

## Dependency and execution boundary

The accompanying read-only pin record reauthenticates the accepted
Normalization peer as the selected primary:

`/tmp/ha-consistency-normalization-independent-zqsk9jr1/lib/DiophantineConsistency/FoundationHAConsistencyNormalization.olean`

SHA256 `69f6eb621b3ecaa9ae50c145af9c9020880c7c388cd043246b3a371c7bc1c8bc`.
The root-author provider and accepted Σ₁ root provider remain in provenance.

Exact source-import traversals give:

| Proposed import scope | Cached modules | Foundation | Cached artifacts | External boundaries |
| --- | ---: | ---: | ---: | ---: |
| Support alone (`FoundationHADeltaZero`) | 102 | 76 | 330 | 34 |
| Generic support + ordinary Nat semantics | 108 | 76 | 336 | 41 |
| Existing fixed Normalization closure, including its fresh main | 456 | 139 | 873 | 57 |

The later fixed supplement would add the one new generic main to the last
row: 457 cached modules and 874 artifacts before its own two fresh leaves.
No new Foundation module or external package boundary is required. The
optional conditional composition alone needs the existing 456-module union.
The actual subsets and dependency order are stored in the pin record;
there are no missing providers and no cached module imports a proposed new
leaf. Only selected sources/objects and explicit accepted package boundaries
are authenticated, not a new compiler replay of the whole closure.

No source implementation, Lean invocation, dependency build, cache copy,
vendor change, shared-document edit, or Git action has occurred in this
audit. A later authorized implementation should read all new source and
driver bytes, reauthenticate before/after, compile only its two leaves in
a new private overlay under Lean 4.32.0 `-M6000 -j1 -DElab.async=false`, and
retain the 512MiB disk reserve and every failed attempt.
