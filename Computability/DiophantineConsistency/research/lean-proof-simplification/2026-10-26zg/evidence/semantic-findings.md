# Semantic proof proposals

Pinned maintained source: `89226e3921bce3e8949fadd12d3efb6914c7630c`.

## A. Quantify over assignments by surjectivity of environment restriction

**Target.** `ObjectPolynomial.lean`, `sat_noZeroForm_iff`, lines 53–72.
The theorem currently builds a total environment from a `Fin n` assignment,
proves an extensional equality, and explicitly transports both the naturalness
guard and the equation along that equality.

The map

    restriction : (Nat -> V) -> (Fin n -> V),  env |-> env o Fin.val

is surjective because `Fin.val` is injective and a default element of `V` is
available. Mathlib already proves exactly this as
`Function.Injective.surjective_comp_right'`. The explicit default `vempty H`
avoids adding an ambient `Nonempty V` argument and also covers `n=0`.
`Function.Surjective.forall` then transports the whole guarded unsolvability
predicate at once. The naturalness hypotheses remain inside that predicate.

Proposed maintained proof after the unchanged statement:

```lean
  refine (seal_valid (mem := mem) _).trans ?_
  change (∀ ee : Nat → V,
    Sat mem ee (inputsNaturalForm (Fin.val : Fin n → Nat)) →
      ¬ Sat mem ee (equationForm e Fin.val)) ↔ NoZeroRel H e
  simp only [inputsNaturalForm_spec H, equationForm_spec H]
  exact (Fin.val_injective.surjective_comp_right'
    (fun _ => vempty H)).forall.symm
```

The patch uses eight physical declaration lines rather than twenty with its
chosen line layout, a 12-line current-snapshot reduction. No new helper is
needed in production. This is a static proposed reduction; the complete
ObjectPolynomial module has not been compiled. The corresponding generic
transport theorem and the guarded-unsolvability specialization are compiled
in `EnvironmentRestriction.lean`.

**Why this remains after prior work.** Earlier packets propose sentence
independence, arity-polymorphic closed-sentence transport, and compositional
normalization of satisfaction specifications. Those may simplify the two
specification rewrites, but they leave the conversion between total
environments and finite assignments. This proposal replaces that conversion
by its existing mathematical API. The independent audit checked a–w and all five
incoming ZIP reports (28 packets through closing snapshot
`7df43cdfacb490cd3ca3acd23e39027efebf8801`) and found no exact prior proposal.

**Boundary.** Injective coordinates are essential. If two free variables share
one environment slot, the restrictions do not range over all assignments. For
example, restriction along the constant map `Fin 2 -> Nat` always satisfies
`v 0=v 1`, although arbitrary `Fin 2 -> Nat` assignments do not. All values are
arbitrary elements of the model carrier; no standard-natural interpretation is
introduced. The checked transport kernels use only the usual axioms
`propext`, `Classical.choice`, and `Quot.sound`; no comparison to the full
upstream theorem's axiom footprint was performed.

## B. Transport integer polynomial identities into split-natural zero semantics

### The actual obstruction

`GatesSemiring.lean`, lines 15–16, defines `Expr.SemiringZero e v` as equality of
the two natural-expression values obtained by `e.splitNatural`. Integer
syntax contains subtraction, while an arbitrary internal-omega carrier is a
semiring, not a ring. Consequently one cannot simply evaluate an integer
polynomial in that carrier by a ring homomorphism from `Int`.

Current `NaturalExpression.eval_splitNatural` concerns external `Nat` values
and an `Int` difference. It does not prove the needed arbitrary-semiring
transport. Two equal integer polynomials can have very different positive and
negative syntax trees. The new theorem relates their zero predicates directly.

### Exact theorem

For arbitrary `Expr σ` expressions `e,f`, an arbitrary commutative semiring `R`
with additive cancellation, and an arbitrary assignment `v : σ -> R`, prove

    e.toPolynomial = f.toPolynomial
      -> (e.splitNatural.1.evalSemiring v = e.splitNatural.2.evalSemiring v
          <-> f.splitNatural.1.evalSemiring v = f.splitNatural.2.evalSemiring v).

The checked Lean assumptions are `[CommSemiring R] [IsCancelAdd R]`. No order,
no characteristic-zero hypothesis on `R`, and no embedding of `R` in a field
are required. In particular the theorem applies to all elements of an
internal omega once its already-existing additive cancellation instance is
available (`ObjectNaturalOrder.lean`, line 145).

### Proof with no semantic ring completion

Write `P_e,N_e` for the two natural-coefficient polynomials corresponding to
`e.splitNatural`, and let `i : Nat[X] -> Int[X]` be coefficient casting.

1. Structural induction gives `i(P_e)-i(N_e)=e.toPolynomial`. The signed
   constant case is `Int.toNat_sub_toNat_neg`; addition, subtraction, and
   multiplication are ring identities.
2. From equality of the integer polynomials,
   `i(P_e)+i(N_f)=i(P_f)+i(N_e)`. Injectivity of coefficient casting gives the
   exact natural-coefficient polynomial identity `P_e+N_f=P_f+N_e`.
3. Evaluate this identity using `MvPolynomial.eval₂Hom (Nat.castRingHom R) v`.
   The result is a subtraction-free semantic equality
   `p_e+n_f=p_f+n_e` in `R`.
4. If `p_e=n_e`, additive cancellation yields `p_f=n_f`; conversely, if
   `p_f=n_f`, cancellation yields `p_e=n_e`.

This preserves nonstandard-model semantics. There is no reduction of an
arbitrary internal natural to a standard numeral.

### Concrete checked client

`ObjectConditional.literal_selection`, lines 12–15, gives the literal
selection residual

    out - (bit*zero + (1-bit)*positive).

Its integer polynomial equals

    (out + bit*positive) - (bit*zero + positive).

The supplied client proves that equality using `ring` and then applies the
new transport law. A short natural-expression simplification yields

    SemiringZero originalRow v
      <-> out + bit*positive = bit*zero + positive.

The artifact checks arbitrary variable indices and also instantiates the
actual sum slots `inl 0`, `inl 4`, `inl 2`, `inl 3` in `Fin 6 + Fin 0`.
The source expression, public polynomial, witness counts, and compiled program
need not change. The normalized expression is only a proof intermediate.

The existing local selection proof is already short. This client is evidence
that the new bridge works at a real source boundary, not a claim that adding a
72-line general theorem file (including comments and audit prints) to save one small lemma is a net source reduction.
Adoption is justified when several row-algebra proofs share the bridge, or
when a more complicated polynomial identity is available but literal
`splitNatural` normalization is unwieldy. The benefit is representation
invariance of zero semantics, separate from any line-saving forecast.

### Cancellation is necessary: checked negative control

The clients file constructs the Boolean OR/AND commutative semiring:
addition is OR, multiplication is AND, zero is false, and one is true.
Integer expressions `e=1` and `f=2-1` have the same integer polynomial.
Nevertheless, `e` splits to `(1,0)`, so its zero predicate is false;
`f` splits to `(2,1)`, and `2=1+1=1` in this semiring, so its zero predicate
is true. The two semantic evaluations are checked by `decide` and have no
axiom dependencies. Thus dropping additive cancellation makes the proposed
transport theorem false; a semiring-only claim would be unsound.

### Novelty and relation to previous packets

Earlier work already covers generic semiring gate semantics, expression
renaming, assignment transport, sparse integer row certificates, and formal
polynomial equality of particular rows. The new law fills the boundary
between *integer polynomial equality* and *split-natural zero semantics in
arbitrary additive-cancellative semirings*. None of those earlier facts alone
permits a signed ring rewrite in the internal-omega interpretation.

### Artifacts and validation

- `PolynomialZeroTransport.lean`: four checked transport theorems built on the
  actual `NatExpr` and `Expr` definitions from the pinned maintained source.
- `PolynomialZeroTransportClients.lean`: exact selection syntax/slot client,
  custom Boolean semiring, and checked failure without cancellation.
- `EnvironmentRestriction.lean`: checked generic environment/assignment bridge.
- `environment-restriction.patch`: proposed upstream ObjectPolynomial edit.
- `candidates/ObjectPolynomial.lean`: the complete candidate module; integration
  is explicitly uncompiled.
- `semantic-validation.json` and `*.final.log`: exact source hashes and final
  compiler outcomes.
- `scripts/replay.py`: portable replay driver for a complete configured
  repository checkout, rebuilding the current lower production dependencies.

Freshly rebuilt production dependencies are `ArithmeticRepresentation`,
`NaturalExpression`, and `NaturalExpressionSemiring`; the supplied current
`Representation.olean` was rebuilt by the parent. Both new polynomial files
pass Lean 4.32.0, and all exported core/client theorem axiom lists are limited
to `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom,
`native_decide`, or evaluation axiom is used. This does not constitute a full
ObjectConditional model-module build or a full repository build.

For production, put the core theorem in a small module importing only
`NaturalExpressionSemiring`. `GatesSemiring` can import it and add the
one-line wrapper below its existing definition:

```lean
theorem semiringZero_iff_of_polynomial_eq [IsCancelAdd R]
    (e f : Expr σ) (h : e.toPolynomial = f.toPolynomial) (v : σ → R) :
    e.SemiringZero v ↔ f.SemiringZero v :=
  splitNatural_zero_iff_of_polynomial_eq e f h v
```

This avoids an import cycle and preserves the existing definition of
`SemiringZero`.
