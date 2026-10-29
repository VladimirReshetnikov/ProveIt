# Concrete first-order PRA design (read-only, 2026-10-29)

This is a proposed implementation interface, not an implemented theory or a
conservation proof. No Lean source, compiler overlay, build, or Git mutation was
made. Foundation contracts below were checked against source commit
`32e1a0956a8622fad067328ca1959729a7634428`; Mathlib's inspected source is at
`81a5d257c8e410db227a6665ed08f64fea08e997`. This complements the separate
`pra-conservation-source-audit-20261029.md` and does not change ROOT's plan or
the controller's current Π₂ classification packet.

## 1. Arity-safe codes, with no semantic quotient

Use a new inductive family in `Type`, schematically:

```lean
inductive PRCode : ℕ → Type
  | zero (n : ℕ) : PRCode n
  | succ : PRCode 1
  | proj {n : ℕ} (i : Fin n) : PRCode n
  | comp {m n : ℕ} (f : PRCode m) (g : Fin m → PRCode n) : PRCode n
  | prec {n : ℕ} (f : PRCode n) (g : PRCode (n + 2)) : PRCode (n + 1)
```

All displayed Lean is design-level syntax, not a compiler-checked declaration.
The recursor's argument convention is fixed throughout:

```
eval (prec f g) (0,xs)     = eval f xs
eval (prec f g) (r+1,xs)   = eval g (r,eval (prec f g) (r,xs),xs).
```

Define `eval : PRCode n → (Fin n → ℕ) → ℕ` by structural recursion on the
code, using ordinary natural recursion for the last clause. Composition has
finitely many subcodes. If nested-family deriving support is awkward, a mutual
finite code-vector datatype may replace the `Fin m → PRCode n` field without
changing these interfaces or equations. No minimization constructor is allowed.

Prove decidable syntactic equality and an explicit finite-tree encoding with
arity-checked decoding and a roundtrip theorem. Function symbols are codes,
not equivalence classes under equality of their natural-number evaluations.
Extensional equality of two represented functions is a theorem to prove, never
an automatic new object-theory axiom.

The exact Mathlib comparison API is already available:

```lean
Nat.Primrec' : (List.Vector ℕ n → ℕ) → Prop
Nat.Primrec'.prim_iff : Nat.Primrec' f ↔ Primrec f
```

Its constructors are zero, successor, projection, composition and primitive
recursion with the same counter/result/parameters convention. Induction on
codes proves

```lean
code_primrec (c : PRCode n) :
  Primrec (fun v : List.Vector ℕ n => eval c v.get)
```

Induction on `Nat.Primrec'` proves the converse existence theorem:

```lean
primrec_has_code (hf : Primrec f) :
  ∃ c : PRCode n, ∀ v : List.Vector ℕ n, eval c v.get = f v
```

This target is a proposition, so it does not illegally eliminate a `Primrec`
proof from `Prop` into code data in `Type`. Individual useful codes should be
defined explicitly. A computable constructor from an external syntactic PR
description is separate from a choice-defined witness of this existence result.
There must be **no claim that the evaluator is jointly primitive recursive in
an arbitrary code and its input**; the required result is for each fixed code.

## 2. The language and the old-language embedding

Foundation already has:

```lean
structure Language where
  Func : ℕ → Type
  Rel  : ℕ → Type
structure Language.Hom (L₁ L₂ : Language) where
  func : {k : ℕ} → L₁.Func k → L₂.Func k
  rel  : {k : ℕ} → L₁.Rel k → L₂.Rel k
```

Choose `LPR.Func := PRCode` and `LPR.Rel := Language.ORing.Rel`. Thus equality
and strict order remain the two existing binary relation symbols. Designate
zero, one, addition and multiplication codes to provide `Language.ORing LPR`.
Then the **existing** `Language.ORing.embedding LPR : ℒₒᵣ →ᵥ LPR` is the literal
arity-preserving symbol map; it is not a semantic interpretation of an arbitrary
function symbol by a formula.

Useful explicit derived codes, with `π_i` denoting a projection, are:

* `one_n := comp succ [zero n]`.
* `addCore := prec π_0 (comp succ [π_1])`, so `addCore(r,x)=x+r`.
  Define `add(x,y):=addCore(y,x)` by a composition with swapped projections.
* `mulCore := prec (zero 1) (comp add [π_1,π_2])`, so
  `mulCore(r,x)=x*r`; again swap to obtain `mul(x,y)`.
* `pred := prec (zero 0) π_0`.
* `subCore := prec π_0 (comp pred [π_1])`, then swap to obtain `sub(x,y)=x−y`.
* `nonzero := prec (zero 0) one_2` and
  `ltBit(x,y) := nonzero(sub(y,x))`.

Prove each evaluation identity. In particular `add(x,one_0)=succ(x)` follows
from the defining composition/recursion equations without using induction:
the recursion counter is the second addition argument. This is deliberate,
because Foundation's induction syntax writes the successor as `x+1`.

Do not introduce a second independent addition/multiplication with no bridge.
The constants and operators in the embedded current sentence must be these
same designated codes. Large coefficients remain ordinary finite terms.

## 3. Object-theory axioms, explicitly delimited

Define an inductive predicate `DefAxiom : Sentence LPR → Prop`, consisting of
the universal closures of the following equations, for every well-typed code:

| Code constructor | Defining equations |
|---|---|
| `zero n` | `zero_n(xs)=zero_0` |
| `proj i` | `proj_i(xs)=x_i` |
| `comp f g` | `comp(f,g)(xs)=f(g_0(xs),…,g_(m−1)(xs))` |
| `prec f g` | `prec(f,g)(0,xs)=f(xs)` |
| `prec f g` | `prec(f,g)(succ(r),xs)=g(r,prec(f,g)(r,xs),xs)` |

Successor itself has the two usual basic axioms `succ(x)≠0` and
`succ(x)=succ(y) → x=y`. Add the universal defining biconditional
`x<y ↔ ltBit(x,y)=one_0`.

**Full equality is mandatory.** Include Foundation's existing `𝗘𝗤 LPR`, not
just the image of `𝗘𝗤 ℒₒᵣ`. `Theory.eqAxiom` contains reflexivity, symmetry,
transitivity, and `Eq.funcExt f` / `Eq.relExt r` for every symbol of its language.
The mapped old axioms would omit congruence for almost all PR function symbols.

Finally include quantifier-free induction with arbitrary finite parameters:

```lean
Arithmetic.InductionScheme LPR Semiformula.Open
```

Exact existing definitions in `Arithmetic/Schemata.lean` are

```lean
succInd (φ : Semiformula L ξ 1) :=
  “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”
InductionScheme L Γ :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = .univCl (succInd φ) }
```

`Semiformula.Open` is exactly `qr = 0`; no bounded or unbounded quantifier is
silently admitted in the induction formula. `.univCl` closes its finite free
parameter support. `PRA` is the union of these explicitly listed axiom sets.
This is a definition of an **object theory**, not a Lean `axiom` declaration.
No truth oracle, all-IΣ₁ consequences, conservation axiom, or desired current
equivalence is included.

The standard predecessor/exhaustion property need not be a new axiom: induction
on the open formula `x=0 ∨ succ(pred(x))=x` gives it, using the recursion equation
for `pred`. Basic semiring/order facts can likewise be derived. If later work
adds mapped PA-minus axioms for convenience, their derivability in this initial
presentation must first be proved; they should not silently enlarge PRA.

This is first-order PRA with quantifier-free induction, a usual presentation.
Its induction **axioms themselves are not syntactically universal sentences**.
To apply a Herbrand result requiring a universal axiom set, separately prove
an equivalent universal presentation using PR bounded-counterexample/search
symbols. Calling the current axiom union universal would be incorrect.

## 4. Proof, semantics and syntactic transport interfaces

Reuse `Theory.Proof`, whose fields are an actual finite axiom list, membership
proofs, and an LK derivation. Consequently the intended formal target is
`PRA ⊢ Semiformula.lMap (Language.ORing.embedding LPR) currentIff`.

Foundation already supplies `Semiformula.lMap`, `Theory.lMap`,
`Derivation.lMap`, and rewriting laws `lMap_subst`, `lMap_free`, `lMap_shift`,
`lMap_allClosure`. A theory-proof language-map lemma follows by mapping the
finite axiom list and its derivation; it concludes provability in the **image
of the original theory**. In particular, mapping an IΣ₁ proof gives a proof in
mapped IΣ₁, not in PRA. Inclusion/conservation is not a property of `lMap`.

Define `Structure LPR ℕ` with function interpretation `eval` and the usual
equality/order relations. Verify every defining axiom and quantifier-free
induction. Prove the ordered-ring reduct equals the existing natural structure;
then `Semiformula.eval_lMap` proves exact evaluation preservation for the
current equation and consistency formulas. This standard-model check validates
the language/theory design, not Parsons' theorem.

For a later compatibility theorem, each fixed code can also be represented in
an arbitrary IΣ₁ model using the existing `PR.Blueprint`/`PR.Construction` API.
One must prove totality, uniqueness and code equations, then translate each
fixed open expanded-language formula to a Δ₁ predicate and justify induction.
This supports the direction that IΣ₁ can interpret PRA. It does not establish
the reverse Π₂ conservation direction.

`Language.Encodable` requires an encoding for each arity. It does not by itself
give `Language.LORDefinable` or `PRA.Δ₁`. If a numeric proof predicate is wanted,
provide a PR raw-code/arity validator and an effective axiom recognizer, or
explicit axiom-witness codes with a PR verification relation and a proved
equivalence to this theory. Those are further proof obligations, not inferred
from countability. No uniform PR evaluation oracle is needed to check defining
axiom syntax.

## 5. Small checkpoints and remaining boundary

Suggested first coherent checkpoint: `PRCode` plus evaluation, the fixed-code
`Primrec` theorem, completeness relative to `Nat.Primrec'`, explicit derived
arithmetic codes, and encoding roundtrip. The second checkpoint defines `LPR`,
all axiom families, standard-model validity, exact `ORing.embedding`, and the
successor/add-one and predecessor lemmas. Neither claims conservation.

The intended narrow imports are `Mathlib.Computability.Primrec.List` for the
code comparison, `Foundation.Syntax.Predicate.Language` for the language, and
`Foundation.FirstOrder.Basic.Eq` plus
`Foundation.FirstOrder.Arithmetic.Schemata` for the existing first-order
calculus/equality/induction interfaces. This is a source-level import proposal,
**not** an authenticated cache inventory or authorization to rebuild Foundation.
An implementation can live in owned project modules with a PRA namespace;
vendored Foundation edits are unnecessary to test the design.

Still required for the final objective: a genuine theorem converting suitable
IΣ₁ proofs to PRA proofs, or separately PRA-certified primitive-recursive
refutation/zero witness transforms. The already-existing cut elimination
theorem leaves negated induction axioms in the sequent. The proposed theory
does not erase that arithmetic proof obligation.

## Inspected source pins

All Foundation paths below are relative to its pinned checkout. The files'
bytes were compared against the pinned commit. This is not a compiled-object
authentication claim.

| File | SHA-256 |
|---|---|
| Syntax/Predicate/Language.lean | b5ef82f9c7198f984d2bfc2a765d67e2f815a6d7d65c1b66eebb3373789b676e |
| FirstOrder/Basic/Eq.lean | f1a53113cb76030f89a78579f822dcfab1e53dccb1b8ede7caf8287630ab63d6 |
| FirstOrder/Basic/Calculus.lean | 03ede19d7a450f4f9f8d6925406c6e6509768ebdea4179fa70418436d47fe08a |
| FirstOrder/Basic/Syntax/Formula.lean | 5cbd864cc34c4b18824757fb2112f9b21f6281b53f6ee434ff326214b2e2b341 |
| FirstOrder/Basic/Syntax/Rew.lean | da568bf2186fd0bb590e794475b7cef3aaef03404b1e27184eccb176bcfab6f5 |
| FirstOrder/Basic/Semantics/Semantics.lean | e7a9b583c6189a35ea161b726db67f87ca79343bbfcb523d5f2409f04a32f113 |
| FirstOrder/Arithmetic/Schemata.lean | 5b1a1d84b71c3f943a0867c14d3b0c8c381062ec742d984fefdacf9f2209a6fd |
| FirstOrder/Arithmetic/HFS/PRF.lean | 5925b829137d35293fa00955e81a584857e49a3db94baff1810b44bd05c7beeb |
| Mathlib/Computability/Primrec/List.lean | ebbd09c0a09c3969b7a62f3c013274751c70d4ab23cc8901bc28ba4a69c7b881 |
