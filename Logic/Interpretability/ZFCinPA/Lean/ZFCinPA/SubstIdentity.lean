import ZFCinPA.SetPlaceholders

/-!
# Self-substitution of a model-coded leaf at a deeper ambient arity

`ZFCinPA.SetPlaceholders.translateFormula` sends a placeholder atom
`srcP i ts` to `(Ks i).subst (fun j ↦ translateTerm (ts j))`: the compiler
*always* emits a substitution, because the source atom may carry arbitrary
argument terms.  The certificate field codes of `ZFCinPA.CertificateFields`,
by contrast, splice their model-coded leaves (`numChainCode x`,
`closCode x`, …) **raw** into a constructor spine, at whatever ambient arity
the spine has reached.  Reconciling the two therefore needs

> a leaf of arity `m`, substituted by the identity bound-variable vector
> `#0, …, #(m-1)` regarded at a larger ambient arity `n`, is unchanged.

Foundation has this only in the *homogeneous* shape.  At the raw level,
`Bootstrapping.subst_eq_self` demands `IsSemitermVec L n n w` — the same
arity on both sides — and at the typed level
`Bootstrapping.Semiformula.subst_eq_self` demands
`w : SemitermVec V L n n`, with `subst_eq_self₁` the special case `n = 1`
(which is what `ZFCinPA.SeparationKernel` uses: there the single
placeholder is unary and every source atom sits at ambient arity `1`).

## What is actually new here

Nothing at the raw level.  The observation that makes this cheap is that
the heterogeneous hypothesis is *self-improving*: if every entry of `w` is
`^#i` with `i < m`, then each entry is already a semiterm of arity `m`, so
`IsSemitermVec L m m w` holds regardless of the ambient arity the vector
was built at.  `subst_bvarVec_eq_self` therefore reduces to Foundation's
`subst_eq_self` in one step, and no induction is repeated.

What *is* new is the typed statement.  `Semiformula V L m` and
`Semiformula V L n` are different types (the arity is a structure index),
so a genuinely heterogeneous identity cannot be an equation between typed
formulas: it has to be stated on `.val`, or with an explicit arity
weakening.  Both forms are provided:

* `Semiformula.subst_bvarVec_val` — the `.val` form, no coercion at all;
* `Semiformula.castLE` and `Semiformula.subst_castLE_bvar` — the typed
  form, through the (definitionally transparent) arity weakening, which is
  available because `IsSemiformula` is `bv ≤ n` and hence monotone.

The last section specializes to the compiler: `translate_emb_srcP_bvars`
says that a placeholder atom whose arguments are exactly the first
`arities i` bound variables translates, at any ambient arity `n ≥
arities i`, to the raw leaf `Ks i`.  That is the identity the certificate
field spines need.

## Disciplines

No concrete Gödel code is named or evaluated anywhere below; the leaves
are universally quantified `V`-elements throughout, so the parameter
firewall of `ZFCinPA.LevelCodeTower` is respected vacuously.
-/

set_option autoImplicit false

namespace LeanProofs.ZFCinPA.SubstIdentity

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA
open LeanProofs.ZFCinPA.SetPlaceholders

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

/-! ## The raw identity -/

/-- An identity bound-variable vector is a semiterm vector *at its own
length*, whatever ambient arity it was built for.  This is what collapses
the heterogeneous statement to Foundation's homogeneous one. -/
theorem isSemitermVec_of_bvarVec {m w : V} (hw : len w = m)
    (H : ∀ i < m, w.[i] = ^#i) : IsSemitermVec L m m w :=
  IsSemitermVec.iff.mpr ⟨hw, fun i hi ↦ by rw [H i hi]; simpa using hi⟩

/-- **Heterogeneous self-substitution, raw form.**  A semiformula of arity
`m` is unchanged by substitution of the identity bound-variable vector of
length `m`, no matter what ambient arity the vector's entries were meant
to live at.

Foundation's `Bootstrapping.subst_eq_self` is the special case in which
the ambient arity is also `m`; here nothing at all is assumed about the
ambient arity, because the hypothesis `H` already forces every entry to be
a semiterm of arity `m`. -/
theorem subst_bvarVec_eq_self {m w p : V} (hp : IsSemiformula L m p)
    (hw : len w = m) (H : ∀ i < m, w.[i] = ^#i) :
    Bootstrapping.subst L w p = p :=
  Bootstrapping.subst_eq_self hp (isSemitermVec_of_bvarVec hw H) H

/-! ## The typed identity

The typed statement cannot be an equation between typed formulas, because
`Semiformula V L m` and `Semiformula V L n` are distinct types.  It is
therefore stated on the underlying codes. -/

namespace Semiformula

/-- **Heterogeneous self-substitution, typed form.**  The code of
`φ.subst w` — an element of `Semiformula V L n` — is the code of
`φ : Semiformula V L m` itself, whenever `w` is the identity
bound-variable vector. -/
theorem subst_bvarVec_val {m n : ℕ} (φ : Bootstrapping.Semiformula V L m)
    (w : Bootstrapping.SemitermVec V L m n)
    (H : ∀ i : Fin m, (w i).val = ^#((i : ℕ) : V)) :
    (φ.subst w).val = φ.val := by
  rw [Bootstrapping.Semiformula.val_substs]
  refine subst_bvarVec_eq_self φ.isSemiformula (by simp) ?_
  intro i hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  rw [Bootstrapping.SemitermVec.val_nth_eq]
  simpa using H i

/-- The identity bound-variable vector at ambient arity `n`, for a leaf of
arity `m ≤ n`. -/
noncomputable def bvarVec {m n : ℕ} (h : m ≤ n) :
    Bootstrapping.SemitermVec V L m n :=
  fun i ↦ Bootstrapping.Semiterm.bvar (Fin.castLE h i)

@[simp] theorem bvarVec_val {m n : ℕ} (h : m ≤ n) (i : Fin m) :
    ((bvarVec (V := V) (L := L) h) i).val = ^#((i : ℕ) : V) := rfl

/-- Named instance of `subst_bvarVec_val` at the canonical vector. -/
theorem subst_bvarVec {m n : ℕ} (h : m ≤ n)
    (φ : Bootstrapping.Semiformula V L m) :
    (φ.subst (bvarVec h)).val = φ.val :=
  subst_bvarVec_val φ _ fun _ ↦ rfl

/-! ### Arity weakening

`IsSemiformula L n p` is `IsUFormula L p ∧ bv L p ≤ n`, so it is monotone
in `n`; the weakening is the identity on codes. -/

/-- Arity weakening of a typed semiformula: same code, larger declared
arity. -/
noncomputable def castLE {m n : ℕ} (h : m ≤ n)
    (φ : Bootstrapping.Semiformula V L m) : Bootstrapping.Semiformula V L n :=
  ⟨φ.val, ⟨φ.isSemiformula.isUFormula,
    le_trans φ.isSemiformula.bv_le (by exact_mod_cast Nat.cast_le.mpr h)⟩⟩

@[simp] theorem castLE_val {m n : ℕ} (h : m ≤ n)
    (φ : Bootstrapping.Semiformula V L m) : (castLE h φ).val = φ.val := rfl

/-- **Heterogeneous self-substitution, typed equation.**  With the arity
weakening made explicit, the identity becomes a genuine equation of typed
formulas. -/
theorem subst_bvarVec_eq_castLE {m n : ℕ} (h : m ≤ n)
    (φ : Bootstrapping.Semiformula V L m) :
    φ.subst (bvarVec h) = castLE h φ :=
  Bootstrapping.Semiformula.ext (subst_bvarVec h φ)

end Semiformula

/-! ## The compiler-facing corollary

A placeholder atom whose argument list is exactly the first `arities i`
bound variables translates to the raw leaf, at any ambient arity that can
accommodate it. -/

section Compiler

variable {k : ℕ} {arities : Fin k → ℕ}

/-- The source argument list `#0, …, #(arities i - 1)` at ambient arity
`n`. -/
def srcBvars {n : ℕ} (i : Fin k) (h : arities i ≤ n) :
    Fin (arities i) → ClosedSemiterm (setTemplateLanguage k arities) n :=
  fun j ↦ #(Fin.castLE h j)

/-- **The reconciliation identity.**  The `i`-th placeholder applied to the
identity argument list specializes to the *raw* model-coded leaf `Ks i`,
spliced at ambient arity `n`. -/
theorem translate_emb_srcP_bvars {n : ℕ}
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (i : Fin k) (h : arities i ≤ n) :
    (translateFormula Ks
        (Rewriting.emb (srcP i (srcBvars i h)) :
          Semiproposition (setTemplateLanguage k arities) n)).val =
      (Ks i).val := by
  rw [translate_emb_srcP]
  refine Semiformula.subst_bvarVec_val (Ks i) _ ?_
  intro j
  rfl

/-- Typed form of the reconciliation identity. -/
theorem translate_emb_srcP_bvars_eq {n : ℕ}
    (Ks : (i : Fin k) → Bootstrapping.Semiformula V ℒₛₑₜ (arities i))
    (i : Fin k) (h : arities i ≤ n) :
    (translateFormula Ks
        (Rewriting.emb (srcP i (srcBvars i h)) :
          Semiproposition (setTemplateLanguage k arities) n)) =
      Semiformula.castLE h (Ks i) :=
  Bootstrapping.Semiformula.ext (translate_emb_srcP_bvars Ks i h)

end Compiler

end LeanProofs.ZFCinPA.SubstIdentity
