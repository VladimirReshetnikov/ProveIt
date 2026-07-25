import ZFCinPA.Instances
import ZFCinPA.SchemaClosure

/-!
# `Δ₁`-definability of the separation schema of `𝗭𝗙`

`Axiom.separationSchema φ` is the universal closure of the fixed skeleton

```
∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ φ(z)
```

with the one-variable instance `φ` plugged in at a single spot.  At the level
of Gödel codes the skeleton is a fixed constructor chain: two constant `∈`-atom
codes, one internal substitution of the core code by the constant vector
`![#0]`, and the connectives `iff`/`⋏`/`^∀`/`^∃`.  This module

* fixes the constants and defines the code-level body `sepBodyVal`,
* proves that it computes the quoted body on quoted cores, with an extractable
  `𝚺₁`-graph valid in every model of `𝗜𝚺₁`,
* assembles the `Δ₁` recognizer `sepCh` for the schema through the generic
  closure recognizer of `ZFCinPA.SchemaClosure`.
-/

namespace LeanProofs.ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory

/-! ## The separation skeleton -/

/-- The (open) body of the separation axiom for the instance `φ`:
`∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ φ(z)`. -/
def sepBodyMeta (φ : SetTheorySemiproposition 1) : SetTheoryProposition :=
  “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

/-- `Axiom.separationSchema` is the universal closure of `sepBodyMeta`. -/
lemma separationSchema_eq_univCl (φ : SetTheorySemiproposition 1) :
    Axiom.separationSchema φ = FirstOrder.Semiformula.univCl (sepBodyMeta φ) := rfl

/-- The atom `z ∈ y` of the skeleton (level 3; `z = #0`, `y = #1`). -/
def sepAtomZY : SetTheorySemiproposition 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- The atom `z ∈ x` of the skeleton (level 3; `z = #0`, `x = #2`). -/
def sepAtomZX : SetTheorySemiproposition 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]

/-- The separation body, resolved to its de Bruijn normal form. -/
lemma sepBodyMeta_eq (φ : SetTheorySemiproposition 1) :
    sepBodyMeta φ
      = ∀⁰ ∃⁰ ∀⁰ (sepAtomZY 🡘 (sepAtomZX ⋏ (φ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 3)]))) := by
  simp [sepBodyMeta, sepAtomZY, sepAtomZX, LogicalConnective.iff,
    FirstOrder.Semiformula.Operator.mem_def]

/-! ## Typed and raw code-level bodies -/

section body

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The typed Gödel code of the separation body, built from the typed core code
`K = ⌜φ⌝` purely with the existing typed constructors. -/
noncomputable def sepBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    Bootstrapping.Semiformula V ℒₛₑₜ 0 :=
  ∀⁰ ∃⁰ ∀⁰ ((⌜sepAtomZY⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)
    🡘 ((⌜sepAtomZX⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)
        ⋏ K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝]))

/-- `sepBody ⌜φ⌝ = ⌜sepBodyMeta φ⌝`: the typed reconstruction matches the code. -/
lemma sepBody_quote (φ : SetTheorySemiproposition 1) :
    (⌜sepBodyMeta φ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 0) = sepBody ⌜φ⌝ := by
  rw [sepBodyMeta_eq]
  unfold sepBody
  simp [Matrix.constant_eq_singleton]

end body

/-! ## Code constants of the skeleton -/

/-- Standard `ℕ`-code of the atom `z ∈ y`. -/
noncomputable def sepAtomZYCode : ℕ := ⌜sepAtomZY⌝

/-- Standard `ℕ`-code of the atom `z ∈ x`. -/
noncomputable def sepAtomZXCode : ℕ := ⌜sepAtomZX⌝

/-- Standard `ℕ`-code of the substitution vector `![#0]` plugging the core into
the skeleton. -/
noncomputable def sepSubstConst : ℕ :=
  Matrix.vecToNat fun i : Fin 1 ↦ Encodable.encode ((![(#0 : SyntacticSemiterm ℒₛₑₜ 3)]) i)

section bodyVal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma val_sepAtomZY :
    ((⌜sepAtomZY⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)).val = ((sepAtomZYCode : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote sepAtomZY).symm

lemma val_sepAtomZX :
    ((⌜sepAtomZX⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)).val = ((sepAtomZXCode : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote sepAtomZX).symm

lemma val_sepSubstConst :
    ((sepSubstConst : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝] : Bootstrapping.SemitermVec V ℒₛₑₜ 1 3) := by
  rw [sepSubstConst, ← Semiterm.quote_eq_encode' (V := V) (![(#0 : SyntacticSemiterm ℒₛₑₜ 3)])]
  congr 1; funext i; simp [Matrix.cons_val_fin_one]

/-- The raw `V → V` separation body: a composition of the `𝚺₁`-definable
internal operations `subst`, `iff`, `^⋏`, `^∀`, `^∃` and the skeleton
constants. -/
noncomputable def sepBodyVal (k : V) : V :=
  ^∀ ^∃ ^∀ (Bootstrapping.iff ℒₛₑₜ ((sepAtomZYCode : ℕ) : V)
    (((sepAtomZXCode : ℕ) : V) ^⋏ Bootstrapping.subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) k))

/-- `sepBodyVal K.val = (sepBody K).val`: the raw function computes the typed body. -/
lemma sepBodyVal_eq (K : Bootstrapping.Semiformula V ℒₛₑₜ 1) :
    sepBodyVal K.val = (sepBody K).val := by
  simp only [sepBodyVal, sepBody, Bootstrapping.Semiformula.val_iff,
    Bootstrapping.Semiformula.val_and, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_substs,
    val_sepAtomZY, val_sepAtomZX, val_sepSubstConst]

/-- `sepBodyVal ⌜γ⌝ = ⌜sepBodyMeta γ⌝` over `ℕ`. -/
lemma sepBodyVal_quote (γ : SetTheorySemiproposition 1) :
    sepBodyVal (⌜γ⌝ : ℕ) = (⌜sepBodyMeta γ⌝ : ℕ) := by
  rw [show (⌜γ⌝ : ℕ) = (⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 1).val from rfl,
    sepBodyVal_eq, ← sepBody_quote]
  rfl

/-- The substituted core sits inside the separation body. -/
lemma subst_le_sepBodyVal (k : V) :
    Bootstrapping.subst ℒₛₑₜ ((sepSubstConst : ℕ) : V) k ≤ sepBodyVal k := by
  unfold sepBodyVal Bootstrapping.iff Bootstrapping.imp
  exact le_of_lt <| lt_trans (lt_K!_right _ _) <| lt_trans (lt_or_right _ _)
    <| lt_trans (lt_K!_left _ _) <| lt_trans (lt_forall _) <| lt_trans (lt_exists _) (lt_forall _)

end bodyVal

/-! ## The identity substitution on codes

Substituting `![#0]` into a one-variable core is a `castLE` at the meta level,
so it fixes the raw Gödel code.  This gives the code-monotonicity of
`sepBodyVal` on quotes, needed to witness the bounded core quantifier of the
recognizer. -/

lemma sep_subst_bvar_eq_castLE (γ : SetTheorySemiproposition 1) :
    (γ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 3)])
      = (Rew.castLE (by omega) ▹ γ : SetTheorySemiproposition 3) := by
  apply FirstOrder.Semiformula.rew_eq_of_funEqOn
  · intro x
    simp
  · intro x _
    simp

lemma sep_subst_quote (γ : SetTheorySemiproposition 1) :
    Bootstrapping.subst ℒₛₑₜ sepSubstConst (⌜γ⌝ : ℕ) = (⌜γ⌝ : ℕ) := by
  have hv := val_sepSubstConst (V := ℕ)
  simp only [natCast_nat] at hv
  rw [hv,
    show (⌜γ⌝ : ℕ) = (⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 1).val from rfl,
    show Bootstrapping.subst ℒₛₑₜ
        (Bootstrapping.SemitermVec.val
          (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝] : Bootstrapping.SemitermVec ℕ ℒₛₑₜ 1 3))
        (⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 1).val
      = ((⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 1).subst
          ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝]).val from rfl]
  have : ((⌜γ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 1).subst
      ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝])
      = (⌜(γ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 3)])⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 3) := by
    simp [Matrix.constant_eq_singleton]
  rw [this, ← FirstOrder.Semiformula.quote_def, sep_subst_bvar_eq_castLE γ,
    FirstOrder.Semiformula.quote_castLE (V := ℕ) γ (by omega)]
  rfl

/-- Code-monotonicity of `sepBodyVal` on quotes, in `ℕ`'s standard order. -/
lemma le_sepBodyVal_quote (γ : SetTheorySemiproposition 1) :
    (⌜γ⌝ : ℕ) ≤ sepBodyVal (⌜γ⌝ : ℕ) := by
  have h := subst_le_sepBodyVal (V := ℕ) (⌜γ⌝ : ℕ)
  simp only [natCast_nat] at h
  rw [sep_subst_quote γ] at h
  rcases le_def.mp h with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt h

/-! ## A concrete `𝚺₁`-graph for `sepBodyVal` -/

section graph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Concrete `𝚺₁`-graph of `sepBodyVal`: a chain of the `subst`/`^⋏`/`iff`/
`^∀`/`^∃` graphs over the skeleton constants. -/
noncomputable def sepBodyValGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s ↑sepSubstConst k ∧
    ∃ c, !qqAndDef c ↑sepAtomZXCode s ∧
    ∃ e, !(Bootstrapping.iffGraph ℒₛₑₜ) e ↑sepAtomZYCode c ∧
    ∃ a1, !qqAllDef a1 e ∧
    ∃ e1, !qqExsDef e1 a1 ∧
    !qqAllDef y e1”

instance sepBodyVal.defined : 𝚺₁-Function₁ (sepBodyVal : V → V) via sepBodyValGraph := .mk fun v ↦ by
  simp [sepBodyValGraph, sepBodyVal, numeral_eq_natCast]

end graph

/-! ## The `Δ₁` recognizer for the separation schema -/

/-- Concrete `𝚫₁.Semisentence 1` recognizer for the separation schema. -/
noncomputable def sepCh : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₛₑₜ) b b ∧ !(Bootstrapping.bvGraph ℒₛₑₜ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).sigma 1 K ∧ !sepBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₛₑₜ) y b → y = b) ∧ (∀ y, !(Bootstrapping.bvGraph ℒₛₑₜ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).pi 1 K ∧ ∀ ib, !sepBodyValGraph ib K → s = ib”)

section recognizer

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The separation-schema recognizer as a predicate. -/
abbrev SepR : V → Prop := SchemaRecognizer ℒₛₑₜ 1 sepBodyVal

instance SepR.defined : 𝚫₁-Predicate[V] (SepR : V → Prop) via sepCh := .mk <| by
  constructor
  · intro v
    simp [sepCh, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [sepCh, HierarchySymbol.Semiformula.val_sigma, SchemaRecognizer,
      lt_succ_iff_le, eq_comm, Nat.cast_one]

end recognizer

/-! ## `Δ₁` of the separation schema -/

/-- The separation instances of `𝗭𝗙`, as a stand-alone theory. -/
def separationTheory : SetTheory := Set.range Axiom.separationSchema

lemma separationTheory_eq :
    separationTheory
      = Set.range (fun ψ : SetTheorySemiproposition 1 =>
          FirstOrder.Semiformula.univCl (sepBodyMeta ψ)) := rfl

/-- The separation schema is `Δ₁`, via the recognizer `sepCh`. -/
noncomputable instance separationTheory_delta1 : separationTheory.Δ₁ where
  ch := sepCh
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] sepCh.val) ↔ SepR (⌜φ⌝ : ℕ) := by simp
    rw [h, show SepR (⌜φ⌝ : ℕ) = SchemaRecognizer ℒₛₑₜ 1 sepBodyVal (⌜φ⌝ : ℕ) from rfl,
      schemaRecognizer_quote_iff sepBodyMeta sepBodyVal sepBodyVal_quote le_sepBodyVal_quote φ,
      separationTheory_eq]
    exact (mem_range_univCl_iff sepBodyMeta φ).symm
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := SepR.defined (V := V); simp

end LeanProofs.ZFCinPA
