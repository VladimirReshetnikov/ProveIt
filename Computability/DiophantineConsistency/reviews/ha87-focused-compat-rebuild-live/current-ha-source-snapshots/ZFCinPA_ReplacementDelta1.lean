import ZFCinPA.SeparationDelta1

/-!
# `Δ₁`-definability of the replacement schema of `𝗭𝗙`

`Axiom.replacementSchema ψ` is the universal closure of the fixed skeleton

```
(∀ x, ∃! y, ψ(x, y)) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, ψ(x, y)
```

with the two-variable instance `ψ` plugged in at three spots, each by a
constant bound-variable substitution.  The development mirrors
`ZFCinPA.SeparationDelta1`: constants for the three atom codes and three
substitution vectors, the code-level body `repBodyVal` with its `𝚺₁`-graph,
and the `Δ₁` recognizer `repCh` obtained from the generic closure recognizer.
-/

namespace LeanProofs.ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory

/-! ## The replacement skeleton -/

/-- The (open) body of the replacement axiom for the instance `ψ`. -/
def repBodyMeta (ψ : SetTheorySemiproposition 2) : SetTheoryProposition :=
  “(∀ x, ∃! y, !ψ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !ψ x y”

/-- `Axiom.replacementSchema` is the universal closure of `repBodyMeta`. -/
lemma replacementSchema_eq_univCl (ψ : SetTheorySemiproposition 2) :
    Axiom.replacementSchema ψ = FirstOrder.Semiformula.univCl (repBodyMeta ψ) := rfl

/-- The atom `z = y` of the uniqueness clause (level 3; `z = #0`, `y = #1`). -/
def repAtomEq : SetTheorySemiproposition 3 :=
  FirstOrder.Semiformula.rel Language.Eq.eq ![#0, #1]

/-- The atom `y ∈ Y` of the collection clause (level 3; `y = #0`, `Y = #1`). -/
def repAtomYY : SetTheorySemiproposition 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- The atom `x ∈ X` of the bounded witness (level 4; `x = #0`, `X = #3`). -/
def repAtomXX : SetTheorySemiproposition 4 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #3]

/-- The replacement body, resolved to its de Bruijn normal form: `ψ` enters at
three spots, under the substitutions `![#1, #0]`, `![#2, #0]` and `![#0, #1]`. -/
lemma repBodyMeta_eq (ψ : SetTheorySemiproposition 2) :
    repBodyMeta ψ
      = (∀⁰ ∃⁰ ((ψ ⇜ ![(#1 : SyntacticSemiterm ℒₛₑₜ 2), #0])
            ⋏ (∀⁰ ((ψ ⇜ ![(#2 : SyntacticSemiterm ℒₛₑₜ 3), #0]) 🡒 repAtomEq))))
        🡒 (∀⁰ ∃⁰ ∀⁰ (repAtomYY
              🡘 (∃⁰ (repAtomXX ⋏ (ψ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1]))))) := by
  have h1 : ∀ θ : SetTheorySemiproposition 2,
      (θ ⇜ ((#0 : SyntacticSemiterm ℒₛₑₜ 2) :> fun _ => #1)) = θ := by
    intro θ
    have hv : ((#0 : SyntacticSemiterm ℒₛₑₜ 2) :> fun _ => #1) = Semiterm.bvar := by
      funext i
      match i with
      | 0 => rfl
      | 1 => rfl
    rw [hv]
    simp [Rewriting.subst]
  have h2 : (ψ ⇜ ![(#1 : SyntacticSemiterm ℒₛₑₜ 2), #0])
        ⇜ ((#0 : SyntacticSemiterm ℒₛₑₜ 3) :> fun _ => #2)
      = ψ ⇜ ![(#2 : SyntacticSemiterm ℒₛₑₜ 3), #0] := by
    show Rew.subst _ ▹ (Rew.subst _ ▹ ψ) = Rew.subst _ ▹ ψ
    rw [← TransitiveRewriting.comp_app, Rew.subst_comp_subst]
    congr 2
    exact congrArg Rew.subst (by
      funext i
      match i with
      | 0 => rfl
      | 1 => rfl)
  simp [repBodyMeta, repAtomEq, repAtomYY, repAtomXX, LogicalConnective.iff,
    FirstOrder.Semiformula.Operator.mem_def, FirstOrder.Semiformula.Operator.eq_def,
    FirstOrder.Semiformula.existsUnique, FirstOrder.Semiformula.bexsMem,
    LO.FirstOrder.bexs, h1, h2]

/-! ## Typed and raw code-level bodies -/

section body

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The typed Gödel code of the replacement body, built from the typed core
code `K = ⌜ψ⌝` with the existing typed constructors. -/
noncomputable def repBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 0 :=
  (∀⁰ ∃⁰ ((K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 2)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 2)⌝])
      ⋏ (∀⁰ ((K.subst ![⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝])
          🡒 (⌜repAtomEq⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)))))
    🡒 (∀⁰ ∃⁰ ∀⁰ ((⌜repAtomYY⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)
        🡘 (∃⁰ ((⌜repAtomXX⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)
            ⋏ K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]))))

/-- `repBody ⌜ψ⌝ = ⌜repBodyMeta ψ⌝`: the typed reconstruction matches the code. -/
lemma repBody_quote (ψ : SetTheorySemiproposition 2) :
    (⌜repBodyMeta ψ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 0) = repBody ⌜ψ⌝ := by
  rw [repBodyMeta_eq]
  unfold repBody
  simp [Matrix.comp_vecCons', Matrix.constant_eq_singleton]

end body

/-! ## Code constants of the skeleton -/

/-- Standard `ℕ`-code of the atom `z = y`. -/
noncomputable def repAtomEqCode : ℕ := ⌜repAtomEq⌝

/-- Standard `ℕ`-code of the atom `y ∈ Y`. -/
noncomputable def repAtomYYCode : ℕ := ⌜repAtomYY⌝

/-- Standard `ℕ`-code of the atom `x ∈ X`. -/
noncomputable def repAtomXXCode : ℕ := ⌜repAtomXX⌝

/-- Standard `ℕ`-code of the substitution vector `![#1, #0]` (functionality
instance `ψ(x, y)`). -/
noncomputable def repSubst1Const : ℕ :=
  Matrix.vecToNat fun i : Fin 2 ↦
    Encodable.encode ((![(#1 : SyntacticSemiterm ℒₛₑₜ 2), #0]) i)

/-- Standard `ℕ`-code of the substitution vector `![#2, #0]` (uniqueness
instance `ψ(x, z)`). -/
noncomputable def repSubst2Const : ℕ :=
  Matrix.vecToNat fun i : Fin 2 ↦
    Encodable.encode ((![(#2 : SyntacticSemiterm ℒₛₑₜ 3), #0]) i)

/-- Standard `ℕ`-code of the substitution vector `![#0, #1]` (collection
instance `ψ(x, y)`). -/
noncomputable def repSubst3Const : ℕ :=
  Matrix.vecToNat fun i : Fin 2 ↦
    Encodable.encode ((![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1]) i)

section bodyVal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma val_repAtomEq :
    ((⌜repAtomEq⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)).val = ((repAtomEqCode : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote repAtomEq).symm

lemma val_repAtomYY :
    ((⌜repAtomYY⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)).val = ((repAtomYYCode : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote repAtomYY).symm

lemma val_repAtomXX :
    ((⌜repAtomXX⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)).val = ((repAtomXXCode : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote repAtomXX).symm

lemma val_repSubst1Const :
    ((repSubst1Const : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 2)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 2)⌝]
            : Bootstrapping.SemitermVec V ℒₛₑₜ 2 2) := by
  rw [repSubst1Const,
    ← Semiterm.quote_eq_encode' (V := V) (![(#1 : SyntacticSemiterm ℒₛₑₜ 2), #0])]
  congr 1; funext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma val_repSubst2Const :
    ((repSubst2Const : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(#2 : SyntacticSemiterm ℒₛₑₜ 3)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 3)⌝]
            : Bootstrapping.SemitermVec V ℒₛₑₜ 2 3) := by
  rw [repSubst2Const,
    ← Semiterm.quote_eq_encode' (V := V) (![(#2 : SyntacticSemiterm ℒₛₑₜ 3), #0])]
  congr 1; funext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma val_repSubst3Const :
    ((repSubst3Const : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]
            : Bootstrapping.SemitermVec V ℒₛₑₜ 2 4) := by
  rw [repSubst3Const,
    ← Semiterm.quote_eq_encode' (V := V) (![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1])]
  congr 1; funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- The raw `V → V` replacement body: a composition of the `𝚺₁`-definable
internal operations over the skeleton constants. -/
noncomputable def repBodyVal (k : V) : V :=
  Bootstrapping.imp ℒₛₑₜ
    (^∀ ^∃ ((Bootstrapping.subst ℒₛₑₜ ((repSubst1Const : ℕ) : V) k)
      ^⋏ (^∀ (Bootstrapping.imp ℒₛₑₜ
          (Bootstrapping.subst ℒₛₑₜ ((repSubst2Const : ℕ) : V) k)
          ((repAtomEqCode : ℕ) : V)))))
    (^∀ ^∃ ^∀ (Bootstrapping.iff ℒₛₑₜ ((repAtomYYCode : ℕ) : V)
      (^∃ (((repAtomXXCode : ℕ) : V)
        ^⋏ Bootstrapping.subst ℒₛₑₜ ((repSubst3Const : ℕ) : V) k))))

/-- `repBodyVal K.val = (repBody K).val`: the raw function computes the typed body. -/
lemma repBodyVal_eq (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    repBodyVal K.val = (repBody K).val := by
  simp only [repBodyVal, repBody, Bootstrapping.Semiformula.val_imp,
    Bootstrapping.Semiformula.val_iff, Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_all, Bootstrapping.Semiformula.val_exs,
    Bootstrapping.Semiformula.val_substs,
    val_repAtomEq, val_repAtomYY, val_repAtomXX,
    val_repSubst1Const, val_repSubst2Const, val_repSubst3Const]

/-- `repBodyVal ⌜ψ⌝ = ⌜repBodyMeta ψ⌝` over `ℕ`. -/
lemma repBodyVal_quote (ψ : SetTheorySemiproposition 2) :
    repBodyVal (⌜ψ⌝ : ℕ) = (⌜repBodyMeta ψ⌝ : ℕ) := by
  rw [show (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 2).val from rfl,
    repBodyVal_eq, ← repBody_quote]
  rfl

/-- The collection-clause substituted core sits inside the replacement body. -/
lemma subst3_le_repBodyVal (k : V) :
    Bootstrapping.subst ℒₛₑₜ ((repSubst3Const : ℕ) : V) k ≤ repBodyVal k := by
  unfold repBodyVal Bootstrapping.iff Bootstrapping.imp
  exact le_of_lt <| lt_trans (lt_K!_right _ _) <| lt_trans (lt_exists _)
    <| lt_trans (lt_or_right _ _) <| lt_trans (lt_K!_left _ _) <| lt_trans (lt_forall _)
    <| lt_trans (lt_exists _) <| lt_trans (lt_forall _) (lt_or_right _ _)

end bodyVal

/-! ## The identity substitution on codes -/

lemma rep_subst_bvar_eq_castLE (ψ : SetTheorySemiproposition 2) :
    (ψ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1])
      = (Rew.castLE (by omega) ▹ ψ : SetTheorySemiproposition 4) := by
  apply FirstOrder.Semiformula.rew_eq_of_funEqOn
  · intro x
    match x with
    | 0 => simp
    | 1 => simp
  · intro x _
    simp

lemma rep_subst_quote (ψ : SetTheorySemiproposition 2) :
    Bootstrapping.subst ℒₛₑₜ repSubst3Const (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : ℕ) := by
  have hv := val_repSubst3Const (V := ℕ)
  simp only [natCast_nat] at hv
  rw [hv,
    show (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 2).val from rfl,
    show Bootstrapping.subst ℒₛₑₜ
        (Bootstrapping.SemitermVec.val
          (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]
            : Bootstrapping.SemitermVec ℕ ℒₛₑₜ 2 4))
        (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 2).val
      = ((⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 2).subst
          ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]).val from rfl]
  have : ((⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 2).subst
      ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝])
      = (⌜(ψ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1])⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 4) := by
    simp [Matrix.comp_vecCons', Matrix.constant_eq_singleton]
  rw [this, ← FirstOrder.Semiformula.quote_def, rep_subst_bvar_eq_castLE ψ,
    FirstOrder.Semiformula.quote_castLE (V := ℕ) ψ (by omega)]
  rfl

/-- Code-monotonicity of `repBodyVal` on quotes, in `ℕ`'s standard order. -/
lemma le_repBodyVal_quote (ψ : SetTheorySemiproposition 2) :
    (⌜ψ⌝ : ℕ) ≤ repBodyVal (⌜ψ⌝ : ℕ) := by
  have h := subst3_le_repBodyVal (V := ℕ) (⌜ψ⌝ : ℕ)
  simp only [natCast_nat] at h
  rw [rep_subst_quote ψ] at h
  rcases le_def.mp h with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt h

/-! ## A concrete `𝚺₁`-graph for `repBodyVal` -/

section graph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Concrete `𝚺₁`-graph of `repBodyVal`: a chain of the component graphs over
the skeleton constants. -/
noncomputable def repBodyValGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ s1, !(Bootstrapping.substsGraph ℒₛₑₜ) s1 ↑repSubst1Const k ∧
    ∃ s2, !(Bootstrapping.substsGraph ℒₛₑₜ) s2 ↑repSubst2Const k ∧
    ∃ s3, !(Bootstrapping.substsGraph ℒₛₑₜ) s3 ↑repSubst3Const k ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 s2 ↑repAtomEqCode ∧
    ∃ a2, !qqAllDef a2 i2 ∧
    ∃ c1, !qqAndDef c1 s1 a2 ∧
    ∃ e1, !qqExsDef e1 c1 ∧
    ∃ a1, !qqAllDef a1 e1 ∧
    ∃ c3, !qqAndDef c3 ↑repAtomXXCode s3 ∧
    ∃ e3, !qqExsDef e3 c3 ∧
    ∃ f3, !(Bootstrapping.iffGraph ℒₛₑₜ) f3 ↑repAtomYYCode e3 ∧
    ∃ a3, !qqAllDef a3 f3 ∧
    ∃ e4, !qqExsDef e4 a3 ∧
    ∃ a4, !qqAllDef a4 e4 ∧
    !(Bootstrapping.impGraph ℒₛₑₜ) y a1 a4”

instance repBodyVal.defined : 𝚺₁-Function₁ (repBodyVal : V → V) via repBodyValGraph := .mk fun v ↦ by
  simp [repBodyValGraph, repBodyVal, numeral_eq_natCast]

end graph

/-! ## The `Δ₁` recognizer for the replacement schema -/

/-- Concrete `𝚫₁.Semisentence 1` recognizer for the replacement schema. -/
noncomputable def repCh : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₛₑₜ) b b ∧ !(Bootstrapping.bvGraph ℒₛₑₜ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).sigma 2 K ∧ !repBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₛₑₜ) y b → y = b) ∧ (∀ y, !(Bootstrapping.bvGraph ℒₛₑₜ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).pi 2 K ∧ ∀ ib, !repBodyValGraph ib K → s = ib”)

section recognizer

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The replacement-schema recognizer as a predicate. -/
abbrev RepR : V → Prop := SchemaRecognizer ℒₛₑₜ 2 repBodyVal

instance RepR.defined : 𝚫₁-Predicate[V] (RepR : V → Prop) via repCh := .mk <| by
  constructor
  · intro v
    simp [repCh, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [repCh, HierarchySymbol.Semiformula.val_sigma, SchemaRecognizer,
      lt_succ_iff_le, eq_comm, Nat.cast_ofNat]

end recognizer

/-! ## `Δ₁` of the replacement schema -/

/-- The replacement instances of `𝗭𝗙`, as a stand-alone theory. -/
def replacementTheory : SetTheory := Set.range Axiom.replacementSchema

lemma replacementTheory_eq :
    replacementTheory
      = Set.range (fun ψ : SetTheorySemiproposition 2 =>
          FirstOrder.Semiformula.univCl (repBodyMeta ψ)) := rfl

/-- The replacement schema is `Δ₁`, via the recognizer `repCh`. -/
noncomputable instance replacementTheory_delta1 : replacementTheory.Δ₁ where
  ch := repCh
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] repCh.val) ↔ RepR (⌜φ⌝ : ℕ) := by simp
    rw [h, show RepR (⌜φ⌝ : ℕ) = SchemaRecognizer ℒₛₑₜ 2 repBodyVal (⌜φ⌝ : ℕ) from rfl,
      schemaRecognizer_quote_iff repBodyMeta repBodyVal repBodyVal_quote le_repBodyVal_quote φ,
      replacementTheory_eq]
    exact (mem_range_univCl_iff repBodyMeta φ).symm
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := RepR.defined (V := V); simp

end LeanProofs.ZFCinPA
