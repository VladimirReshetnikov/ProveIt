import ZFCinPA.ReplacementDelta1

/-!
# `Δ₁`-definability of the native global-image collection schema

The native numerical calculus axiomatizes, besides containers and
irreflexivity, **global-image collection** (GIC) for every matrix
(`SetTheory.BusyBeaver.ZFC.NativeTheory254.NativeAx`,
`ProfileCollection.CollectionInstance`). Over Foundation's `ℒₛₑₜ` its
instance for a two-variable core `ψ(x, y)` is the universal closure of

```
∀ a, ∃ b, (∀ y, y ∈ b → ∃ x, ψ(x, y)) ∧
          (∀ x, x ∈ a → (∃ y, ψ(x, y)) → ∃ y, y ∈ b ∧ ψ(x, y))
```

The skeleton is written directly in de Bruijn normal form (`gicBodyMeta`).
The development mirrors `ZFCinPA.ReplacementDelta1`: three atom codes, two
constant substitution vectors (`![#0, #1]` for support, `![#1, #0]` for
coverage), the code-level body `gicBodyVal` with its `𝚺₁`-graph, and the
`Δ₁` recognizer `gicCh` from the generic closure recognizer.
-/

namespace LeanProofs.ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open LO.FirstOrder.SetTheory

/-! ## The GIC skeleton -/

/-- `y ∈ b` in the support clause (level 3; `y = #0`, `b = #1`). -/
def gicAtomYB3 : SetTheorySemiproposition 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #1]

/-- `x ∈ a` in the coverage clause (level 3; `x = #0`, `a = #2`). -/
def gicAtomXA3 : SetTheorySemiproposition 3 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]

/-- `y ∈ b` in the coverage witness (level 4; `y = #0`, `b = #2`). -/
def gicAtomYB4 : SetTheorySemiproposition 4 :=
  FirstOrder.Semiformula.rel Language.Mem.mem ![#0, #2]

/-- The (open) GIC body for the core `ψ(x, y)`, in de Bruijn normal form. -/
def gicBodyMeta (ψ : SetTheorySemiproposition 2) : SetTheoryProposition :=
  ∀⁰ ∃⁰ ((∀⁰ (gicAtomYB3 🡒 ∃⁰ (ψ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1]))) ⋏
    (∀⁰ (gicAtomXA3 🡒 ((∃⁰ (ψ ⇜ ![(#1 : SyntacticSemiterm ℒₛₑₜ 4), #0])) 🡒
      ∃⁰ (gicAtomYB4 ⋏ (ψ ⇜ ![(#1 : SyntacticSemiterm ℒₛₑₜ 4), #0]))))))

/-! ## Typed and raw code-level bodies -/

section body

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The typed Gödel code of the GIC body, built from the typed core code. -/
noncomputable def gicBody (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 0 :=
  ∀⁰ ∃⁰ ((∀⁰ ((⌜gicAtomYB3⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) 🡒
      ∃⁰ (K.subst ![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]))) ⋏
    (∀⁰ ((⌜gicAtomXA3⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3) 🡒
      ((∃⁰ (K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝])) 🡒
        ∃⁰ ((⌜gicAtomYB4⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4) ⋏
          K.subst ![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝])))))

/-- `gicBody ⌜ψ⌝ = ⌜gicBodyMeta ψ⌝`. -/
lemma gicBody_quote (ψ : SetTheorySemiproposition 2) :
    (⌜gicBodyMeta ψ⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 0) = gicBody ⌜ψ⌝ := by
  unfold gicBodyMeta gicBody
  simp [Matrix.comp_vecCons', Matrix.constant_eq_singleton]

end body

/-! ## Code constants of the skeleton -/

noncomputable def gicAtomYB3Code : ℕ := ⌜gicAtomYB3⌝
noncomputable def gicAtomXA3Code : ℕ := ⌜gicAtomXA3⌝
noncomputable def gicAtomYB4Code : ℕ := ⌜gicAtomYB4⌝

/-- Standard `ℕ`-code of the support substitution `![#0, #1]` (level 4). -/
noncomputable def gicSubst01Const : ℕ :=
  Matrix.vecToNat fun i : Fin 2 ↦
    Encodable.encode ((![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1]) i)

/-- Standard `ℕ`-code of the coverage substitution `![#1, #0]` (level 4). -/
noncomputable def gicSubst10Const : ℕ :=
  Matrix.vecToNat fun i : Fin 2 ↦
    Encodable.encode ((![(#1 : SyntacticSemiterm ℒₛₑₜ 4), #0]) i)

section bodyVal

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma val_gicAtomYB3 :
    ((⌜gicAtomYB3⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)).val = ((gicAtomYB3Code : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote gicAtomYB3).symm

lemma val_gicAtomXA3 :
    ((⌜gicAtomXA3⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 3)).val = ((gicAtomXA3Code : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote gicAtomXA3).symm

lemma val_gicAtomYB4 :
    ((⌜gicAtomYB4⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 4)).val = ((gicAtomYB4Code : ℕ) : V) :=
  (FirstOrder.Semiformula.coe_quote_eq_quote gicAtomYB4).symm

lemma val_gicSubst01Const :
    ((gicSubst01Const : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝]
            : Bootstrapping.SemitermVec V ℒₛₑₜ 2 4) := by
  rw [gicSubst01Const,
    ← Semiterm.quote_eq_encode' (V := V) (![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1])]
  congr 1; funext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma val_gicSubst10Const :
    ((gicSubst10Const : ℕ) : V)
      = Bootstrapping.SemitermVec.val
          (![⌜(#1 : SyntacticSemiterm ℒₛₑₜ 4)⌝, ⌜(#0 : SyntacticSemiterm ℒₛₑₜ 4)⌝]
            : Bootstrapping.SemitermVec V ℒₛₑₜ 2 4) := by
  rw [gicSubst10Const,
    ← Semiterm.quote_eq_encode' (V := V) (![(#1 : SyntacticSemiterm ℒₛₑₜ 4), #0])]
  congr 1; funext i
  match i with
  | 0 => rfl
  | 1 => rfl

/-- The raw `V → V` GIC body. -/
noncomputable def gicBodyVal (k : V) : V :=
  ^∀ ^∃ ((^∀ (Bootstrapping.imp ℒₛₑₜ ((gicAtomYB3Code : ℕ) : V)
      (^∃ (Bootstrapping.subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) k)))) ^⋏
    (^∀ (Bootstrapping.imp ℒₛₑₜ ((gicAtomXA3Code : ℕ) : V)
      (Bootstrapping.imp ℒₛₑₜ (^∃ (Bootstrapping.subst ℒₛₑₜ ((gicSubst10Const : ℕ) : V) k))
        (^∃ (((gicAtomYB4Code : ℕ) : V) ^⋏
          Bootstrapping.subst ℒₛₑₜ ((gicSubst10Const : ℕ) : V) k))))))

/-- `gicBodyVal K.val = (gicBody K).val`. -/
lemma gicBodyVal_eq (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    gicBodyVal K.val = (gicBody K).val := by
  simp only [gicBodyVal, gicBody, Bootstrapping.Semiformula.val_imp,
    Bootstrapping.Semiformula.val_and, Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_exs, Bootstrapping.Semiformula.val_substs,
    val_gicAtomYB3, val_gicAtomXA3, val_gicAtomYB4, val_gicSubst01Const, val_gicSubst10Const]

/-- `gicBodyVal ⌜ψ⌝ = ⌜gicBodyMeta ψ⌝` over `ℕ`. -/
lemma gicBodyVal_quote (ψ : SetTheorySemiproposition 2) :
    gicBodyVal (⌜ψ⌝ : ℕ) = (⌜gicBodyMeta ψ⌝ : ℕ) := by
  rw [show (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : Bootstrapping.Semiformula ℕ ℒₛₑₜ 2).val from rfl,
    gicBodyVal_eq, ← gicBody_quote]
  rfl

/-- The support-clause substituted core sits inside the GIC body. -/
lemma subst01_le_gicBodyVal (k : V) :
    Bootstrapping.subst ℒₛₑₜ ((gicSubst01Const : ℕ) : V) k ≤ gicBodyVal k := by
  unfold gicBodyVal Bootstrapping.imp
  exact le_of_lt <| lt_trans (lt_exists _) <| lt_trans (lt_or_right _ _)
    <| lt_trans (lt_forall _) <| lt_trans (lt_K!_left _ _) <| lt_trans (lt_exists _) (lt_forall _)

end bodyVal

/-! ## The identity substitution on codes -/

lemma gic_subst_bvar_eq_castLE (ψ : SetTheorySemiproposition 2) :
    (ψ ⇜ ![(#0 : SyntacticSemiterm ℒₛₑₜ 4), #1])
      = (Rew.castLE (by omega) ▹ ψ : SetTheorySemiproposition 4) := by
  apply FirstOrder.Semiformula.rew_eq_of_funEqOn
  · intro x
    match x with
    | 0 => simp
    | 1 => simp
  · intro x _
    simp

lemma gic_subst_quote (ψ : SetTheorySemiproposition 2) :
    Bootstrapping.subst ℒₛₑₜ gicSubst01Const (⌜ψ⌝ : ℕ) = (⌜ψ⌝ : ℕ) := by
  have hv := val_gicSubst01Const (V := ℕ)
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
  rw [this, ← FirstOrder.Semiformula.quote_def, gic_subst_bvar_eq_castLE ψ,
    FirstOrder.Semiformula.quote_castLE (V := ℕ) ψ (by omega)]
  rfl

/-- Code-monotonicity of `gicBodyVal` on quotes. -/
lemma le_gicBodyVal_quote (ψ : SetTheorySemiproposition 2) :
    (⌜ψ⌝ : ℕ) ≤ gicBodyVal (⌜ψ⌝ : ℕ) := by
  have h := subst01_le_gicBodyVal (V := ℕ) (⌜ψ⌝ : ℕ)
  simp only [natCast_nat] at h
  rw [gic_subst_quote ψ] at h
  rcases le_def.mp h with h | h
  · exact Nat.le_of_eq h
  · exact Nat.le_of_lt h

/-! ## A concrete `𝚺₁`-graph for `gicBodyVal` -/

section graph

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def gicBodyValGraph : 𝚺₁.Semisentence 2 := .mkSigma
  “y k.
    ∃ s1, !(Bootstrapping.substsGraph ℒₛₑₜ) s1 ↑gicSubst01Const k ∧
    ∃ s2, !(Bootstrapping.substsGraph ℒₛₑₜ) s2 ↑gicSubst10Const k ∧
    ∃ e1, !qqExsDef e1 s1 ∧
    ∃ i1, !(Bootstrapping.impGraph ℒₛₑₜ) i1 ↑gicAtomYB3Code e1 ∧
    ∃ a1, !qqAllDef a1 i1 ∧
    ∃ e2, !qqExsDef e2 s2 ∧
    ∃ c3, !qqAndDef c3 ↑gicAtomYB4Code s2 ∧
    ∃ e3, !qqExsDef e3 c3 ∧
    ∃ i2, !(Bootstrapping.impGraph ℒₛₑₜ) i2 e2 e3 ∧
    ∃ i3, !(Bootstrapping.impGraph ℒₛₑₜ) i3 ↑gicAtomXA3Code i2 ∧
    ∃ a3, !qqAllDef a3 i3 ∧
    ∃ c, !qqAndDef c a1 a3 ∧
    ∃ e, !qqExsDef e c ∧
    !qqAllDef y e”

instance gicBodyVal.defined : 𝚺₁-Function₁ (gicBodyVal : V → V) via gicBodyValGraph :=
  .mk fun v ↦ by simp [gicBodyValGraph, gicBodyVal, numeral_eq_natCast]

end graph

/-! ## The `Δ₁` recognizer for the GIC schema -/

noncomputable def gicCh : 𝚫₁.Semisentence 1 := .mkDelta
  (.mkSigma “p.
    ∃ m < p + 1, ∃ b < p + 1,
      !qqAllsDef p b m ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).sigma b
      ∧ !(Bootstrapping.shiftGraph ℒₛₑₜ) b b ∧ !(Bootstrapping.bvGraph ℒₛₑₜ) m b
      ∧ ∃ fv, !fvarVecDef fv m ∧ ∃ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
        ∧ ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).sigma 2 K ∧ !gicBodyValGraph s K”)
  (.mkPi “p.
    ∃ m < p + 1, ∃ b < p + 1,
      (∀ y, !qqAllsDef y b m → y = p) ∧ !(Bootstrapping.isUFormula ℒₛₑₜ).pi b
      ∧ (∀ y, !(Bootstrapping.shiftGraph ℒₛₑₜ) y b → y = b) ∧ (∀ y, !(Bootstrapping.bvGraph ℒₛₑₜ) y b → y = m)
      ∧ ∀ fv, !fvarVecDef fv m → ∀ s, !(Bootstrapping.substsGraph ℒₛₑₜ) s fv b
        → ∃ K < s + 1, !(Bootstrapping.isSemiformula ℒₛₑₜ).pi 2 K ∧ ∀ ib, !gicBodyValGraph ib K → s = ib”)

section recognizer

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The GIC-schema recognizer as a predicate. -/
abbrev GicR : V → Prop := SchemaRecognizer ℒₛₑₜ 2 gicBodyVal

instance GicR.defined : 𝚫₁-Predicate[V] (GicR : V → Prop) via gicCh := .mk <| by
  constructor
  · intro v
    simp [gicCh, HierarchySymbol.Semiformula.val_sigma, eq_comm]
  · intro v
    simp [gicCh, HierarchySymbol.Semiformula.val_sigma, SchemaRecognizer,
      lt_succ_iff_le, eq_comm, Nat.cast_ofNat]

end recognizer

/-! ## `Δ₁` of the GIC schema -/

/-- The GIC instances, as a stand-alone theory. -/
def gicTheory : SetTheory :=
  Set.range (fun ψ : SetTheorySemiproposition 2 => FirstOrder.Semiformula.univCl (gicBodyMeta ψ))

/-- The GIC schema is `Δ₁`, via the recognizer `gicCh`. -/
noncomputable instance gicTheory_delta1 : gicTheory.Δ₁ where
  ch := gicCh
  mem_iff φ := by
    have h : (ℕ ⊧/![(⌜φ⌝ : ℕ)] gicCh.val) ↔ GicR (⌜φ⌝ : ℕ) := by simp
    rw [h, show GicR (⌜φ⌝ : ℕ) = SchemaRecognizer ℒₛₑₜ 2 gicBodyVal (⌜φ⌝ : ℕ) from rfl,
      schemaRecognizer_quote_iff gicBodyMeta gicBodyVal gicBodyVal_quote le_gicBodyVal_quote φ]
    exact (mem_range_univCl_iff gicBodyMeta φ).symm
  isDelta1 := HierarchySymbol.Semiformula.ProvablyProperOn.ofProperOn.{0} _ fun V _ _ ↦ by
    haveI := GicR.defined (V := V); simp

end LeanProofs.ZFCinPA
