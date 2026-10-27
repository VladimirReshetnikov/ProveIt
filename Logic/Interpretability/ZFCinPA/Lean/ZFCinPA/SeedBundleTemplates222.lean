import ZFCinPA.SeedTemplate222

set_option autoImplicit false
noncomputable section

/-!
# The negated C222 `nks` clause as two compiled template sentences

The C222 seed bundle is `¬(vrel → nks)`, where `nks a b c` says that no
container `c` is both closed and answers the root request. Its negation is a
fixed sentence over one BINARY placeholder `R(input, output)` for the matrix:

* `nksB`: distinct input/output labels, with the root input quantified;
* `nksD`: coincident labels (`a = b`); the matrix is read as `R(x, x)`.

Both sentences are written in explicit de Bruijn form with exactly the
connectives of the decoded circuit (implications into `⊥`, universal
quantifiers, membership atoms), so their compiled translations coincide with
the named decoded formulas. Each holds in every template model by
`SeedTemplate222.models_seed`; compilation gives internal `𝗭𝗙`-proofs at every
internal matrix (`zf_nksB`, `zf_nksD`).
-/

namespace LeanProofs.ZFCinPA.SeedBundleTemplates222

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA LeanProofs.ZFCinPA.SetPlaceholders LeanProofs.ZFCinPA.LTemplate

abbrev arB : Fin 1 → ℕ := fun _ => 2
abbrev LB := setTemplateLanguage 1 arB

local instance : Language.Mem LB := ⟨Sum.inl Language.Set.Rel.mem⟩

/-- `R(#i, #j)`: input `#i`, output `#j`. -/
def rA {n : ℕ} (i j : Fin n) : Semisentence LB n :=
  Semiformula.rel (placeholderRel (0 : Fin 1)) ![#i, #j]

/-- `#i ∈ #j`. -/
def mA {n : ℕ} (i j : Fin n) : Semisentence LB n :=
  Semiformula.rel (Sum.inl Language.Set.Rel.mem) ![#i, #j]

/-! ## Distinct labels -/

/-- The request of the root (`#2` at depth 3) against the container (`#1`). -/
def reqRoot : Semisentence LB 2 :=
  ∀⁰ (rA 2 0 🡒 ((∀⁰ (rA 3 0 🡒 (mA 0 2 🡒 ⊥))) 🡒 ⊥))

/-- The request of the inner input `x'` (`#0` at depth 5) against `C` (`#3`). -/
def reqInner : Semisentence LB 5 :=
  ∀⁰ (rA 1 0 🡒 ((∀⁰ (rA 2 0 🡒 (mA 0 5 🡒 ⊥))) 🡒 ⊥))

/-- The closure of the container `C = #0` (depth 2, root `#1`). -/
def closB : Semisentence LB 2 :=
  ∀⁰ (mA 0 1 🡒 ((∀⁰ (rA 0 1 🡒 ((∀⁰ ((∀⁰ (mA 0 1 🡒 mA 0 3)) 🡒 reqInner)) 🡒 ⊥))) 🡒 ⊥))

/-- `∀ A ¬nks(A)`. -/
def nksB : Sentence LB := ∀⁰ ((∀⁰ (closB 🡒 (reqRoot 🡒 ⊥))) 🡒 ⊥)

/-! ## Coincident labels -/

def reqDiag1 : Semisentence LB 1 :=
  ∀⁰ (rA 0 0 🡒 ((∀⁰ (rA 0 0 🡒 (mA 0 2 🡒 ⊥))) 🡒 ⊥))

def reqDiag4 : Semisentence LB 4 :=
  ∀⁰ (rA 0 0 🡒 ((∀⁰ (rA 0 0 🡒 (mA 0 5 🡒 ⊥))) 🡒 ⊥))

def closD : Semisentence LB 1 :=
  ∀⁰ (mA 0 1 🡒 ((∀⁰ (rA 0 0 🡒 ((∀⁰ ((∀⁰ (mA 0 1 🡒 mA 0 1)) 🡒 reqDiag4)) 🡒 ⊥))) 🡒 ⊥))

def nksD : Sentence LB := (∀⁰ (closD 🡒 (reqDiag1 🡒 ⊥))) 🡒 ⊥

/-! ## Semantics -/

section Semantics

variable {M : Type} [Nonempty M] [SetStructure M] [Structure LB M] [Structure.Eq LB M]
  [Structure.Mem LB M] [M↓[LB] ⊧* templTheory 1 arB]

/-- The placeholder relation, input first. -/
abbrev Rr (x y : M) : Prop :=
  Structure.rel (L := LB) (placeholderRel (0 : Fin 1)) ![x, y]

/-- The seed relation with the output first, read from `R(input, output)`. -/
def rOut : Semisentence LB 2 := rA 1 0

/-- The diagonal seed relation `R(y, y)`, output first. -/
def rDiag : Semisentence LB 2 := rA 0 0

omit [Nonempty M] [M↓[LB] ⊧* templTheory 1 arB] in
@[simp] lemma eval_rA {n : ℕ} (i j : Fin n) (e : Fin n → M) :
    (rA i j).Eval e Empty.elim ↔ Rr (e i) (e j) := by
  simp [rA, Rr, Semiformula.eval_rel]

omit [Nonempty M] [M↓[LB] ⊧* templTheory 1 arB] in
@[simp] lemma eval_mA {n : ℕ} (i j : Fin n) (e : Fin n → M) :
    (mA i j).Eval e Empty.elim ↔ e i ∈ e j := by
  simp only [mA, Semiformula.eval_rel]
  exact Structure.mem_lang (L := LB) (M := M)

theorem models_nksB : M↓[LB] ⊧ nksB := by
  have hs := SeedTemplate222.models_seed (k := 1) (arities := arB) (M := M) rOut
  simp only [SetTheory.BusyBeaver.ZFC.KSeed222.SeedProp, SeedTemplate222.Qr, rOut, eval_rA] at hs
  simp [models_iff, nksB, closB, reqRoot, reqInner]
  intro A
  obtain ⟨C, hroot, hclos⟩ := hs A
  refine ⟨C, fun y hy => ?_, fun b hb => ?_⟩
  · obtain ⟨x, hx, hcl⟩ := hclos y hy
    refine ⟨⟨x, by simpa using hx⟩, fun x' hsub b hb => ?_⟩
    obtain ⟨z, hz, hzC⟩ := hcl x' hsub b (by simpa using hb)
    exact ⟨z, by simpa using hz, hzC⟩
  · obtain ⟨z, hz, hzC⟩ := hroot b (by simpa using hb)
    exact ⟨z, by simpa using hz, hzC⟩

theorem models_nksD : M↓[LB] ⊧ nksD := by
  have hs := SeedTemplate222.models_seed (k := 1) (arities := arB) (M := M) rDiag
  simp only [SetTheory.BusyBeaver.ZFC.KSeed222.SeedProp, SeedTemplate222.Qr, rDiag, eval_rA] at hs
  obtain ⟨C, hroot, hclos⟩ := hs (Classical.arbitrary M)
  simp [models_iff, nksD, closD, reqDiag1, reqDiag4]
  refine ⟨C, fun y hy => ?_, fun b hb => ?_⟩
  · obtain ⟨x, hx, -⟩ := hclos y hy
    refine ⟨⟨y, by simpa using hx⟩, fun b hb => ?_⟩
    obtain ⟨z, hz, hzC⟩ := hroot b (by simpa using hb)
    exact ⟨z, by simpa using hz, hzC⟩
  · obtain ⟨z, hz, hzC⟩ := hroot b (by simpa using hb)
    exact ⟨z, by simpa using hz, hzC⟩

end Semantics

theorem nksB_provable : templTheory 1 arB ⊢ nksB := by
  apply templ_provable
  intro M _ _ _ _ _ _
  exact models_nksB

theorem nksD_provable : templTheory 1 arB ⊢ nksD := by
  apply templ_provable
  intro M _ _ _ _ _ _
  exact models_nksD

/-! ## Compiled at internal matrices -/

section Compile

open LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem zf_nksB (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula (fun _ : Fin 1 => K) (Rewriting.emb nksB) :=
  compileT_provable (fun _ => by norm_num) (fun _ => K) nksB_provable

theorem zf_nksD (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula (fun _ : Fin 1 => K) (Rewriting.emb nksD) :=
  compileT_provable (fun _ => by norm_num) (fun _ => K) nksD_provable

end Compile

end LeanProofs.ZFCinPA.SeedBundleTemplates222
