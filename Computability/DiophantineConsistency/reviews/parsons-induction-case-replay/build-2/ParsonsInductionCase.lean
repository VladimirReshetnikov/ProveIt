import DiophantineConsistency.ParsonsRule
import DiophantineConsistency.ParsonsSelection
/-! The principal existential case in the cut-free reduction of a negative
Σ₁ induction axiom. This file does not assert the overall conservation theorem. -/
set_option autoImplicit false
namespace DiophantineConsistency.ParsonsInductionCase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open ParsonsRule ParsonsSelection
variable {L : Language} [L.ORing]

/-- The witness is the induction counter; all original free parameters remain. -/
def matrix (φ : Semiproposition L 1) : Semiproposition L 1 :=
  (Rew.bShift ▹ base φ) ⋏ ((Rew.bShift ▹ step φ) ⋏ ∼φ)

@[simp] theorem matrix_subst (φ : Semiproposition L 1) (t : SyntacticTerm L) :
    (matrix φ)/[t] = base φ ⋏ (step φ ⋏ ∼(φ/[t])) := by
  simp [matrix, ← TransitiveRewriting.comp_app]

theorem matrix_free (φ : Semiproposition L 1) :
    (matrix φ).free = Rewriting.shift (base φ) ⋏
      (Rewriting.shift (step φ) ⋏ ∼φ.free) := by
  simp [matrix, ← TransitiveRewriting.comp_app]

/-- Logical normalization of the open negated induction axiom; all free
parameters remain free and are shifted under the eigenvariable. -/
def induction_normalization (φ : Semiproposition L 1) :
    Derivation [succInd φ, ∃⁰ (matrix φ)] := by
  let A := Rewriting.shift (base φ)
  let B := Rewriting.shift (step φ)
  let P := φ.free
  have ha : Derivation [A, P, ∼A, ∼B] := Derivation.close A (by simp) (by simp)
  have hb : Derivation [B, P, ∼A, ∼B] := Derivation.close B (by simp) (by simp)
  have hn : Derivation [∼P, P, ∼A, ∼B] := Derivation.close P (by simp) (by simp)
  have hm : Derivation [A ⋏ (B ⋏ ∼P), P, ∼A, ∼B] := ha.and (hb.and hn)
  have hm' : Derivation [(Rewriting.shift (matrix φ))/[&0], P, ∼A, ∼B] := by
    simpa [P, A, B, matrix_free] using hm
  have hex : Derivation [∃⁰ Rewriting.shift (matrix φ), P, ∼A, ∼B] := hm'.exs
  have hfree : Derivation (φ.free :: [∼base φ, ∼step φ, ∃⁰ matrix φ]⁺) := by
    simpa [A, B, P, Rewriting.shifts] using hex.contra
      (Γ := [P, ∼A, ∼B, ∃⁰ Rewriting.shift (matrix φ)]) (by simp)
  have hall : Derivation [∀⁰ φ, ∼base φ, ∼step φ, ∃⁰ matrix φ] := hfree.all
  have h1 : Derivation [∼step φ, ∀⁰ φ, ∼base φ, ∃⁰ matrix φ] := hall.contra (by simp)
  have h2 : Derivation [∼base φ, ∼step φ ⋎ (∀⁰ φ), ∃⁰ matrix φ] := h1.or.contra (by simp)
  have h3 : Derivation [(∼base φ) ⋎ (∼step φ ⋎ (∀⁰ φ)), ∃⁰ matrix φ] := h2.or
  simpa [succInd, base, step, Semiformula.imp_eq] using h3

/-- Replace an open negative induction axiom in a context using a logical
cut. This normalization must be performed before the cut-elimination pass;
no height bound or cut-freeness is claimed for the resulting derivation. -/
def normalize_in_context (φ : Semiproposition L 1) (Γ : Sequent L)
    (d : Derivation (∼(succInd φ) :: Γ)) : Derivation ((∃⁰ matrix φ) :: Γ) := by
  simpa using (induction_normalization φ).cut d

/-- Each inverted matrix premise is strictly shorter than the existential step. -/
theorem invert_exists (φ : Semiproposition L 1) (t : SyntacticTerm L)
    (Γ : Sequent L) (d : Derivation ((matrix φ)/[t] :: Γ))
    (hc : Derivation.IsCutFree d) :
    (∃ e : Derivation (base φ :: Γ), Derivation.IsCutFree e ∧ e.height < d.exs.height) ∧
    (∃ e : Derivation (step φ :: Γ), Derivation.IsCutFree e ∧ e.height < d.exs.height) ∧
    (∃ e : Derivation (∼(φ/[t]) :: Γ), Derivation.IsCutFree e ∧ e.height < d.exs.height) := by
  have he : (matrix φ)/[t] :: Γ = (base φ ⋏ (step φ ⋏ ∼(φ/[t]))) :: Γ := by simp
  let h : Derivation ((base φ ⋏ (step φ ⋏ ∼(φ/[t]))) :: Γ) := d.cast he
  have hc' : Derivation.IsCutFree h := by simpa [h] using hc
  have hh : h.height = d.height := by simp [h]
  obtain ⟨⟨a, ha, hla⟩, ⟨b, hb, hlb⟩, ⟨c, hcc, hlc⟩⟩ := invert_three h hc'
  refine ⟨⟨a, ha, ?_⟩, ⟨b, hb, ?_⟩, ⟨c, hcc, ?_⟩⟩ <;>
    simp only [Derivation.height_exs] <;> omega

/-- The principal existential case, assuming the three genuinely smaller
recursive cases have already been translated. No global conservation premise. -/
theorem one_case {T : Theory L} (φ : Semiproposition L 1) (E : Proposition L)
    (t : SyntacticTerm L) (Γ : Sequent L)
    (d : Derivation ((matrix φ)/[t] :: Γ)) (hc : Derivation.IsCutFree d)
    (hφ : Hierarchy 𝚺 1 φ) (hE : Hierarchy 𝚺 1 E)
    (hbase : ∀ e : Derivation (base φ :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (Proof T (base φ ⋎ E)))
    (hstep : ∀ e : Derivation (step φ :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (Proof T (step φ ⋎ E)))
    (hneg : ∀ e : Derivation (∼(φ/[t]) :: Γ), Derivation.IsCutFree e →
      e.height < d.exs.height → Nonempty (Proof T (∼(φ/[t]) ⋎ E))) :
    Nonempty (Proof T E) := by
  obtain ⟨⟨a, ha, hla⟩, ⟨b, hb, hlb⟩, ⟨c, hcc, hlc⟩⟩ := invert_exists φ t Γ d hc
  exact ⟨three_disjunctions φ E t hφ hE (hbase a ha hla).some
    (hstep b hb hlb).some (hneg c hcc hlc).some⟩

end DiophantineConsistency.ParsonsInductionCase
