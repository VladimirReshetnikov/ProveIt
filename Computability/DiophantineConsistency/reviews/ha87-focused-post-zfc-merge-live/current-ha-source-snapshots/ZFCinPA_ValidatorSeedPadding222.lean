import ZFCinPA.ValidatorImplicationContext
import ZFCinPA.ValidatorSeedImage222
import ZFCinPA.ValidatorEnvironmentStreams222

/-! Bounded even self-labels for actual C222 seeds. Finite actual checker
deductions replace the self-coded matrix by the original matrix, retaining
the new binder. Numeric bounds and parity then prove its freshness for
typed matrices using an odd binder stream. No raw CP/GIC, tagged Collection,
source-axiom image or final consistency reduction is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace LeanProofs.ZFCinPA.ValidatorSeedPadding222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorSeedWitness222
open ValidatorSeedImage222 ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

local notation "h0" => (ValidatorImplicationContext.h0 CProv)
local notation "ded1" => (ValidatorImplicationContext.ded1 CProv cProv_classical)
private lemma self_imp (a : V) : CProv (wim a a) := ded1 h0

def raised (bound p : V) : V := wim (wim (bound+1) (bound+1)) p
def seedLabel (bound p : V) : V := ValidatorSeedImage222.pad (raised bound p)

local instance wim_sigma1 : 𝚺₁-Function₂[V] wim := wim_defined.to_definable₀
instance seedLabel_definable : 𝚺₁-Function₂[V] seedLabel := by
  unfold seedLabel ValidatorSeedImage222.pad raised ValidatorRelationalCore222.neg
  definability

theorem bound_lt_seedLabel (bound p : V) : bound < seedLabel bound p := by
  have h₁ := (tagged_components (0 : V) (bound+1) (bound+1)).1
  have h₂ := (tagged_components (0 : V) (wim (bound+1) (bound+1)) p).1
  have h₃ := (tagged_components (0 : V) (raised bound p) 1).1
  have h₄ := (tagged_components (0 : V) (wim (raised bound p) 1) 1).1
  exact lt_of_lt_of_le (lt_add_one bound)
    (le_trans h₁ (le_trans h₂ (le_trans h₃ h₄)))

theorem seedLabel_mod_two (bound p : V) : seedLabel bound p % 2 = 0 := by
  unfold seedLabel ValidatorSeedImage222.pad ValidatorRelationalCore222.neg wim tagged
  simp only [add_zero]
  rw [←two_mul_two_eq_four, mul_assoc]
  simp

theorem raised_equiv (bound p : V) :
    CProv (wim (raised bound p) p) ∧ CProv (wim p (raised bound p)) :=
  ⟨ded1 (.mp h0 (.ax (self_imp (bound+1)))), cProv_k p _⟩

theorem seedLabel_equiv (bound p : V) :
    CProv (wim (seedLabel bound p) p) ∧ CProv (wim p (seedLabel bound p)) :=
  ⟨compose (double_neg_elim _) (raised_equiv bound p).1,
    compose (raised_equiv bound p).2 (double_neg_intro _)⟩

/-- Only the matrix changes; the self-label binder and both literal gates remain. -/
theorem bounded_seed_image (bound p a b : V) (ha : a≤bound) (hb : b≤bound) :
    CProv (ex (seedLabel bound p) (imageBody a b (seedLabel bound p) p)) := by
  let c := seedLabel bound p
  have hp := seedLabel_equiv bound p
  have point : CProv (wim (conj (ArithmeticSeedTemplates222.clos a b c c)
      (ArithmeticSeedTemplates222.req b c c))
      (conj (ArithmeticSeedTemplates222.clos a b c p)
        (ArithmeticSeedTemplates222.req b c p))) := by
    apply ded1
    exact .mp (.mp (.ax (conj_rule _ _))
      (.mp (.ax (closure_congr a b c c p hp.1 hp.2).1) (.mp (.ax (conj_left _ _)) h0)))
      (.mp (.ax (request_congr b c c p hp.1 hp.2).1) (.mp (.ax (conj_right _ _)) h0))
  exact cProv_mp (ex_mono c (compose point (pair_image a b c p)))
    (seed_pair a b c (ne_of_gt (lt_of_le_of_lt ha (bound_lt_seedLabel bound p)))
      (ne_of_gt (lt_of_le_of_lt hb (bound_lt_seedLabel bound p))))

theorem seedLabel_avoids (bound p env : V) (he : env≤bound) :
    Avoid (seedLabel bound p) env := by
  intro j _hj
  exact ne_of_gt (lt_of_le_of_lt (le_trans (nth_le env j) he) (bound_lt_seedLabel bound p))

theorem seedLabel_free (bound p F : V) (hF : F≤bound) :
    FreeAvoid (seedLabel bound p) F := by
  have h3 : (3 : V)<seedLabel bound p := pad_gt_three _
  exact ⟨ne_of_gt (lt_trans (by simp) h3),seedLabel_avoids bound p F hF⟩

/-- Even self-labels avoid the whole odd stream, including nonstandard indices. -/
theorem seedLabel_stream (bound p s : V) (hs : s%2=1) :
    StreamAvoid (seedLabel bound p) s := by
  intro k he
  have hm := congrArg (fun x : V => x%2) he
  simp [seedLabel_mod_two,hs] at hm

/-- Typed represented matrices have both an actual seed and its proved binder
vacuity. The source typing and exact bound-stack length remain explicit. -/
theorem typed_seed_vacuity {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (bound F B s a b : V)
    (hlen : len B=n) (hF : F≤bound) (hB : B≤bound)
    (hs : s%2=1) (ha : a≤bound) (hb : b≤bound) :
    let matrix := encode F B s p
    let c := seedLabel bound matrix
    CProv (ex c (imageBody a b c matrix)) ∧ Vac c matrix := by
  dsimp
  exact ⟨bounded_seed_image bound _ a b ha hb,
    encode_vac hp F B s _ hlen (seedLabel_free bound _ F hF)
      (seedLabel_avoids bound _ B hB) (seedLabel_stream bound _ s hs)⟩

theorem typed_seed_witnesses {n p : V}
    (hp : IsSemiformula ℒₛₑₜ n p) (bound F B s a b : V)
    (hlen : len B=n) (hF : F≤bound) (hB : B≤bound)
    (hs : s%2=1) (ha : a≤bound) (hb : b≤bound) :
    let matrix := encode F B s p
    let c := seedLabel bound matrix
    ∃ d e : V, ArithmeticHistory222.value d = ex c (imageBody a b c matrix)+1 ∧
      ArithmeticHistory222.value e = wim matrix (wal c matrix)+1 := by
  obtain ⟨⟨d,hd⟩,⟨e,he⟩⟩ := typed_seed_vacuity hp bound F B s a b hlen hF hB hs ha hb
  exact ⟨d,e,hd,he⟩

end LeanProofs.ZFCinPA.ValidatorSeedPadding222
