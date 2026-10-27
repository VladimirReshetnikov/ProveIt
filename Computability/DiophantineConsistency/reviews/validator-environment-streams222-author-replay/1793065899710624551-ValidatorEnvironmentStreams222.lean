import ZFCinPA.ValidatorEnvironmentAlpha222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-!
Concrete internal fresh-stream selection and composition of actual C222 alpha
transport. The fixed Σ0 selector uses IΣ1; formula transport invokes the
accepted IΣ2 Alpha222 theorem. No CProv254 semantics are used. A coarse bound by the numeric vector code suffices for every stored
label. The fixed selector chooses the opposite parity above that bound. The
formula client compares arbitrary free-safe starts, including overlapping
streams. Original-stream safety remains explicit; source substitution,
semantic quantifier inference and proof translation are not asserted.
-/
namespace LeanProofs.ZFCinPA.ValidatorEnvironmentStreams222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEnvironmentAlpha222
open scoped LO.FirstOrder.Arithmetic

/-- Graph argument order is output, coarse bound, original stream seed. -/
def alternateStartDef : 𝚺₀.Semisentence 3 := .mkSigma
  “out bound seed. ∃ r < 2, !remDef r seed 2 ∧
    ((r = 0 ∧ out = 2 * (bound + 2) + 1) ∨
     (r ≠ 0 ∧ out = 2 * (bound + 2)))”

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def alternateStart (bound seed : V) : V := by
  classical
  exact if seed % 2=0 then 2*(bound+2)+1 else 2*(bound+2)

instance alternateStart_defined : 𝚺₀-Function₂[V] alternateStart via alternateStartDef :=
  .mk fun v => by
    classical
    by_cases hs : v 2 % 2=0 <;>
      simp [alternateStartDef,alternateStart,hs,mod_lt (v 2) (b := 2) (by simp)]
instance alternateStart_sigma1 : 𝚺₁-Function₂[V] alternateStart :=
  alternateStart_defined.to_definable₀

lemma streamEnv_of_lt {s B : V} (hB : B<s) : StreamEnv s B := by
  intro k i _hi
  exact ne_of_gt (lt_of_le_of_lt (nth_le B i)
    (lt_of_lt_of_le hB (le_add_of_nonneg_right (Arithmetic.zero_le _))))

lemma streamFree_of_bounds {s F : V} (hF : F<s) (h1 : 1<s) : StreamFree s F := by
  intro k
  exact ⟨ne_of_gt (lt_of_lt_of_le h1 (le_add_of_nonneg_right (Arithmetic.zero_le _))),
    streamEnv_of_lt hF k⟩

lemma apart_of_mod_ne {s t : V} (h : s % 2≠t % 2) : Apart s t := by
  intro i j hij
  apply h
  simpa using congrArg (fun x : V => x % 2) hij

private lemma double_bound (bound : V) : bound+2≤2*(bound+2) := by
  simpa using mul_le_mul_of_nonneg_right (show (1 : V)≤2 by simp)
    (Arithmetic.zero_le (bound+2))

lemma bound_lt_alternateStart (bound seed : V) : bound<alternateStart bound seed := by
  have hb : bound<2*(bound+2) := lt_of_lt_of_le (by simp) (double_bound bound)
  classical
  unfold alternateStart
  split
  · exact lt_of_lt_of_le hb (le_add_of_nonneg_right (Arithmetic.zero_le _))
  · exact hb

lemma one_lt_alternateStart (bound seed : V) : 1<alternateStart bound seed := by
  have hb : (1 : V)<2*(bound+2) :=
    lt_of_lt_of_le (lt_of_lt_of_le (show (1 : V)<2 by simp) (by simp)) (double_bound bound)
  classical
  unfold alternateStart
  split
  · exact lt_of_lt_of_le hb (le_add_of_nonneg_right (Arithmetic.zero_le _))
  · exact hb

lemma alternateStart_mod_ne (bound seed : V) : seed % 2≠alternateStart bound seed % 2 := by
  classical
  by_cases hs : seed % 2=0
  · simp [alternateStart,hs]
  · have hs1 : seed % 2=1 := mod_two_not_zero_iff.mp hs
    simp [alternateStart,hs,hs1]

lemma alternateStart_apart (bound seed : V) : Apart seed (alternateStart bound seed) :=
  apart_of_mod_ne (alternateStart_mod_ne bound seed)

lemma alternateStart_env (bound seed B : V) (hB : B≤bound) :
    StreamEnv (alternateStart bound seed) B :=
  streamEnv_of_lt (lt_of_le_of_lt hB (bound_lt_alternateStart bound seed))

lemma alternateStart_free (bound seed F : V) (hF : F≤bound) :
    StreamFree (alternateStart bound seed) F :=
  streamFree_of_bounds (lt_of_le_of_lt hF (bound_lt_alternateStart bound seed))
    (one_lt_alternateStart bound seed)

/-- A concrete stream avoiding F, fallback1 and both bound stacks. The sum
bound uses existing nth_le, and requires no new maximum-fold computation. -/
lemma alternateStart_resources (F B B' seed : V) :
    StreamFree (alternateStart (F+B+B') seed) F ∧
    StreamEnv (alternateStart (F+B+B') seed) B ∧
    StreamEnv (alternateStart (F+B+B') seed) B' ∧
    Apart seed (alternateStart (F+B+B') seed) := by
  refine ⟨alternateStart_free _ _ _ ?_,alternateStart_env _ _ _ ?_,
    alternateStart_env _ _ _ ?_,alternateStart_apart _ _⟩
  · exact le_trans (le_add_of_nonneg_right (Arithmetic.zero_le B))
      (le_add_of_nonneg_right (Arithmetic.zero_le B'))
  · exact le_trans (le_add_of_nonneg_left (Arithmetic.zero_le F))
      (le_add_of_nonneg_right (Arithmetic.zero_le B'))
  · exact le_add_of_nonneg_left (Arithmetic.zero_le (F+B))

/-- Compare arbitrary free-safe starts. When their residues agree, compose
through the explicit fresh stream of the opposite parity. -/
theorem encode_formula_relabel [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s t : V) (hs : StreamFree s F) (ht : StreamFree t F) :
    CProv (wim (encode F 0 s p) (encode F 0 t p)) ∧
    CProv (wim (encode F 0 t p) (encode F 0 s p)) := by
  classical
  by_cases hmod : s % 2=t % 2
  · let u := alternateStart F s
    have hu : StreamFree u F := alternateStart_free F s F (le_refl F)
    have hsu : Apart s u := alternateStart_apart F s
    have htu : Apart t u := apart_of_mod_ne (by
      rw [← hmod]
      exact alternateStart_mod_ne F s)
    have hsu' := encode_formula_alpha hp F s u hs hu hsu
    have htu' := encode_formula_alpha hp F t u ht hu htu
    exact ⟨compose hsu'.1 htu'.2,compose htu'.1 hsu'.2⟩
  · exact encode_formula_alpha hp F s t hs ht (apart_of_mod_ne hmod)

/-- The overlapping next-stream case needed after one binder allocation. -/
lemma encode_formula_next [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2] {p : V} (hp : IsFormula ℒₛₑₜ p)
    (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode F 0 s p) (encode F 0 (s+2) p)) ∧
    CProv (wim (encode F 0 (s+2) p) (encode F 0 s p)) :=
  encode_formula_relabel hp F s (s+2) hs (streamFree_next hs)

end LeanProofs.ZFCinPA.ValidatorEnvironmentStreams222
