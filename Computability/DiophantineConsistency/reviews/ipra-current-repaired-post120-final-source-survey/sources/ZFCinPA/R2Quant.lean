import ZFCinPA.R2Neg
import ZFCinPA.ValidatorEnvironmentAlpha254
import ZFCinPA.ValidatorEnvironmentStreams254
import ZFCinPA.ValidatorEnvironmentOpening254
import ZFCinPA.ValidatorEnvironmentInstantiation254
import ZFCinPA.ValidatorNativeGicSlots254

set_option autoImplicit false
noncomputable section

/-!
# R2: the quantifier rules of the translation

Parity keeps all labels apart: free labels are odd (`OddEnv F`, fallback `1`),
the encoder's binder stream `s` is even, and the auxiliary labels
`x = 2F+3`, `w = x+2`, `u = x+4` are odd and above every free label.

* `all_step`: `∀x enc_F[x/#0]_s p ↔ enc_F (∀p)`, through one intermediate binder
  (two applications of Codex's alpha transport `encode_eq_under` and
  `eqUnder_all_of_cons`);
* `all_intro`: the universal rule, generalizing a derivation in a context of
  sequent hypotheses (vacuous in the fresh `x`);
* `ex_intro`: the existential rule, `enc_F[z/#0]_s p → enc_F (∃p)` for any odd
  label `z` of the environment, by Leibniz (`encode_eq_under` at `[w]`, `[z]`),
  `∃w (w = z)` (`rho1`) and vacuity.
-/

namespace LeanProofs.ZFCinPA.R2Quant

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254 LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254 LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254
open LeanProofs.ZFCinPA.ValidatorEqualityContext254 LeanProofs.ZFCinPA.ValidatorEqualityContextVacuity254
open LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg
open scoped LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Parity and freshness -/

lemma ne_of_parity {a b : V} (ha : a % 2 = 0) (hb : b % 2 = 1) : a ≠ b := by
  intro h
  have := congrArg (fun q : V ↦ q % 2) h
  simp [ha, hb] at this

lemma even_add_two_mul {s : V} (hs : s % 2 = 0) (k : V) : (s + 2 * k) % 2 = 0 := by
  simp [hs]

lemma odd_add_two_mul {s : V} (hs : s % 2 = 1) (k : V) : (s + 2 * k) % 2 = 1 := by
  simp [hs]

/-- An even label avoids an odd environment, its fallback included. -/
lemma freeAvoid_even {z F : V} (hz : z % 2 = 0) (hF : OddEnv F) : FreeAvoid z F :=
  even_free_avoids_odd_env hz hF

/-- A label above the environment code avoids it, fallback included when above `1`. -/
lemma freeAvoid_big {z F : V} (hz : F < z) (h1 : 1 < z) : FreeAvoid z F :=
  ⟨ne_of_gt h1, fun i _ ↦ ne_of_gt (lt_of_le_of_lt (nth_le F i) hz)⟩

lemma streamFree_even {s F : V} (hs : s % 2 = 0) (hF : OddEnv F) : StreamFree s F :=
  fun k ↦ freeAvoid_even (even_add_two_mul hs k) hF

lemma streamFree_big {u F : V} (hu : F < u) (h1 : 1 < u) : StreamFree u F :=
  fun k ↦ freeAvoid_big (lt_of_lt_of_le hu (le_add_of_nonneg_right (Arithmetic.zero_le _)))
    (lt_of_lt_of_le h1 (le_add_of_nonneg_right (Arithmetic.zero_le _)))

lemma streamEnv_one {s y : V} (h : ∀ k : V, s + 2 * k ≠ y) : StreamEnv s (y ∷ 0) :=
  fun k ↦ avoid_cons (avoid_nil _) (h k)

lemma streamEnv_one_parity {s y : V} (hs : s % 2 = 0) (hy : y % 2 = 1) : StreamEnv s (y ∷ 0) :=
  streamEnv_one fun k ↦ ne_of_parity (even_add_two_mul hs k) hy

lemma streamEnv_one_parity' {s y : V} (hs : s % 2 = 1) (hy : y % 2 = 0) : StreamEnv s (y ∷ 0) :=
  streamEnv_one fun k ↦ (ne_of_parity hy (odd_add_two_mul hs k)).symm

lemma streamEnv_one_big {s y : V} (h : y < s) : StreamEnv s (y ∷ 0) :=
  streamEnv_one fun k ↦ ne_of_gt (lt_of_lt_of_le h (le_add_of_nonneg_right (Arithmetic.zero_le _)))

lemma apart_parity {s t : V} (hs : s % 2 = 0) (ht : t % 2 = 1) : Apart s t :=
  apart_of_mod_ne (by rw [hs, ht]; simp)

lemma streamAvoid_parity {z s : V} (hz : z % 2 = 1) (hs : s % 2 = 0) : StreamAvoid z s :=
  fun k ↦ (ne_of_parity (even_add_two_mul hs k) hz).symm

lemma streamAvoid_parity' {z s : V} (hz : z % 2 = 0) (hs : s % 2 = 1) : StreamAvoid z s :=
  fun k ↦ ne_of_parity hz (odd_add_two_mul hs k)

lemma streamAvoid_big {z s : V} (h : z < s) : StreamAvoid z s := stream_of_lt h

lemma avoid_one {z y : V} (h : z ≠ y) : Avoid z (y ∷ 0) := avoid_cons (avoid_nil z) h

lemma lt_two_mul_add_one_succ (F : V) : F < 2 * (F + 1) + 1 := by
  calc F < F + 1 := by simp
    _ ≤ 2 * (F + 1) := by rw [two_mul]; exact le_add_of_nonneg_left (Arithmetic.zero_le _)
    _ < 2 * (F + 1) + 1 := by simp

lemma one_lt_two_mul_add_one_succ (F : V) : 1 < 2 * (F + 1) + 1 :=
  lt_of_lt_of_le (by simp : (1 : V) < 2 * 1 + 1)
    (by gcongr; exact le_add_of_nonneg_left (Arithmetic.zero_le F))

/-- The labels of a free environment are bounded by its code, or are the fallback. -/
lemma freeLabel_lt {F j : V} : freeLabel F j < 2 * (F + 1) + 1 := by
  classical
  by_cases hj : j < len F
  · simp only [freeLabel, hj, if_true]
    exact lt_of_le_of_lt (nth_le F j) (lt_two_mul_add_one_succ F)
  · simp only [freeLabel, hj, if_false]
    exact one_lt_two_mul_add_one_succ F

lemma freeLabel_odd {F j : V} (hF : OddEnv F) : freeLabel F j % 2 = 1 := by
  classical
  by_cases hj : j < len F
  · simpa [freeLabel, hj] using hF j hj
  · simp [freeLabel, hj]

/-! ## Binder renaming -/

lemma eqContext_nil : eqContext (0 : V) 0 = 0 := by
  simp [eqContext, prefixContext, Prefix.construction]

/-- Renaming one binder, from equivalence of the bodies under `x = y`. -/
lemma all_iff_of_eqUnder {x y P Q : V} (he : EqUnder (eqContext (x ∷ 0) (y ∷ 0)) P Q)
    (vxQ : Vac x Q) (vyP : Vac y P) : Iff2 (wal x P) (wal y Q) := by
  have hv : ∀ z : V, Vac z (eqContext (0 : V) 0) := fun z ↦ by
    rw [eqContext_nil]; exact vac_truth z
  have hall := eqUnder_all_of_cons 0 0 P Q x y he (hv x) (hv y) vxQ vyP
  have hc : CProv (eqContext (0 : V) 0) := by rw [eqContext_nil]; exact cProv_truth
  exact ⟨cProv_mp hall.1 hc, cProv_mp hall.2 hc⟩

lemma iff2_trans {a b c : V} (h₁ : Iff2 a b) (h₂ : Iff2 b c) : Iff2 a c :=
  ⟨compose h₁.1 h₂.1, compose h₂.2 h₁.2⟩

/-- The auxiliary labels. -/
abbrev lx (F : V) : V := 2 * (F + 1) + 1
abbrev lw (F : V) : V := lx F + 2
abbrev lu (F : V) : V := lw F + 2

lemma odd_two_mul_add_one (k : V) : (2 * k + 1) % 2 = 1 := by simp

lemma lx_odd (F : V) : lx F % 2 = 1 := odd_two_mul_add_one _
lemma lw_odd (F : V) : lw F % 2 = 1 := by
  rw [show lw F = 2 * (F + 2) + 1 by simp only [lw, lx]; ring]; exact odd_two_mul_add_one _
lemma lu_odd (F : V) : lu F % 2 = 1 := by
  rw [show lu F = 2 * (F + 3) + 1 by simp only [lu, lw, lx]; ring]; exact odd_two_mul_add_one _
lemma lx_gt (F : V) : F < lx F := lt_two_mul_add_one_succ F
lemma lt_add_two (a : V) : a < a + 2 := lt_add_of_pos_right a (by simp)
lemma lx_lt_lw (F : V) : lx F < lw F := lt_add_two _
lemma lw_lt_lu (F : V) : lw F < lu F := lt_add_two _
lemma one_lt_lx (F : V) : 1 < lx F := one_lt_two_mul_add_one_succ F

section Steps

variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- **The universal step**: `∀x enc[x] ↔ enc(∀p)` at the fresh odd `x`. -/
theorem all_step {p F s : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0) :
    Iff2 (wal (lx F) (encode F (lx F ∷ 0) s p)) (encode F 0 s (^∀ p)) := by
  rw [encode_all F 0 s hp.isUFormula]
  set x := lx F
  set w := lw F
  set u := lu F
  have hx : x % 2 = 1 := lx_odd F
  have hw : w % 2 = 1 := lw_odd F
  have hu : u % 2 = 1 := lu_odd F
  have hxw : x < w := lx_lt_lw F
  have hwu : w < u := lw_lt_lu F
  have hFx : F < x := lx_gt F
  have h1x : 1 < x := one_lt_lx F
  have hs2 : (s + 2) % 2 = 0 := by simp [hs]
  -- step A: x, stream s  ↦  w, stream u
  have fA : FreshPair F (x ∷ 0) (w ∷ 0) s u :=
    ⟨streamFree_even hs hF, streamFree_big (hFx.trans (hxw.trans hwu)) (h1x.trans (hxw.trans hwu)),
      streamEnv_one_parity hs hx, streamEnv_one_parity hs hw,
      streamEnv_one_big (hxw.trans hwu), streamEnv_one_big hwu, apart_parity hs hu⟩
  have eA := encode_eq_under hp F (x ∷ 0) (w ∷ 0) s u (by simp) (by simp) fA
  have vxA : Vac x (encode F (w ∷ 0) u p) :=
    encode_vac hp F (w ∷ 0) u x (by simp) (freeAvoid_big hFx h1x) (avoid_one (ne_of_lt hxw))
      (streamAvoid_big (hxw.trans hwu))
  have vwA : Vac w (encode F (x ∷ 0) s p) :=
    encode_vac hp F (x ∷ 0) s w (by simp) (freeAvoid_big (hFx.trans hxw) (h1x.trans hxw))
      (avoid_one (ne_of_gt hxw)) (streamAvoid_parity hw hs)
  have A := all_iff_of_eqUnder eA vxA vwA
  -- step B: w, stream u  ↦  s, stream s+2
  have hFw : F < w := hFx.trans hxw
  have h1w : 1 < w := h1x.trans hxw
  have fB : FreshPair F (w ∷ 0) (s ∷ 0) u (s + 2) :=
    ⟨streamFree_big (hFw.trans hwu) (h1w.trans hwu), streamFree_even hs2 hF,
      streamEnv_one_big hwu, streamEnv_one_parity' hu hs,
      streamEnv_one_parity hs2 hw,
      streamEnv_one fun k ↦ (stream_of_lt (z := s) (fresh := s + 2) (by simp) k).symm,
      apart_of_mod_ne (by rw [hu, hs2]; simp)⟩
  have eB := encode_eq_under hp F (w ∷ 0) (s ∷ 0) u (s + 2) (by simp) (by simp) fB
  have vwB : Vac w (encode F (s ∷ 0) (s + 2) p) :=
    encode_vac hp F (s ∷ 0) (s + 2) w (by simp) (freeAvoid_big hFw h1w)
      (avoid_one (ne_of_parity hs hw).symm) (streamAvoid_parity hw hs2)
  have vsB : Vac s (encode F (w ∷ 0) u p) :=
    encode_vac hp F (w ∷ 0) u s (by simp) (freeAvoid_even hs hF)
      (avoid_one (ne_of_parity hs hw)) (streamAvoid_parity' hs hu)
  exact iff2_trans A (all_iff_of_eqUnder eB vwB vsB)

/-- **The existential step**: from the instance at an odd label `z` below `lx F`,
the encoded existential. -/
theorem ex_step {p F s z : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0)
    (hz : z % 2 = 1) (hzx : z < lx F) :
    CProv (wim (encode F (z ∷ 0) s p) (encode F 0 s (^∃ p))) := by
  rw [encode_exs F 0 s hp.isUFormula]
  set w := lw F
  set u := lu F
  have hw : w % 2 = 1 := lw_odd F
  have hu : u % 2 = 1 := lu_odd F
  have hxw : lx F < w := lx_lt_lw F
  have hwu : w < u := lw_lt_lu F
  have hFw : F < w := (lx_gt F).trans hxw
  have h1w : 1 < w := (one_lt_lx F).trans hxw
  have hzw : z < w := hzx.trans hxw
  have hs2 : (s + 2) % 2 = 0 := by simp [hs]
  set P := encode F (z ∷ 0) s p
  set Qw := encode F (w ∷ 0) u p
  set Qs := encode F (s ∷ 0) (s + 2) p
  -- Leibniz at w = z
  have fL : FreshPair F (w ∷ 0) (z ∷ 0) u s :=
    ⟨streamFree_big (hFw.trans hwu) (h1w.trans hwu), streamFree_even hs hF,
      streamEnv_one_big hwu, streamEnv_one_big (hzw.trans hwu),
      streamEnv_one_parity hs hw, streamEnv_one_parity hs hz,
      apart_of_mod_ne (by rw [hu, hs]; simp)⟩
  have eL := encode_eq_under hp F (w ∷ 0) (z ∷ 0) u s (by simp) (by simp) fL
  -- renaming the s-binder to w, negated bodies
  have fR : FreshPair F (s ∷ 0) (w ∷ 0) (s + 2) u :=
    ⟨streamFree_even hs2 hF, streamFree_big (hFw.trans hwu) (h1w.trans hwu),
      streamEnv_one fun k ↦ (stream_of_lt (z := s) (fresh := s + 2) (by simp) k).symm,
      streamEnv_one_parity hs2 hw, streamEnv_one_parity' hu hs, streamEnv_one_big hwu,
      apart_of_mod_ne (by rw [hs2, hu]; simp)⟩
  have eR := encode_eq_under hp F (s ∷ 0) (w ∷ 0) (s + 2) u (by simp) (by simp) fR
  have vsQw : Vac s Qw :=
    encode_vac hp F (w ∷ 0) u s (by simp) (freeAvoid_even hs hF)
      (avoid_one (ne_of_parity hs hw)) (streamAvoid_parity' hs hu)
  have vwQs : Vac w Qs :=
    encode_vac hp F (s ∷ 0) (s + 2) w (by simp) (freeAvoid_big hFw h1w)
      (avoid_one (ne_of_parity hs hw).symm) (streamAvoid_parity hw hs2)
  have Rn := all_iff_of_eqUnder (eqUnder_neg eR) (vac_neg vsQw) (vac_neg vwQs)
  -- the equality context from w = z
  have E : CProv (wim (weq w z) (eqContext (w ∷ 0) (z ∷ 0))) := by
    have hb := eqContext_cons_backward (0 : V) 0 w z
    rw [eqContext_nil] at hb
    exact compose (conj_under (self_imp (weq w z)) (cProv_mp (cProv_k 0 (weq w z)) cProv_truth)) hb
  have L1 : CProv (wim (ValidatorQuantifierCore254.neg Qw)
      (wim (weq w z) (ValidatorQuantifierCore254.neg P))) :=
    ded3 (.mp h2 (.mp (.mp (.ax eL.2) (.mp (.ax E) h1)) h0))
  have L2 := all_mono w L1
  have L3 : CProv (wim (wal w (wim (weq w z) (ValidatorQuantifierCore254.neg P)))
      (ex w (ValidatorQuantifierCore254.neg P))) :=
    ded1 (.mp (.mp (.ax (all_imp_ex w (weq w z) (ValidatorQuantifierCore254.neg P))) h0)
      (.ax (ex_equality w z)))
  have vwP : Vac w P :=
    encode_vac hp F (z ∷ 0) s w (by simp) (freeAvoid_big hFw h1w)
      (avoid_one (ne_of_gt hzw)) (streamAvoid_parity hw hs)
  have L4 := ex_elim_of_vac (vac_neg vwP)
  have T := compose (compose (compose Rn.1 L2) L3) L4
  exact ded2 (.mp (.mp (.ax T) h0) h1)

/-- Generalization through a sequent context, internalized: the negated encodings
of formulas are vacuous in the fresh odd label `lx F`. -/
lemma cProv_gen_ctx {F s g : V} (hF : OddEnv F) (hs : s % 2 = 0) : ∀ L : V,
    (∀ i < len L, IsFormula ℒₛₑₜ L.[i]) →
    CProv (wim (wal (lx F) (imps (negEnc F s L) g)) (imps (negEnc F s L) (wal (lx F) g))) := by
  intro L
  induction L using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => intro _; simpa using self_imp (wal (lx F) g)
  case adjoin A L ih =>
    intro hL
    have ih' := ih fun i hi ↦ by simpa using hL (i + 1) (by simpa using hi)
    have hA : IsFormula ℒₛₑₜ A := by simpa using hL 0 (by simp)
    have va : Vac (lx F) (ValidatorQuantifierCore254.neg (encode F 0 s A)) :=
      vac_neg (encode_formula_vac hA F s (lx F) (freeAvoid_big (lx_gt F) (one_lt_lx F))
        (streamAvoid_parity (lx_odd F) hs))
    simp only [negEnc_cons, imps_cons]
    apply ded2
    exact .mp (.ax ih') (.mp (.mp (.ax (all_distribution (lx F) _ _)) h1) (.mp (.ax va) h0))

/-- **The universal rule in a sequent context.** -/
theorem all_intro {p F s L : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0)
    (hL : ∀ i < len L, IsFormula ℒₛₑₜ L.[i])
    (h : Der (negEnc F s L) (encode F (lx F ∷ 0) s p)) :
    Der (negEnc F s L) (encode F 0 s (^∀ p)) :=
  der_mp (der_of (all_step hp hF hs).1) (cProv_mp (cProv_gen_ctx hF hs L hL) (cProv_gen (lx F) h))

/-- **The existential rule in a context.** -/
theorem ex_intro {p F s z G : V} (hp : IsSemiformula ℒₛₑₜ 1 p) (hF : OddEnv F) (hs : s % 2 = 0)
    (hz : z % 2 = 1) (hzx : z < lx F) (h : Der G (encode F (z ∷ 0) s p)) :
    Der G (encode F 0 s (^∃ p)) :=
  der_mp (der_of (ex_step hp hF hs hz hzx)) h

end Steps

end LeanProofs.ZFCinPA.R2Quant
