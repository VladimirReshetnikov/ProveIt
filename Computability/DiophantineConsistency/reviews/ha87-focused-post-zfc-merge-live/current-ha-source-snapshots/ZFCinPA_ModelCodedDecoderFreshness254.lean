import ZFCinPA.ModelCodedBindOneCommute
import ZFCinPA.ModelCodedDecoderAtomicVacuity254

set_option autoImplicit false

/-!
Positive source codes are fresh named labels for their own decoded formulas.
The proof uses internal Pi1 order induction, not external standardness or a
free-variable bound confused with the target syntax's bound-variable bound.
The literal decoder zero contains free label zero and is explicitly excluded.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

private instance termBindOneAt_delta : 𝚫₁-Function₃[V] (termBindOneAt L) :=
  termBindOneAt_defined.graph_delta.to_definable
private instance bindOneAt_delta : 𝚫₁-Function₃[V] (bindOneAt L) :=
  bindOneAt_defined.graph_delta.to_definable
private instance decode_delta : 𝚫₁-Function₁[V] decode :=
  decode_defined.graph_delta.to_definable

lemma bindOneAt_isUFormula {p : V} (hp : IsUFormula L p) :
    ∀ chosen depth : V, IsUFormula L (bindOneAt L chosen depth p) :=
  ModelCodedBindOneCommute.bindOneAt_isUFormula hp

/-- Binding distinct free labels commutes when each keeps its own depth. -/
lemma termBindOneAt_commute {term : V} (ht : IsUTerm L term) :
    ∀ a b d e : V, a ≠ b →
    termBindOneAt L a d (termBindOneAt L b e term) =
      termBindOneAt L b e (termBindOneAt L a d term) :=
  ModelCodedBindOneCommute.termBindOneAt_commute ht

lemma termBindOneVecAt_commute {arity terms : V} (ht : IsUTermVec L arity terms)
    (a b d e : V) (hab : a ≠ b) :
    termBindOneVecAt L a d arity (termBindOneVecAt L b e arity terms) =
      termBindOneVecAt L b e arity (termBindOneVecAt L a d arity terms) :=
  ModelCodedBindOneCommute.termBindOneVecAt_commute ht a b d e hab

lemma bindOneAt_commute {p : V} (hp : IsUFormula L p) :
    ∀ a b d e : V, a ≠ b →
    bindOneAt L a d (bindOneAt L b e p) =
      bindOneAt L b e (bindOneAt L a d p) :=
  ModelCodedBindOneCommute.bindOneAt_commute hp

private lemma formula_at_depth {p : V} (hp : IsFormula L p) (depth : V) :
    IsSemiformula L depth p :=
  ⟨hp.isUFormula,le_trans hp.bv_le (by simp)⟩

lemma atomCode_binder_fresh (symbol a b chosen depth : V)
    (hr : (ℒₛₑₜ).IsRel 2 symbol) (ha : a ≠ chosen) (hb : b ≠ chosen) :
    bindOneAt ℒₛₑₜ chosen depth (atomCode symbol a b) = atomCode symbol a b := by
  unfold atomCode
  rw [bindOneAt_rel chosen depth hr (by simp),
    termBindOneVecAt_pair chosen depth _ _ (by simp) (by simp),
    termBindOneAt_other chosen depth a ha,termBindOneAt_other chosen depth b hb]

/-- Internal order induction includes code zero only with a positive chosen
label. Every label read from a positive source row is strictly below its code. -/
theorem decode_binder_fresh (code : V) :
    ∀ chosen depth : V, 0 < chosen → code ≤ chosen →
    bindOneAt ℒₛₑₜ chosen depth (decode code) = decode code := by
  induction code using ISigma1.pi1_order_induction
  · definability
  case ind code ih =>
    intro chosen depth hchosen hle
    have hr0 : (ℒₛₑₜ).IsRel (2 : V) 0 := by
      simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 0)).mpr
        ⟨Language.Set.Rel.eq,rfl⟩
    have hr1 : (ℒₛₑₜ).IsRel (2 : V) 1 := by
      simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
        ⟨Language.Set.Rel.mem,rfl⟩
    by_cases hz : code = 0
    · subst code
      rw [decode_zero]
      unfold zeroFormula
      rw [bindOneAt_imp (formula_at_depth (memCode_isFormula 0 0) depth)
        (formula_at_depth (memCode_isFormula 0 0) depth) chosen,
        atomCode_binder_fresh 1 0 0 chosen depth hr1 (ne_of_lt hchosen) (ne_of_lt hchosen)]
    · have hpos : 0 < code := lt_of_le_of_ne (by simp) (Ne.symm hz)
      have ha := (child_bounds hpos).1
      have hb := (child_bounds hpos).2
      have hia (d : V) := ih _ ha chosen d hchosen (le_trans (le_of_lt ha) hle)
      have hib (d : V) := ih _ hb chosen d hchosen (le_trans (le_of_lt hb) hle)
      have hna : _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCantor.first (code/4) ≠ chosen :=
        ne_of_lt (lt_of_lt_of_le ha hle)
      have hnb : _root_.SetTheory.BusyBeaver.ZFC.ArithmeticCantor.second (code/4) ≠ chosen :=
        ne_of_lt (lt_of_lt_of_le hb hle)
      rw [decode_positive code hz]
      by_cases h0 : code%4 = 0
      · simp only [h0,if_pos]
        rw [bindOneAt_imp (formula_at_depth (decode_isFormula _) depth)
          (formula_at_depth (decode_isFormula _) depth) chosen,hia depth,hib depth]
      · by_cases h1 : code%4 = 1
        · rw [if_neg h0,if_pos h1]
          exact atomCode_binder_fresh 1 _ _ chosen depth hr1 hna hnb
        · by_cases h2 : code%4 = 2
          · rw [if_neg h0,if_neg h1,if_pos h2]
            unfold namedAll
            rw [bindOneAt_all chosen depth (bindOneAt_isSemiformula (decode_isFormula _) _).isUFormula,
              bindOneAt_commute (decode_isFormula _).isUFormula chosen _ (depth+1) 0 hna.symm,
              hib (depth+1)]
          · rw [if_neg h0,if_neg h1,if_neg h2]
            exact atomCode_binder_fresh 0 _ _ chosen depth hr0 hna hnb

theorem positive_code_fresh (code : V) (h : 0 < code) (depth : V) :
    bindOneAt ℒₛₑₜ code depth (decode code) = decode code :=
  decode_binder_fresh code code depth h le_rfl

/-- A direct client of the freshness theorem; no target set axiom or GEN rule
is assumed. This does not yet construct the internal Collection instance. -/
theorem decoded_positive_vacuity (T : SetTheory) [T.Δ₁] (code : V) (h : 0 < code) :
    Provable T (decode (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wim code
      (_root_.SetTheory.BusyBeaver.ZFC.ArithmeticCode254.wal code code))) :=
  decoded_vacuity_of_bindOne T code code (positive_code_fresh code h 0)

end LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254
