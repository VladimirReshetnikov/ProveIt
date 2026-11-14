import PA194PAeqSequent
import PA194PAeqNegation
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194PAeqTermBlueprint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
variable (T : Theory ℒₒᵣ) [T.Δ₁] (U : Theory PA194PAeq.language) [U.Δ₁]

theorem derivation_transport (haxiom : ∀ p : V, p∈T.Δ₁Class → Provable U (formulaCode 0 p)) {d : V}
    (hd : Derivation T d) : Derivable U (sequentCode (fstIdx d)) := by
  have ha := haxiom
  apply Derivation.induction1 𝚺 (P:=fun d : V=>Derivable U (sequentCode (fstIdx d))) (by definability) hd
  · intro s hs p hp hn
    simp only [fstIdx_axL]
    apply Derivable.em (sequent_valid hs) (formulaCode 0 p) (sequent_member hp)
    simpa only [formulaCode_neg 0 (hs p hp).isUFormula] using sequent_member hn
  · intro s hs hv
    simp only [fstIdx_verumIntro]
    exact Derivable.verum (sequent_valid hs) (by simpa only [formulaCode_verum] using sequent_member hv)
  · intro s hs p q dp dq hpq hdp hdq ihp ihq
    have hp : IsFormula ℒₒᵣ p := (IsSemiformula.and.mp (hs _ hpq)).1
    have hq : IsFormula ℒₒᵣ q := (IsSemiformula.and.mp (hs _ hpq)).2
    simp only [fstIdx_andIntro]
    apply Derivable.and_m (p:=formulaCode 0 p) (q:=formulaCode 0 q)
    · simpa only [formulaCode_and 0 p q hp.isUFormula hq.isUFormula] using sequent_member hpq
    · simpa only [hdp.1,sequent_insert] using ihp
    · simpa only [hdq.1,sequent_insert] using ihq
  · intro s hs p q dp hpq hdp ih
    have hp : IsFormula ℒₒᵣ p := (IsSemiformula.or.mp (hs _ hpq)).1
    have hq : IsFormula ℒₒᵣ q := (IsSemiformula.or.mp (hs _ hpq)).2
    simp only [fstIdx_orIntro]
    apply Derivable.or_m (p:=formulaCode 0 p) (q:=formulaCode 0 q)
    · simpa only [formulaCode_or 0 p q hp.isUFormula hq.isUFormula] using sequent_member hpq
    · simpa only [hdp.1,sequent_insert] using ih
  · intro s hs p dp hp hdp ih
    have hp' : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
    simp only [fstIdx_allIntro]
    apply Derivable.all_m (p:=formulaCode 0 p)
    · simpa only [formulaCode_all 0 p hp'.isUFormula] using sequent_member hp
    · simpa only [hdp.1,sequent_insert,sequent_shift hs,formulaCode_free 0 hp'] using ih
  · intro s hs p t dp hp ht hdp ih
    have hp' : IsSemiformula ℒₒᵣ 1 p := by simpa using hs _ hp
    simp only [fstIdx_exsIntro]
    apply Derivable.ex_m (p:=formulaCode 0 p) (t:=termCode t)
    · simpa only [formulaCode_exs 0 p hp'.isUFormula] using sequent_member hp
    · exact termCode_valid ht
    · simpa only [hdp.1,sequent_insert,formulaCode_substs1 0 hp' ht] using ih
  · intro s hs dp hsub hdp ih
    simp only [fstIdx_wkRule]
    exact Derivable.wk (sequent_valid hs) (sequent_mono hsub) ih
  · intro s hs dp he hdp ih
    simp only [fstIdx_shiftRule,he,sequent_shift hdp.isFormulaSet]
    exact Derivable.shift ih
  · intro s hs p d₁ d₂ h₁ h₂ ih₁ ih₂
    have hp : IsFormula ℒₒᵣ p := h₁.isFormulaSet p (by simp)
    simp only [fstIdx_cutRule]
    apply Derivable.cut (formulaCode 0 p)
    · simpa only [h₁.1,sequent_insert] using ih₁
    · simpa only [h₂.1,sequent_insert,formulaCode_neg 0 hp.isUFormula] using ih₂
  · intro s hs p hp hpa
    simp only [fstIdx_axm]
    apply Derivable.wk (sequent_valid hs) (s':={formulaCode 0 p})
    · intro q hq; have : q=formulaCode 0 p := by simpa using hq
      subst q; exact sequent_member hp
    · exact ha p hpa

theorem derivationOf_transport (haxiom : ∀ p : V, p∈T.Δ₁Class → Provable U (formulaCode 0 p)) {d s : V}
    (hd : DerivationOf T d s) : Derivable U (sequentCode s) := by
  simpa only [hd.1] using derivation_transport T U haxiom hd.2

theorem provable_transport (haxiom : ∀ p : V, p∈T.Δ₁Class → Provable U (formulaCode 0 p)) {p : V}
    (hp : Provable T p) : Provable U (formulaCode 0 p) := by
  obtain ⟨d,hd⟩:=hp
  simpa only [sequent_singleton,Provable,Proof,Derivable] using derivationOf_transport T U haxiom hd

theorem refutation_transport (haxiom : ∀ p : V, p∈T.Δ₁Class → Provable U (formulaCode 0 p))
    (hp : Provable T (qqFalsum : V)) : Provable U (qqFalsum : V) := by
  simpa only [formulaCode_falsum] using provable_transport T U haxiom hp


#print axioms derivation_transport
#print axioms provable_transport
#print axioms refutation_transport
end PA194PAeqTermBlueprint
