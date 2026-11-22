import IPRADerivations.Analysis.GammaEulerConstantName
import IPRADerivations.Analysis.GammaMeshRobinLogBridge

/-!
# Actual finite harmonic intervals on positive rational arguments

The actual normalized value is H_(Qa)-H_(Qb), with a computed factorial
horizon Q(a+b). Existing native reciprocal rectangle refinement derives
its exact finite 1/Q change under any positive numerical mesh refinement.
No completed logarithm or output relation is an input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalHarmonicInterval

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.MeshChange (S_denom)
open Products (fact)
open GammaEulerMesh (factorial_positive factorial_quotient)
open RationalValueBounds (upper radius radius_of_upper)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def numerator (a b Q L : PTm n) : ZT n := ⟨S (Q*a) (fact L), S (Q*b) (fact L)⟩
def common (a b Q L : PTm n) : PTm n := RationalIntegerNormalization.normalize (numerator a b Q L) (fact L)
def horizon (a b Q : PTm n) : PTm n := Q*(a+b)
def interval (a b Q : PTm n) : PTm n := common a b Q (horizon a b Q)
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (a b Q L : PTm n) :
    (numerator a b Q L).subst σ = numerator (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) (Syn.subst σ L) := by simp [numerator,ZT.subst,S]
@[simp] theorem subst_common {m : ℕ} (σ : Fin n → PTm m) (a b Q L : PTm n) :
    Syn.subst σ (common a b Q L) = common (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) (Syn.subst σ L) := by simp [common]
@[simp] theorem subst_horizon {m : ℕ} (σ : Fin n → PTm m) (a b Q : PTm n) :
    Syn.subst σ (horizon a b Q) = horizon (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) := by simp [horizon]
@[simp] theorem subst_interval {m : ℕ} (σ : Fin n → PTm m) (a b Q : PTm n) :
    Syn.subst σ (interval a b Q) = interval (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) := by simp [interval]

theorem common_value (a b Q L : PTm n) : Γ ⊢[PRAAx] RationalArithmetic.represents
    (common a b Q L) (numerator a b Q L) (fact L) :=
  RationalIntegerNormalization.normalize_preserves_value _ _ (factorial_positive L)
theorem common_canonical (a b Q L : PTm n) : Γ ⊢[PRAAx] RationalNormalForm.wellFormed (common a b Q L) :=
  RationalNormalForm.normalize_well_formed _ _ (factorial_positive L)
theorem left_horizon (a b Q : PTm n) : Γ ⊢[PRAAx] le (Q*a) (horizon a b Q) :=
  le_congr (.eqRefl _) (by unfold horizon; ipra_ring) (le_add_right (Q*a) (Q*b))
theorem right_horizon (a b Q : PTm n) : Γ ⊢[PRAAx] le (Q*b) (horizon a b Q) :=
  le_congr (.eqRefl _) (by unfold horizon; ipra_ring) (le_add_left (Q*b) (Q*a))

theorem at_common (a b Q L : PTm n) (hL : Γ ⊢[PRAAx] le (horizon a b Q) L) :
    Γ ⊢[PRAAx] common a b Q L ≐ interval a b Q := by
  have left := natEq (S_denom (left_horizon a b Q) hL)
  have right := natEq (S_denom (right_horizon a b Q) hL)
  apply RationalFiniteSum.canonical_equal (common a b Q L) (interval a b Q)
    (numerator a b Q L) (numerator a b Q (horizon a b Q)) (fact L) (fact (horizon a b Q))
    (common_canonical a b Q L) (common_canonical a b Q (horizon a b Q)) (common_value a b Q L) (common_value a b Q (horizon a b Q))
    (factorial_positive L) (factorial_positive (horizon a b Q))
  apply ZT.derive (u := numerator a b Q L*ZT.ofNat (fact (horizon a b Q)))
    (v := numerator a b Q (horizon a b Q)*ZT.ofNat (fact L))
  simp only [ZT.toZ_mul,ZT.toZ_ofNat]
  simp only [numerator,ZT.toZ]
  ipra_simps
  linear_combination left-right

/-- Native fine/coarse rectangle bounds on one original factorial scale. -/
theorem ordered_refinement (a b Q E L : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (hba : Γ ⊢[PRAAx] le b a) (hQ : Γ ⊢[PRAAx] le one Q) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le (E*(Q*a)) L) : Γ ⊢[PRAAx]
    le (S (E*(Q*a)) (fact L)+S (Q*b) (fact L))
      (S (E*(Q*b)) (fact L)+S (Q*a) (fact L)+quo (fact L) Q) ⋏
    le (S (E*(Q*b)) (fact L)+S (Q*a) (fact L))
      (S (E*(Q*a)) (fact L)+S (Q*b) (fact L)+quo (fact L) Q) := by
  let N := Q*b
  let M := Q*a
  let F := fact L
  have hn := RationalAlgebra.positive_product hQ hb
  have hnm : Γ ⊢[PRAAx] le N M := AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl Q) hba
  have hm := le_trans hn hnm
  have qL : Γ ⊢[PRAAx] le Q L := by
    have qn : Γ ⊢[PRAAx] le Q N := by dsimp [N]; ipra_le 𝔞 Q*sl hb
    have me : Γ ⊢[PRAAx] le M (E*M) := by ipra_le 𝔞 M*sl hE
    exact le_trans qn (le_trans hnm (le_trans me hL))
  have old := GammaEulerMesh.synchronous_cleared N M E L hn hnm hE hL
  have gap : Γ ⊢[PRAAx] le (monus M N) (Q*a*b) := by
    have small : Γ ⊢[PRAAx] le (monus M N) M :=
      le_congr (.eqRefl _) (eq_add_of_le hnm).eqSymm (le_add_left (monus M N) N)
    have large : Γ ⊢[PRAAx] le M (Q*a*b) := by dsimp [M]; ipra_le 𝔞 (Q*a)*sl hb
    exact le_trans small large
  have quotient := factorial_quotient Q L hQ qL
  have cancellation : Γ ⊢[PRAAx] (N*M)*quo F Q ≐ (Q*a*b)*F :=
    (by dsimp [N,M]; ipra_ring : Γ ⊢[PRAAx] (N*M)*quo F Q ≐ (Q*a*b)*(Q*quo F Q)).eqTrans
      (congrMul (.eqRefl _) quotient)
  have tail : Γ ⊢[PRAAx] le (monus M N*F) ((N*M)*quo F Q) :=
    le_congr (.eqRefl _) cancellation.eqSymm (mul_le_mul_right F gap)
  have added := add_le_add_right (N*M*(S M F+S (E*N) F)) tail
  have increased : Γ ⊢[PRAAx] le (N*M*(S N F+S (E*M) F)) (N*M*(S M F+S (E*N) F+quo F Q)) :=
    le_trans old.andE₂ (le_congr (by ipra_ring) (by ipra_ring) added)
  have upper : Γ ⊢[PRAAx] le (S N F+S (E*M) F) (S M F+S (E*N) F+quo F Q) :=
    RationalValueBounds.positive_cancel (RationalAlgebra.positive_product hn hm) increased
  have lower := le_trans old.andE₁ (le_add_right (S N F+S (E*M) F) (quo F Q))
  exact .andI (le_congr (by ipra_ring) (by ipra_ring) upper)
    (le_congr (by ipra_ring) (by ipra_ring) lower)


theorem refinement_bounds (a b Q E L : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le one Q) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le (E*horizon a b Q) L) : Γ ⊢[PRAAx]
    le (S (E*(Q*a)) (fact L)+S (Q*b) (fact L))
      (S (E*(Q*b)) (fact L)+S (Q*a) (fact L)+quo (fact L) Q) ⋏
    le (S (E*(Q*b)) (fact L)+S (Q*a) (fact L))
      (S (E*(Q*a)) (fact L)+S (Q*b) (fact L)+quo (fact L) Q) := by
  have boundA : Γ ⊢[PRAAx] le (E*(Q*a)) L :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E (left_horizon a b Q))) hL
  have boundB : Γ ⊢[PRAAx] le (E*(Q*b)) L :=
    le_trans (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E (right_horizon a b Q))) hL
  refine .orE (le_total b a) ?_ ?_
  · exact ordered_refinement a b Q E L hb.wk Prf.hyp0 hQ.wk hE.wk boundA.wk
  · have swapped := ordered_refinement b a Q E L ha.wk Prf.hyp0 hQ.wk hE.wk boundB.wk
    exact .andI swapped.andE₂ swapped.andE₁

theorem common_refinement (a b Q E L : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le one Q) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le (E*horizon a b Q) L) : Γ ⊢[PRAAx]
    radius (common a b (E*Q) L) (common a b Q L) one Q := by
  have qh : Γ ⊢[PRAAx] le Q (horizon a b Q) := by
    have first : Γ ⊢[PRAAx] le Q (Q*a) := by ipra_le 𝔞 Q*sl ha
    exact le_trans first (left_horizon a b Q)
  have old : Γ ⊢[PRAAx] le (horizon a b Q) (E*horizon a b Q) := by ipra_le 𝔞 (horizon a b Q)*sl hE
  have qL := le_trans qh (le_trans old hL)
  have bounds := refinement_bounds a b Q E L ha hb hQ hE hL
  have left : Γ ⊢[PRAAx] S ((E*Q)*a) (fact L) ≐ S (E*(Q*a)) (fact L) :=
    congrAp2 (sumF hB) (by ipra_ring) (.eqRefl _)
  have right : Γ ⊢[PRAAx] S ((E*Q)*b) (fact L) ≐ S (E*(Q*b)) (fact L) :=
    congrAp2 (sumF hB) (by ipra_ring) (.eqRefl _)
  have first : Γ ⊢[PRAAx] le
      ((numerator a b (E*Q) L).pos+(numerator a b Q L).neg)
      ((numerator a b (E*Q) L).neg+(numerator a b Q L).pos+quo (fact L) Q) :=
    le_congr (congrAdd left (.eqRefl _)).eqSymm (congrAdd (congrAdd right (.eqRefl _)) (.eqRefl _)).eqSymm bounds.andE₁
  have second : Γ ⊢[PRAAx] le
      ((numerator a b Q L).pos+(numerator a b (E*Q) L).neg)
      ((numerator a b Q L).neg+(numerator a b (E*Q) L).pos+quo (fact L) Q) :=
    le_congr ((congrAdd (.eqRefl _) right).eqTrans (add_comm _ _)).eqSymm
      ((congrAdd (congrAdd (.eqRefl _) left) (.eqRefl _)).eqTrans
        (by ipra_ring : Γ ⊢[PRAAx] S (Q*b) (fact L)+S (E*(Q*a)) (fact L)+quo (fact L) Q ≐
          S (E*(Q*a)) (fact L)+S (Q*b) (fact L)+quo (fact L) Q)).eqSymm bounds.andE₂
  exact radius_of_upper _ _ _ _
    (GammaEulerConstantName.common_quotient_upper _ _ (numerator a b (E*Q) L) (numerator a b Q L) L Q hQ qL
      (common_value a b (E*Q) L) (common_value a b Q L) first)
    (GammaEulerConstantName.common_quotient_upper _ _ (numerator a b Q L) (numerator a b (E*Q) L) L Q hQ qL
      (common_value a b Q L) (common_value a b (E*Q) L) second)

/-- A genuine finite refinement estimate for every internal positive
mesh, either sign of the interval, and independently normalized outputs. -/
theorem refinement (a b Q E : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hQ : Γ ⊢[PRAAx] le one Q) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    radius (interval a b (E*Q)) (interval a b Q) one Q := by
  let L := E*horizon a b Q
  have coarse : Γ ⊢[PRAAx] le (horizon a b Q) L := by dsimp [L]; ipra_le 𝔞 (horizon a b Q)*sl hE
  have fine : Γ ⊢[PRAAx] le (horizon a b (E*Q)) L := le_of_eq_add (d := zero) (by dsimp [horizon,L]; ipra_ring)
  exact RationalValueBounds.radius_congr (at_common a b (E*Q) L fine) (at_common a b Q L coarse) (.eqRefl _) (.eqRefl _)
    (common_refinement a b Q E L ha hb hQ hE (le_refl _))


private theorem normalize_congr (p q D r s E : PTm n) (hp : Γ ⊢[PRAAx] p ≐ r)
    (hq : Γ ⊢[PRAAx] q ≐ s) (hD : Γ ⊢[PRAAx] D ≐ E) : Γ ⊢[PRAAx]
    RationalIntegerNormalization.normalize (⟨p,q⟩ : ZT n) D ≐ RationalIntegerNormalization.normalize (⟨r,s⟩ : ZT n) E :=
  (RationalIntegerNormalization.normalize_at p q D).eqSymm.eqTrans
    ((congrAp3 RationalIntegerNormalization.normalizeF hp hq hD).eqTrans (RationalIntegerNormalization.normalize_at r s E))

/-- Cross multiplication of the original positive fractions identifies
both endpoints and the actual factorial horizon at their common mesh. -/
theorem equal_ratio_refined (a b c d Q : PTm n) (h : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    interval a b (d*Q) ≐ interval c d (b*Q) := by
  have left : Γ ⊢[PRAAx] (d*Q)*a ≐ (b*Q)*c :=
    (by ipra_ring : Γ ⊢[PRAAx] (d*Q)*a ≐ Q*(a*d)).eqTrans
      ((congrMul (.eqRefl _) h).eqTrans (by ipra_ring))
  have right : Γ ⊢[PRAAx] (d*Q)*b ≐ (b*Q)*d := by ipra_ring
  have hor : Γ ⊢[PRAAx] horizon a b (d*Q) ≐ horizon c d (b*Q) :=
    (by unfold horizon; ipra_ring : Γ ⊢[PRAAx] horizon a b (d*Q) ≐ (d*Q)*a+(d*Q)*b).eqTrans
      ((congrAdd left right).eqTrans (by unfold horizon; ipra_ring))
  have den : Γ ⊢[PRAAx] fact (horizon a b (d*Q)) ≐ fact (horizon c d (b*Q)) := congrAp2 factF hor (.eqRefl zero)
  exact normalize_congr _ _ _ _ _ _ (congrAp2 (sumF hB) left den) (congrAp2 (sumF hB) right den) den

/-- Equal numerical fractions have genuinely close finite harmonic
intervals, from two actual common refinements, before taking any name. -/
theorem equal_ratio_finite (a b c d Q : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (hQ : Γ ⊢[PRAAx] le one Q) (h : Γ ⊢[PRAAx] a*d ≐ b*c) : Γ ⊢[PRAAx]
    radius (interval a b Q) (interval c d Q) two Q := by
  have left := RationalValueBounds.radius_symmetric _ _ _ _ (refinement a b Q d ha hb hQ hd)
  have right := RationalValueBounds.radius_congr (equal_ratio_refined a b c d Q h).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (refinement c d Q b hc hd hQ hb)
  have total := RationalValueBounds.radius_triangle _ _ _ one Q one Q left right
  exact RationalValueBounds.radius_mono _ _ _ _ two Q (RationalAlgebra.positive_product hQ hQ) total
    (le_of_eq_add (d := zero) (by ipra_ring))

def input (a b Q E : PTm n) : Fm PTm n := le one a ⋏ (le one b ⋏ (le one Q ⋏ le one E))
def output (a b Q E : PTm n) : PTm n := pairT (interval a b (E*Q)) (pairT (interval a b Q) Q)
def outputF : PR 4 := PTm.toPR (output (var 0) (var 1) (var 2) (var 3))
def run (a b Q E : PTm n) : PTm n := PTm.app outputF ![a,b,Q,E]
@[simp] theorem subst_output {m : ℕ} (σ : Fin n → PTm m) (a b Q E : PTm n) :
    Syn.subst σ (output a b Q E) = output (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ Q) (Syn.subst σ E) := by simp [output]
theorem program_at (a b Q E : PTm n) : Γ ⊢[PRAAx] run a b Q E ≐ output a b Q E := by
  simpa [run,outputF] using toPR_eq (Γ := Γ) (output (var 0) (var 1) (var 2) (var 3) : PTm 4) ![a,b,Q,E]
theorem returned_fine (a b Q E : PTm n) : Γ ⊢[PRAAx] fstT (run a b Q E) ≐ interval a b (E*Q) :=
  (congrFst (program_at a b Q E)).eqTrans (fst_pair _ _)
theorem returned_coarse (a b Q E : PTm n) : Γ ⊢[PRAAx] fstT (sndT (run a b Q E)) ≐ interval a b Q :=
  ((congrFst (congrSnd (program_at a b Q E))).eqTrans (congrFst (snd_pair _ _))).eqTrans (fst_pair _ _)
theorem returned_denominator (a b Q E : PTm n) : Γ ⊢[PRAAx] sndT (sndT (run a b Q E)) ≐ Q :=
  ((congrSnd (congrSnd (program_at a b Q E))).eqTrans (congrSnd (snd_pair _ _))).eqTrans (snd_pair _ _)

theorem actual_harmonic_interval_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (input (var 0) (var 1) (var 2) (var 3) ⟶ radius (interval (var 0) (var 1) (var 3*var 2))
      (interval (var 0) (var 1) (var 2)) one (var 2)) :=
  closeUniv 4 (.impI (refinement _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂))
theorem actual_equal_ratio_common_refinement_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (var 0*var 3 ≐ var 1*var 2 ⟶ interval (var 0) (var 1) (var 3*var 4) ≐ interval (var 2) (var 3) (var 1*var 4)) :=
  closeUniv 5 (.impI (equal_ratio_refined _ _ _ _ _ Prf.hyp0))
theorem actual_equal_ratio_finite_interval_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ (le one (var 1) ⋏ (le one (var 2) ⋏ (le one (var 3) ⋏ le one (var 4))))) ⟶
      var 0*var 3 ≐ var 1*var 2 ⟶ radius (interval (var 0) (var 1) (var 4)) (interval (var 2) (var 3) (var 4)) two (var 4)) :=
  closeUniv 5 (.impI (.impI (equal_ratio_finite _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₂ Prf.hyp0)))
theorem actual_harmonic_interval_program_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (run (var 0) (var 1) (var 2) (var 3) ≐ output (var 0) (var 1) (var 2) (var 3)) := closeUniv 4 (program_at _ _ _ _)

end LeanProofs.IPRA.Analysis.RationalHarmonicInterval
