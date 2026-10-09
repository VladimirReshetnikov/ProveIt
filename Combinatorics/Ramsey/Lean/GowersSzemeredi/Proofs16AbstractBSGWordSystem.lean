import GowersSzemeredi.Proofs16AbstractBSGCore
import GowersSzemeredi.Proofs16AbstractBSGBridging

/-! The abstract BSG core with all bounded-length compatible word families.
The weak-transitivity budget is explicit and positive. Its dependence on
word length is confined to the finite cubic density recurrence. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped Pointwise

/-- A positive cutoff valid for every word length at most `k+1`. -/
def relationWordCutoff (lambda eta : Real) : Nat → Real
  | 0 => lambda / 2
  | k+1 => min (relationWordCutoff lambda eta k)
      (thresholdColumnWordDensity lambda eta (k+1) / 2)

theorem relationWordCutoff_pos {lambda eta : Real} (hl : 0 < lambda) (he : 0 < eta)
    (k : Nat) : 0 < relationWordCutoff lambda eta k := by
  induction k with
  | zero => simpa [relationWordCutoff] using half_pos hl
  | succ k ih =>
    exact lt_min ih (half_pos (thresholdColumnWordDensity_pos hl he (k+1)))

theorem relationWordCutoff_le_density (lambda eta : Real) (k j : Nat) (hj : j ≤ k) :
    relationWordCutoff lambda eta k ≤ thresholdColumnWordDensity lambda eta j / 2 := by
  induction k with
  | zero =>
    have hj0 : j = 0 := by omega
    subst j
    exact le_rfl
  | succ k ih =>
    by_cases heq : j = k+1
    · subst j; exact min_le_right _ _
    · exact (min_le_left _ _).trans (ih (by omega))

/-- Claim 4.4 is exactly threshold richness for the word-gluing relation. -/
theorem threshold_relation_richness_of_walks {N : Nat} [NeZero N]
    {A X B : Finset (ZMod N)} (hAX : A ⊆ X) (hBA : B ⊆ A) (hX : X.Nonempty)
    {P : Finset (ZMod N × ZMod N)} (hPA : P ⊆ A ×ˢ A)
    (Q : Nat → ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (h20 : ∀ p ∈ P, ∀ q ∈ P, p.1-p.2 = q.1-q.2 → Q 4 p.1 p.2 q.1 q.2)
    (hS3 : ∀ i a b c d, Q i a b c d → Q i a c b d)
    {c' K eta beta : Real} (hc' : 0 < c') (hK : 0 < K) (he : 0 ≤ eta) (hb : 0 ≤ beta)
    (hWT : ∀ i j, i + j ≤ 16 → ∀ a b c d, c' * X.card ≤ (((A ×ˢ A).filter fun p =>
      Q i a b p.1 p.2 ∧ Q j p.1 p.2 c d).card : Real) → Q (i+j) a b c d)
    (hdoub : ((X-X).card : Real) ≤ K * X.card)
    (hwalk : ∀ u ∈ B, ∀ v ∈ B, eta * (X.card : Real)^3 ≤ (walkSet P X u v).card)
    (hsmall : 16*c' ≤ (beta*beta*eta)^2 / K^4) (hXN : X = Finset.univ) :
    ThresholdRelationRichness B (Q 16) beta (eta / K^2) := by
  intro U V hU hV b1 b2 hb1 hb2 hUc hVc
  have hb10 : 0 ≤ b1 := hb.trans hb1
  have hb20 : 0 ≤ b2 := hb.trans hb2
  have hsmall' : 16*c' ≤ (b1*b2*eta)^2 / K^4 := by
    apply hsmall.trans
    gcongr
  have hcount := claim_4_4 hAX hBA hU hV hX hPA Q h20 hS3 hc' hWT hK (by
      convert hdoub using 1
      congr 2
      ext z
      simp only [Finset.mem_sub]) he hwalk
    hb10 hb20 (by simpa [hXN] using hUc) (by simpa [hXN] using hVc) hsmall'
  have hcard := mixedRelationQuadruples_card U V (Q 16)
  have hcount' : (b1*b2*eta)^2 / K^4 / 2 * (X.card : Real)^3 ≤
      (mixedRelationQuadruples U V (Q 16)).card := by
    convert hcount using 1
    apply congrArg Nat.cast
    convert hcard using 1
    congr 1
    ext q
    simp only [Finset.mem_filter]
  clear hcount

  have hsize : X.card = N := by simp [hXN]
  rw [hsize] at hcount'
  convert hcount' using 1
  field_simp

/-- The base triple density retained by pruning. -/
def absBsgWordLambda (c K : Real) : Real := absBsgKappa c K / 4
/-- The mixed-quadruple density coefficient, including doubling losses. -/
def absBsgWordEta (c K : Real) : Real := absBsgEta c K / K^2
/-- The smallest subset density used by the word induction. -/
def absBsgWordBeta (c K : Real) (k : Nat) : Real :=
  relationWordCutoff (absBsgWordLambda c K) (absBsgWordEta c K) k
/-- Sufficient weak-transitivity parameter for the core and all word lengths. -/
def absBsgWordTransitivity (c K : Real) (k : Nat) : Real :=
  min (absBsgDelta c K ^ 5 / (8*16384))
    (min (absBsgKappa c K / 16)
      ((absBsgWordBeta c K k * absBsgWordBeta c K k * absBsgEta c K)^2 / (16*K^4)))

theorem absBsgWord_parameters_pos {c K : Real} (hc : 0 < c) (hK : 0 < K) (k : Nat) :
    0 < absBsgWordLambda c K ∧ 0 < absBsgWordEta c K ∧
      0 < absBsgWordBeta c K k ∧ 0 < absBsgWordTransitivity c K k := by
  have hl : 0 < absBsgWordLambda c K := by
    unfold absBsgWordLambda absBsgKappa absBsgEps absBsgEta absBsgDelta2 absBsgDelta
    positivity
  have he : 0 < absBsgWordEta c K := by
    unfold absBsgWordEta absBsgEta absBsgDelta2 absBsgDelta
    positivity
  have hb : 0 < absBsgWordBeta c K k := relationWordCutoff_pos hl he k
  refine ⟨hl, he, hb, ?_⟩
  unfold absBsgWordTransitivity
  apply lt_min
  · unfold absBsgDelta; positivity
  · apply lt_min
    · unfold absBsgKappa absBsgEps absBsgEta absBsgDelta2 absBsgDelta; positivity
    · have heta : 0 < absBsgEta c K := by unfold absBsgEta absBsgDelta2 absBsgDelta; positivity
      positivity

/-- **Abstract BSG for every bounded-length tuple of cyclic-group anchors.**
The output retains both the dense index sets and the actual recursive
representation families. The relation level is `16` with four-walks. -/
theorem abstract_bsg_word_system {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 2 < N) (A : Finset (ZMod N))
    (Q : Nat → ZMod N → ZMod N → ZMod N → ZMod N → Prop)
    (hS1 : ∀ a b c d, Q 1 a b c d → Q 1 c d a b)
    (hS2 : ∀ a b c d, Q 4 a b c d → Q 4 b a d c)
    (hS3 : ∀ i a b c d, Q i a b c d → Q i a c b d)
    {c c' K : Real} (hc : 0 < c) (hc' : 0 < c') (hK : 0 < K)
    (hWT : ∀ i j, i + j ≤ 16 → ∀ a b d e, c' * N ≤ (((A ×ˢ A).filter fun p =>
      Q i a b p.1 p.2 ∧ Q j p.1 p.2 d e).card : Real) → Q (i+j) a b d e)
    (hdoub : (((Finset.univ : Finset (ZMod N)) - Finset.univ).card : Real) ≤ K*N)
    (hgood : c*(N : Real)^3 ≤ ∑ d ∈
      (Finset.univ : Finset (ZMod N)) - Finset.univ, (diffGoodCount A (Q 1) d : Real))
    (hcN : 4 ≤ c*N) (k : Nat) (hsmall : c' ≤ absBsgWordTransitivity c K k) :
    ∃ B B' : Finset (ZMod N), B' ⊆ B ∧ B ⊆ A ∧
      absBsgEps c K*N ≤ (B'.card : Real) ∧
      ThresholdRelationRichness B (Q 16) (absBsgWordBeta c K k) (absBsgWordEta c K) ∧
      ∀ a : ZMod N, ∀ as : List (ZMod N), (∀ x ∈ a::as, x ∈ B') → as.length ≤ k →
        thresholdColumnWordDensity (absBsgWordLambda c K) (absBsgWordEta c K) as.length *
          (N : Real)^(3*as.length+2) ≤ (relationWordRepresentations B (Q 16) (a::as)).card := by
  have h2 : ∀ d : ZMod N, d+d = 0 → d = 0 := by
    intro d hd
    have htwo : (2 : ZMod N) ≠ 0 := by
      intro h
      exact (Nat.not_dvd_of_pos_of_lt (by omega) hN) ((ZMod.natCast_eq_zero_iff 2 N).mp h)
    have he : (2 : ZMod N)*d = 0 := by linear_combination hd
    exact (mul_eq_zero.mp he).resolve_left htwo
  have hp := absBsgWord_parameters_pos hc hK k
  have hkap : 0 < absBsgKappa c K := by
    have := hp.1; unfold absBsgWordLambda at this; linarith
  have hs1 : 8*c' ≤ absBsgDelta c K^5/16384 := by
    have := hsmall.trans (show absBsgWordTransitivity c K k ≤
      absBsgDelta c K^5/(8*16384) from min_le_left _ _)
    linarith
  have hs2 : 16*c' ≤ absBsgKappa c K := by
    have h := hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
    linarith
  obtain ⟨P, B, B', hPA, h20, hBA, hB'B, hsize, hwalk, hrich⟩ :=
    abstract_bsg_rich_core h2 (Finset.subset_univ A) (Finset.univ_nonempty)
      Q hS1 hS2 hS3 hc hc'
      (by simpa using hWT) hK (by simpa using hdoub) (by simpa using hgood)
      (by simpa using hcN) hs1 hs2 (show absBsgWordLambda c K < absBsgKappa c K/2 by
        unfold absBsgWordLambda; linarith)
  have hs3 : 16*c' ≤ (absBsgWordBeta c K k*absBsgWordBeta c K k*absBsgEta c K)^2/K^4 := by
    have h := hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
    have hK4 : 0 < K^4 := by positivity
    rw [le_div_iff₀ (by positivity)] at h
    rw [le_div_iff₀ hK4]
    nlinarith
  have hrichness := threshold_relation_richness_of_walks (Finset.subset_univ A) hBA
    Finset.univ_nonempty hPA Q h20 hS3 hc' hK (by unfold absBsgEta absBsgDelta2 absBsgDelta; positivity) hp.2.2.1.le
    (by simpa using hWT) (by simpa using hdoub) hwalk hs3 rfl
  refine ⟨B, B', hB'B, hBA, by simpa using hsize, hrichness, ?_⟩
  intro a as has hlen
  apply relation_word_representations_count B B' (Q 16) hp.1 hp.2.1
    (fun a ha => ?_) hrichness k (fun j hj => relationWordCutoff_le_density _ _ k j hj)
    a as has hlen
  rw [relationTripleRepresentations_card]
  simpa using hrich a ha

end LeanProofs.GowersSzemeredi
