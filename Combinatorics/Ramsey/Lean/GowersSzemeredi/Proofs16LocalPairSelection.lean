import GowersSzemeredi.Proofs16LocalPairCounts
import GowersSzemeredi.Proofs16PropNineThree

/-! Choose pairs inside prescribed local anchor sets and retain source quadruples.
The bad-triple and twelve-tuple errors are charged against the local candidate
mass. All retained queries and pair endpoints keep their original identities. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

/-- Local selection with explicit vertex, repeat and twelve-tuple losses. -/
theorem exists_local_pair_selection {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (A : ZMod N → Finset (ZMod N))
    (Q : Finset (Fin 4 → ZMod N)) (Bad4 : Finset (ZMod N × ZMod N × ZMod N))
    (Bad12 : Finset (Fin 11 → ZMod N)) {lambda eps4 eps12 : Real} (hl : 0 < lambda)
    (hA : ∀ a ∈ S, lambda*(N : Real) ≤ ((A a).card : Real))
    (hQ : ∀ q ∈ Q, q 0+q 1 = q 2+q 3 ∧ ∀ j, q j ∈ S)
    (hBad4 : (Bad4.card : Real) ≤ eps4*(N : Real)^3)
    (hBad12 : (Bad12.card : Real) ≤ eps12*(N : Real)^11) :
    ∃ (X : Finset (ZMod N)) (c : ZMod N → ZMod N × ZMod N)
      (R : Finset (Fin 4 → ZMod N)),
      X = S \ localCandidateBadVertices S A Bad4 lambda ∧
      (∀ a ∈ X, c a ∈ localCandidateGoodPairs A Bad4 a) ∧
      (∀ q ∈ R, q ∈ Q ∧ Function.Injective q ∧ (∀ j, q j ∈ X) ∧
        twelveOf q (fun j => c (q j)) ∉ Bad12) ∧
      (Q.card : Real)-(8*eps4/lambda^2)*(N : Real)^3-6*(N : Real)^2-
        (16*eps12/lambda^8)*(N : Real)^3 ≤ R.card := by
  have hNR : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let V := localCandidateBadVertices S A Bad4 lambda
  let X := S \ V
  let Qv := Q.filter fun q => ∀ j, q j ∈ X
  let Qi := Qv.filter Function.Injective
  have hBadV : (V.card : Real) ≤ (2*eps4/lambda^2)*N :=
    local_bad_vertices_card_bound S A Bad4 hl hA hBad4
  have hbadQ : ((Q.filter fun q => ∃ j, q j ∈ V).card : Real) ≤
      (8*eps4/lambda^2)*(N : Real)^3 := by
    have hc : ((Q.filter fun q => ∃ j, q j ∈ V).card : Real) ≤ 4*V.card*(N : Real)^2 := by
      exact_mod_cast additive_quadruple_vertex_loss Q V (fun q hq => (hQ q hq).1)
    calc _ ≤ 4*V.card*(N : Real)^2 := hc
      _ ≤ 4*((2*eps4/lambda^2)*N)*(N : Real)^2 := by gcongr
      _ = _ := by ring
  have hQveq : Qv = Q.filter (fun q => ¬ ∃ j, q j ∈ V) := by
    ext q
    simp only [Qv,Finset.mem_filter,X,Finset.mem_sdiff]
    constructor
    · rintro ⟨hq,hx⟩
      exact ⟨hq,fun ⟨j,hj⟩ => (hx j).2 hj⟩
    · rintro ⟨hq,hnot⟩
      exact ⟨hq,fun j => ⟨(hQ q hq).2 j,fun hj => hnot ⟨j,hj⟩⟩⟩
  have hQvmass : (Q.card : Real)-(8*eps4/lambda^2)*(N : Real)^3 ≤ Qv.card := by
    have hs := Finset.card_filter_add_card_filter_not (s := Q) (fun q => ∃ j, q j ∈ V)
    rw [← hQveq] at hs
    have hsR : ((Q.filter fun q => ∃ j, q j ∈ V).card : Real)+Qv.card = Q.card := by exact_mod_cast hs
    linarith only [hsR,hbadQ]
  have hrepeat : ((Qv.filter fun q => ¬ Function.Injective q).card : Real) ≤ 6*(N : Real)^2 := by
    have hsub : (Qv.filter fun q => ¬ Function.Injective q) ⊆
        (additiveQuadruplesIn (Finset.univ : Finset (ZMod N))).filter fun q => ¬ Function.Injective q := by
      intro q hq
      obtain ⟨hqV,hn⟩ := Finset.mem_filter.mp hq
      have hqQ := (Finset.mem_filter.mp hqV).1
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,(hQ q hqQ).1,fun _ => Finset.mem_univ _⟩,hn⟩
    exact_mod_cast (Finset.card_le_card hsub).trans (additiveQuadruplesIn_repeated_card_le Finset.univ)
  have hQimass : (Q.card : Real)-(8*eps4/lambda^2)*(N : Real)^3-6*(N : Real)^2 ≤ Qi.card := by
    have hs := Finset.card_filter_add_card_filter_not (s := Qv) Function.Injective
    have hsR : (Qi.card : Real)+(Qv.filter fun q => ¬ Function.Injective q).card = Qv.card := by exact_mod_cast hs
    linarith only [hQvmass,hsR,hrepeat]
  let g : Real := (lambda*N)^2/2
  have hg : 0 < g := by dsimp only [g]; positivity
  let Choices : ZMod N → Finset (ZMod N × ZMod N) := fun a =>
    if a ∈ X then localCandidateGoodPairs A Bad4 a else {(0,0)}
  have hGood : ∀ a ∈ X, g ≤ ((localCandidateGoodPairs A Bad4 a).card : Real) := by
    intro a ha
    obtain ⟨haS,haV⟩ := Finset.mem_sdiff.mp ha
    exact local_good_pair_card_at_retained S A Bad4 lambda haS haV
  have hChoices : ∀ a, (Choices a).Nonempty := by
    intro a
    by_cases ha : a ∈ X
    · simp only [Choices,if_pos ha]
      exact Finset.card_pos.mp (by exact_mod_cast hg.trans_le (hGood a ha))
    · simp only [Choices,if_neg ha]
      exact Finset.singleton_nonempty _
  have hQi : ∀ q ∈ Qi, Function.Injective q ∧ q 0+q 1 = q 2+q 3 ∧ ∀ j, q j ∈ X := by
    intro q hq
    obtain ⟨hqV,hinj⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqQ,hx⟩ := Finset.mem_filter.mp hqV
    exact ⟨hinj,(hQ q hqQ).1,hx⟩
  have hprod : ∀ q ∈ Qi, g^4 ≤ ((∏ j : Fin 4, (Choices (q j)).card : Nat) : Real) := by
    intro q hq
    push_cast
    calc g^4 = ∏ _j : Fin 4, g := by simp [Fintype.card_fin]
      _ ≤ ∏ j : Fin 4, ((Choices (q j)).card : Real) := by
        apply Finset.prod_le_prod (fun _ _ => hg.le)
        intro j _
        have hj := (hQi q hq).2.2 j
        simpa only [Choices,if_pos hj] using hGood _ hj
  obtain ⟨c,hc,hfail⟩ := exists_pair_choice_few_bad Choices hChoices Qi
    (fun q hq => (hQi q hq).1) (fun q hq => (hQi q hq).2.1) Bad12 (pow_pos hg _) hprod
  have hfailBound : ((Qi.filter fun q => twelveOf q (fun j => c (q j)) ∈ Bad12).card : Real) ≤
      (16*eps12/lambda^8)*(N : Real)^3 := by
    calc _ ≤ (Bad12.card : Real)/g^4 := hfail
      _ ≤ (eps12*(N : Real)^11)/g^4 := div_le_div_of_nonneg_right hBad12 (pow_nonneg hg.le _)
      _ = _ := by dsimp only [g]; field_simp <;> ring
  let R := Qi.filter fun q => twelveOf q (fun j => c (q j)) ∉ Bad12
  refine ⟨X,c,R,rfl,?_,?_,?_⟩
  · intro a ha
    simpa only [Choices,if_pos ha] using hc a
  · intro q hq
    obtain ⟨hqI,hnb⟩ := Finset.mem_filter.mp hq
    have hh := hQi q hqI
    have hqQ := (Finset.mem_filter.mp (Finset.mem_filter.mp hqI).1).1
    exact ⟨hqQ,hh.1,hh.2.2,hnb⟩
  · have hs := Finset.card_filter_add_card_filter_not (s := Qi)
      (fun q => twelveOf q (fun j => c (q j)) ∈ Bad12)
    have hsR : ((Qi.filter fun q => twelveOf q (fun j => c (q j)) ∈ Bad12).card : Real)+R.card = Qi.card := by exact_mod_cast hs
    linarith only [hQimass,hsR,hfailBound]

end LeanProofs.GowersSzemeredi
