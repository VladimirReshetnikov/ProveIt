import GowersSzemeredi.Proofs16FinalPairChoice
import GowersSzemeredi.Proofs16AdditiveQuadrupleProjection

/-! Local candidate pairs and relative pruning bounds.
The candidate density is measured inside the prescribed anchor family,
without an ambient half-column assumption. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical
open scoped BigOperators

def localCandidateGoodPairs {N : Nat} (A : ZMod N → Finset (ZMod N))
    (Bad : Finset (ZMod N × ZMod N × ZMod N)) (a : ZMod N) : Finset (ZMod N × ZMod N) :=
  ((A a) ×ˢ (A a)).filter fun p => (p.1,p.2,a) ∉ Bad

def localCandidateRejectedPairs {N : Nat} (A : ZMod N → Finset (ZMod N))
    (Bad : Finset (ZMod N × ZMod N × ZMod N)) (a : ZMod N) : Finset (ZMod N × ZMod N) :=
  ((A a) ×ˢ (A a)).filter fun p => (p.1,p.2,a) ∈ Bad

def localCandidateBadVertices {N : Nat} (S : Finset (ZMod N))
    (A : ZMod N → Finset (ZMod N)) (Bad : Finset (ZMod N × ZMod N × ZMod N))
    (lambda : Real) : Finset (ZMod N) :=
  S.filter fun a => ((localCandidateGoodPairs A Bad a).card : Real) < (lambda*N)^2/2

theorem local_candidate_pair_split {N : Nat} (A : ZMod N → Finset (ZMod N))
    (Bad : Finset (ZMod N × ZMod N × ZMod N)) (a : ZMod N) :
    (localCandidateGoodPairs A Bad a).card+(localCandidateRejectedPairs A Bad a).card = (A a).card^2 := by
  have h := Finset.card_filter_add_card_filter_not (s := (A a) ×ˢ (A a))
    (fun p => (p.1,p.2,a) ∈ Bad)
  simpa only [localCandidateGoodPairs,localCandidateRejectedPairs,Finset.card_product,pow_two,Nat.add_comm] using h

/-- Rejected local pairs inject into the original bad triples across all indices. -/
theorem local_rejected_pair_sum_le {N : Nat} (S : Finset (ZMod N))
    (A : ZMod N → Finset (ZMod N)) (Bad : Finset (ZMod N × ZMod N × ZMod N)) :
    (∑ a ∈ S, (localCandidateRejectedPairs A Bad a).card) ≤ Bad.card := by
  rw [← Finset.card_sigma]
  apply Finset.card_le_card_of_injOn (fun p => (p.2.1,p.2.2,p.1))
  · intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2
  · intro p hp q hq he
    have hfirst : p.1 = q.1 := congrArg (fun t : ZMod N × ZMod N × ZMod N => t.2.2) he
    have hpair : p.2 = q.2 := Prod.ext
      (congrArg (fun t : ZMod N × ZMod N × ZMod N => t.1) he)
      (congrArg (fun t : ZMod N × ZMod N × ZMod N => t.2.1) he)
    exact Sigma.ext hfirst (heq_of_eq hpair)

/-- Heavy local failures consume the corresponding mass of bad triples. -/
theorem local_bad_vertices_weighted_bound {N : Nat}
    (S : Finset (ZMod N)) (A : ZMod N → Finset (ZMod N))
    (Bad : Finset (ZMod N × ZMod N × ZMod N)) {lambda : Real} (hl : 0 ≤ lambda)
    (hA : ∀ a ∈ S, lambda*(N : Real) ≤ ((A a).card : Real)) :
    ((lambda*N)^2/2)*(localCandidateBadVertices S A Bad lambda).card ≤ (Bad.card : Real) := by
  let V := localCandidateBadVertices S A Bad lambda
  have hreject : ∀ a ∈ V, (lambda*N)^2/2 ≤ ((localCandidateRejectedPairs A Bad a).card : Real) := by
    intro a ha
    obtain ⟨haS,haBad⟩ := Finset.mem_filter.mp ha
    have hpow : (lambda*N)^2 ≤ ((A a).card : Real)^2 := pow_le_pow_left₀ (by positivity) (hA a haS) 2
    have hsplit : ((localCandidateGoodPairs A Bad a).card : Real)+
        (localCandidateRejectedPairs A Bad a).card = ((A a).card : Real)^2 := by
      exact_mod_cast local_candidate_pair_split A Bad a
    linarith only [hpow,hsplit,haBad]
  calc ((lambda*N)^2/2)*V.card = ∑ _a ∈ V, (lambda*N)^2/2 := by simp; ring
    _ ≤ ∑ a ∈ V, ((localCandidateRejectedPairs A Bad a).card : Real) :=
      Finset.sum_le_sum hreject
    _ ≤ Bad.card := by exact_mod_cast local_rejected_pair_sum_le V A Bad

/-- The local vertex loss is relative to the prescribed anchor density. -/
theorem local_bad_vertices_card_bound {N : Nat} [NeZero N]
    (S : Finset (ZMod N)) (A : ZMod N → Finset (ZMod N))
    (Bad : Finset (ZMod N × ZMod N × ZMod N)) {lambda eps : Real} (hl : 0 < lambda)
    (hA : ∀ a ∈ S, lambda*(N : Real) ≤ ((A a).card : Real))
    (hBad : (Bad.card : Real) ≤ eps*(N : Real)^3) :
    ((localCandidateBadVertices S A Bad lambda).card : Real) ≤ (2*eps/lambda^2)*N := by
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hw := (local_bad_vertices_weighted_bound S A Bad hl.le hA).trans hBad
  have hscale : 0 < (lambda*(N : Real))^2/2 := by positivity
  calc ((localCandidateBadVertices S A Bad lambda).card : Real) =
      (((lambda*N)^2/2)*(localCandidateBadVertices S A Bad lambda).card)/((lambda*N)^2/2) := by field_simp
    _ ≤ (eps*(N : Real)^3)/((lambda*N)^2/2) := div_le_div_of_nonneg_right hw hscale.le
    _ = (2*eps/lambda^2)*N := by field_simp

/-- A retained vertex has enough actual local good pairs. -/
theorem local_good_pair_card_at_retained {N : Nat} (S : Finset (ZMod N))
    (A : ZMod N → Finset (ZMod N)) (Bad : Finset (ZMod N × ZMod N × ZMod N))
    (lambda : Real) {a : ZMod N} (ha : a ∈ S) (hret : a ∉ localCandidateBadVertices S A Bad lambda) :
    (lambda*N)^2/2 ≤ ((localCandidateGoodPairs A Bad a).card : Real) := by
  by_contra h
  exact hret (Finset.mem_filter.mpr ⟨ha,lt_of_not_ge h⟩)

/-- Deleting vertices costs at most four projection fibres per vertex. -/
theorem additive_quadruple_vertex_loss {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (V : Finset (ZMod N))
    (hQ : ∀ q ∈ Q, q 0+q 1 = q 2+q 3) :
    (Q.filter fun q => ∃ j, q j ∈ V).card ≤ 4*V.card*N^2 := by
  let Qj := fun j : Fin 4 => Q.filter fun q => q j ∈ V
  have hsub : (Q.filter fun q => ∃ j, q j ∈ V) ⊆ Finset.univ.biUnion Qj := by
    intro q hq
    obtain ⟨hqQ,j,hj⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hqQ,hj⟩⟩
  have hbound : ∀ j, (Qj j).card ≤ V.card*N^2 := by
    intro j
    have hrow : anchorRowSupport (Qj j) j ⊆ V := by
      intro x hx
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hq).2
    exact (additive_quadruples_row_card_le (Qj j) (fun q hq => hQ q (Finset.mem_filter.mp hq).1) j).trans
      (Nat.mul_le_mul_right _ (Finset.card_le_card hrow))
  calc (Q.filter fun q => ∃ j, q j ∈ V).card ≤ (Finset.univ.biUnion Qj).card := Finset.card_le_card hsub
    _ ≤ ∑ j : Fin 4, (Qj j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 4, V.card*N^2 := Finset.sum_le_sum fun j _ => hbound j
    _ = _ := by simp [Fintype.card_fin]; ring

end LeanProofs.GowersSzemeredi
