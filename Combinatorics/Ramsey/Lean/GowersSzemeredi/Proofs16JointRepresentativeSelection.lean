import GowersSzemeredi.Proofs16JointRepresentationEvents

/-! One global representative selection controls both selected tuple
failures and the mass of bad alternatives at every queried coordinate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def jointRepresentationQueryFailures {N : Nat} [NeZero N]
    (U : Finset (ZMod N)) (Q : Finset (Fin 4 → ZMod N))
    (f : ZMod N → FourRepresentationTuple N) (Bad : Finset (ColumnAnchorTuple N 15))
    (kappa : Real) : Finset (Fin 4 → ZMod N) :=
  Q.filter fun q => (fun j => f (q j)) ∈ jointBadRepresentationBlocks U q Bad kappa

/-- The joint selector retains at least half the uniform alternative mass
on every coordinate of every nonexceptional distinct-index query. -/
theorem exists_joint_progression_representatives {N : Nat} [NeZero N]
    (U C : Finset (ZMod N)) {kappa : Real} (hk : 0 < kappa) (hk1 : kappa ≤ 1)
    (hrep : ∀ x ∈ C, kappa*(N : Real)^3 ≤ (fourDifferenceRepresentations U x).card)
    (Q : Finset (Fin 4 → ZMod N))
    (hQ : ∀ q ∈ Q, (∀ j, q j ∈ C) ∧ Function.Injective q)
    (Bad : Finset (ColumnAnchorTuple N 15)) :
    ∃ f : ZMod N → FourRepresentationTuple N,
      (∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x) ∧
      ((jointRepresentationQueryFailures U Q f Bad kappa).card : Real) ≤
        9*(Bad.card : Real)/(kappa^5*(N : Real)^12) ∧
      ∀ q ∈ Q, q ∉ jointRepresentationQueryFailures U Q f Bad kappa →
        flattenFourRepresentations (fun j => f (q j)) ∉ Bad ∧
        ∀ i, kappa*(N : Real)^3/2 ≤ (((fourDifferenceRepresentations U (q i)).filter
          fun p => flattenFourRepresentations (Function.update (fun j => f (q j)) i p) ∉ Bad).card : Real) := by
  classical
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let F := progressionRepresentationChoiceSets U C
  have hF : ∀ x : ZMod N, (F x).Nonempty := by
    intro x
    by_cases hx : x ∈ C
    · have hpos : (0 : Real) < (fourDifferenceRepresentations U x).card :=
        (by positivity : (0 : Real) < kappa*(N : Real)^3).trans_le (hrep x hx)
      simpa [F,progressionRepresentationChoiceSets,hx] using
        Finset.card_pos.mp (by exact_mod_cast hpos)
    · simp [F,progressionRepresentationChoiceSets,hx]
  have hB : ∀ q ∈ Q, ∀ b ∈ jointBadRepresentationBlocks U q Bad kappa, ∀ j, b j ∈ F (q j) := by
    intro q hq b hb j
    have h := joint_bad_representation_blocks_valid U q Bad kappa hb j
    simpa only [F,progressionRepresentationChoiceSets,if_pos ((hQ q hq).1 j)] using h
  have hprod : ∀ q ∈ Q, kappa^4*(N : Real)^12 ≤ ((∏ j : Fin 4, (F (q j)).card) : Real) := by
    intro q hq
    have hp : (∏ _j : Fin 4, kappa*(N : Real)^3) ≤ ∏ j : Fin 4, ((F (q j)).card : Real) := by
      apply Finset.prod_le_prod (fun _ _ => by positivity)
      intro j hj
      simpa only [F,progressionRepresentationChoiceSets,if_pos ((hQ q hq).1 j)] using hrep (q j) ((hQ q hq).1 j)
    simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow,←pow_mul,Nat.cast_prod] using hp
  have hcoeff : 1+8/kappa ≤ 9/kappa := by
    apply (le_div_iff₀ hk).mpr
    have heq : (1+8/kappa)*kappa = kappa+8 := by field_simp <;> ring
    rw [heq]
    linarith
  have htotal : (∑ q ∈ Q, ((jointBadRepresentationBlocks U q Bad kappa).card : Real)) ≤
      (9/kappa)*(Bad.card : Real) :=
    (joint_bad_representation_blocks_total U Q Bad hk).trans
      (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _))
  obtain ⟨f,hf,hbad⟩ := exists_independent_choice_few_bad_queries F hF Q
    (fun q => jointBadRepresentationBlocks U q Bad kappa) (fun q hq => (hQ q hq).2) hB
    (by positivity : (0 : Real) < kappa^4*(N : Real)^12) hprod htotal
  have hvalid : ∀ x ∈ C, f x ∈ fourDifferenceRepresentations U x := by
    intro x hx
    simpa only [F,progressionRepresentationChoiceSets,if_pos hx] using Fintype.mem_piFinset.mp hf x
  have hbound : ((jointRepresentationQueryFailures U Q f Bad kappa).card : Real) ≤
      9*(Bad.card : Real)/(kappa^5*(N : Real)^12) := by
    have heq : ((9/kappa)*(Bad.card : Real))/(kappa^4*(N : Real)^12) =
        9*(Bad.card : Real)/(kappa^5*(N : Real)^12) := by field_simp <;> ring
    simpa only [jointRepresentationQueryFailures,heq] using hbad
  refine ⟨f,hvalid,hbound,?_⟩
  intro q hq hnot
  apply good_joint_representation_block U q (fun j => f (q j)) Bad
    (fun j => hvalid _ ((hQ q hq).1 j)) (fun j => hrep _ ((hQ q hq).1 j))
  intro hblock
  exact hnot (Finset.mem_filter.mpr ⟨hq,hblock⟩)

end LeanProofs.GowersSzemeredi
