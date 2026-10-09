import GowersSzemeredi.Proofs16MixedCoordinateRetention

/-! Dense additive configurations have dense coordinate projections. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem additive_quadruples_coordinate_card_le {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (E : Finset (ZMod N)) (i : Fin 4)
    (hadd : ∀ q ∈ Q, q 0-q 1 = q 2-q 3) (hE : ∀ q ∈ Q, q i ∈ E) :
    Q.card ≤ E.card*N^2 := by
  let e := mixedCoordinatePermutation i
  let enc (q : Fin 4 → ZMod N) := (q (e 0),q (e 1),q (e 2))
  have hcard : Q.card ≤ (E ×ˢ ((Finset.univ : Finset (ZMod N)) ×ˢ (Finset.univ : Finset (ZMod N)))).card := by
    apply Finset.card_le_card_of_injOn enc
    · intro q hq
      simp only [Finset.mem_coe,enc,Finset.mem_product,Finset.mem_univ,and_true,e,mixedCoordinatePermutation_zero]
      exact hE q hq
    · intro q hq p hp he
      have he' : q (e 0) = p (e 0) ∧ q (e 1) = p (e 1) ∧ q (e 2) = p (e 2) := by
        simpa only [enc,Prod.mk.injEq] using he
      have hq' := mixed_relation_reindex q (hadd q hq) i
      have hp' := mixed_relation_reindex p (hadd p hp) i
      have h3 : q (e 3) = p (e 3) := by
        change q (e 0)-q (e 1) = q (e 2)-q (e 3) at hq'
        change p (e 0)-p (e 1) = p (e 2)-p (e 3) at hp'
        linear_combination hq'-hp'-he'.1+he'.2.1+he'.2.2
      funext j
      obtain ⟨l,rfl⟩ := e.surjective j
      fin_cases l
      · exact he'.1
      · exact he'.2.1
      · exact he'.2.2
      · exact h3
  simpa only [Finset.card_product,Finset.card_univ,ZMod.card,pow_two] using hcard

theorem additive_quadruples_coordinate_density {N : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (E : Finset (ZMod N)) (i : Fin 4)
    (hadd : ∀ q ∈ Q, q 0-q 1 = q 2-q 3) (hE : ∀ q ∈ Q, q i ∈ E)
    {delta : Real} (hQ : delta*(N : Real)^3 ≤ Q.card) : delta*N ≤ (E.card : Real) := by
  have hc : (Q.card : Real) ≤ (E.card : Real)*(N : Real)^2 := by
    exact_mod_cast additive_quadruples_coordinate_card_le Q E i hadd hE
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)^2) _ (by positivity)
  calc delta*N*(N : Real)^2 = delta*(N : Real)^3 := by ring
    _ ≤ (Q.card : Real) := hQ
    _ ≤ _ := hc

end LeanProofs.GowersSzemeredi
