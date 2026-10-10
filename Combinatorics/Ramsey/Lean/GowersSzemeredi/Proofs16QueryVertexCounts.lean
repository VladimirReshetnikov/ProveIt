import GowersSzemeredi.Proofs16ResizedProgressionSums
import GowersSzemeredi.Proofs16PurificationMassBudget

/-! Every vertex of the sixteenth shrinking participates in a quadratic
family of parent queries. Sparse bad queries therefore leave few vertices
without any good query, including all repeated-index exceptions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def anchoredProgressionQuery {N : Nat} (x y z : ZMod N) : Fin 4 → ZMod N := ![x,y,z,x-y+z]

def progressionQueryBadVertices {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (Bad : Finset (Fin 4 → ZMod N)) : Finset (ZMod N) :=
  (centeredProgressionShrink Q 16).carrier.filter fun x =>
    ∀ q ∈ progressionAdditiveQuadruples Q.carrier, q 0=x → q ∈ Bad

/-- Two thirty-second-box points complete every sixteenth-box vertex to
a parent additive quadruple. -/
theorem anchored_progression_query_mem {N : Nat} [NeZero N]
    (Q : CenteredProgression N) {x y z : ZMod N}
    (hx : x ∈ (centeredProgressionShrink Q 16).carrier)
    (hy : y ∈ (centeredProgressionShrink Q 32).carrier)
    (hz : z ∈ (centeredProgressionShrink Q 32).carrier) :
    anchoredProgressionQuery x y z ∈ progressionAdditiveQuadruples Q.carrier := by
  have hlast : x-y+z ∈ (centeredProgressionShrink Q 8).carrier := by
    have hsum := centered_progression_translated_sum_mem Q (fun i => Q.radius i/32)
      (fun i => Q.radius i/16) (fun i => Q.radius i/8) (fun i => by omega) x ![-y,z] hx
      (by intro j; fin_cases j
          · exact cyclic_centered_progression_neg_mem _ hy
          · exact hz)
    have heq : x+(∑ j : Fin 2, (![-y,z] : Fin 2 → ZMod N) j) = x-y+z := by
      rw [Fin.sum_univ_two]
      change x+(-y+z) = x-y+z
      ring
    rw [heq] at hsum
    exact hsum
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,?_⟩
  · intro i
    fin_cases i
    · exact centered_progression_shrink_subset Q 16 hx
    · exact centered_progression_shrink_subset Q 32 hy
    · exact centered_progression_shrink_subset Q 32 hz
    · exact centered_progression_shrink_subset Q 8 hlast
  · change x-y+z-(x-y+z)=0
    ring

/-- Query completion is injective in the vertex and its two free points. -/
theorem progression_bad_query_vertices_product {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (Bad : Finset (Fin 4 → ZMod N)) :
    (progressionQueryBadVertices Q Bad).card*((centeredProgressionShrink Q 32).carrier.card)^2 ≤ Bad.card := by
  let V := progressionQueryBadVertices Q Bad
  let B := (centeredProgressionShrink Q 32).carrier
  have hcount : (V ×ˢ B ×ˢ B).card ≤ Bad.card := by
    apply Finset.card_le_card_of_injOn (fun p => anchoredProgressionQuery p.1 p.2.1 p.2.2)
    · intro p hp
      obtain ⟨hpV,hprest⟩ := Finset.mem_product.mp hp
      obtain ⟨hpB1,hpB2⟩ := Finset.mem_product.mp hprest
      obtain ⟨hx,hbad⟩ := Finset.mem_filter.mp hpV
      exact hbad _ (anchored_progression_query_mem Q hx hpB1 hpB2) rfl
    · intro p hp q hq he
      have h0 : p.1=q.1 := by simpa [anchoredProgressionQuery] using congrFun he 0
      have h1 : p.2.1=q.2.1 := by simpa [anchoredProgressionQuery] using congrFun he 1
      have h2 : p.2.2=q.2.2 := by simpa [anchoredProgressionQuery] using congrFun he 2
      exact Prod.ext h0 (Prod.ext h1 h2)
  simpa only [V,B,Finset.card_product,pow_two,Nat.mul_assoc] using hcount

/-- A linear vertex-exception bound, with an explicit parent-density and
rank cost. No good-query participation is supplied as a separate premise. -/
theorem progression_bad_query_vertices_mass {N : Nat} [NeZero N]
    (Q : CenteredProgression N) (hQ : Q.Proper) (Bad : Finset (Fin 4 → ZMod N))
    {delta eta : Real} (hdelta : 0 < delta) (hmass : delta*N ≤ (Q.carrier.card : Real))
    (hbad : (Bad.card : Real) ≤ eta*(N : Real)^3) :
    ((progressionQueryBadVertices Q Bad).card : Real) ≤ eta*(4096 : Real)^Q.rank/delta^2*N := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  have hB := centered_progression_shrink_real_mass Q hQ (by decide : 0 < (32 : Nat))
  norm_num only [Nat.cast_ofNat] at hB
  have hBmass : delta*N/(64 : Real)^Q.rank ≤ ((centeredProgressionShrink Q 32).carrier.card : Real) :=
    (div_le_div_of_nonneg_right hmass (by positivity)).trans hB
  have hsq := pow_le_pow_left₀ (by positivity : (0 : Real) ≤ delta*N/(64 : Real)^Q.rank) hBmass 2
  have hcount : ((progressionQueryBadVertices Q Bad).card : Real)*
      (((centeredProgressionShrink Q 32).carrier.card : Real)^2) ≤ (Bad.card : Real) := by
    exact_mod_cast progression_bad_query_vertices_product Q Bad
  have hscaled := (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg (progressionQueryBadVertices Q Bad).card)).trans
    (hcount.trans hbad)
  have hdiv : ((progressionQueryBadVertices Q Bad).card : Real) ≤
      (eta*(N : Real)^3)/(delta*N/(64 : Real)^Q.rank)^2 := by
    exact (le_div_iff₀ (by positivity)).mpr hscaled
  have hpow : (4096 : Real)^Q.rank = ((64 : Real)^Q.rank)^2 := by
    calc (4096 : Real)^Q.rank = ((64 : Real)^2)^Q.rank := by norm_num
      _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm]
  have heq : (eta*(N : Real)^3)/(delta*N/(64 : Real)^Q.rank)^2 = eta*(4096 : Real)^Q.rank/delta^2*N := by
    rw [hpow]
    field_simp <;> ring
  simpa only [heq] using hdiv

end LeanProofs.GowersSzemeredi
