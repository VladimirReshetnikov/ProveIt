import GowersSzemeredi.Proofs16MixedColumnEnergy

/-! Mixed additive quadruples force an order-eight Freiman piece of one
map, even though the other three maps can be different. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def mixedColumnQuadruples {N : Nat} [NeZero N] (A : Finset (ZMod N))
    (f : Fin 4 → ZMod N → ZMod N) : Finset (Fin 4 → ZMod N) :=
  Finset.univ.filter fun q => q 0 ∈ A ∧ q 0-q 1 = q 2-q 3 ∧
    f 0 (q 0)-f 1 (q 1) = f 2 (q 2)-f 3 (q 3)

theorem mixedColumnQuadruples_card {N : Nat} [NeZero N] (A : Finset (ZMod N))
    (f : Fin 4 → ZMod N → ZMod N) :
    (mixedColumnQuadruples A f).card =
      mixedColumnEnergy A Finset.univ Finset.univ Finset.univ (f 0) (f 1) (f 2) (f 3) := by
  unfold mixedColumnQuadruples mixedColumnEnergy keyMatchingCount
  apply Finset.card_bij (fun q _ => ((q 0,q 1),(q 2,q 3)))
  · intro q hq
    obtain ⟨_,hA,hd,hv⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨by simpa only [Finset.mem_product,Finset.mem_univ,and_true,true_and] using hA,
      Prod.ext hd hv⟩
  · intro q _ q' _ he
    have hp := Prod.mk.inj he
    have h01 := Prod.mk.inj hp.1
    have h23 := Prod.mk.inj hp.2
    obtain ⟨h0,h1⟩ := h01
    obtain ⟨h2,h3⟩ := h23
    funext i
    fin_cases i <;> assumption
  · intro p hp
    obtain ⟨hm,he⟩ := Finset.mem_filter.mp hp
    have hA : p.1.1 ∈ A := (Finset.mem_product.mp (Finset.mem_product.mp hm).1).1
    have hkey := Prod.mk.inj he
    exact ⟨![p.1.1,p.1.2,p.2.1,p.2.2],Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hA,hkey.1,hkey.2⟩,rfl⟩

/-- Restricting the first coordinate to `A` produces energy on `A`.
The exponent four comes from two applications of Cauchy--Schwarz. -/
theorem mixed_quadruples_coordinate_energy {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N)) (hQ : Q ⊆ mixedColumnQuadruples A f)
    {delta : Real} (hdelta : 0 ≤ delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    delta^4*(N : Real)^3 ≤ phiAdditiveCount A (f 0) := by
  have hNat : Q.card^4 ≤ phiAdditiveCount A (f 0)*N^9 := by
    calc Q.card^4 ≤ (mixedColumnQuadruples A f).card^4 := Nat.pow_le_pow_left (Finset.card_le_card hQ) 4
      _ ≤ _ := by rw [mixedColumnQuadruples_card]; exact mixedColumnEnergy_coordinate_bound A _ _ _ _
  have hR : (Q.card : Real)^4 ≤ (phiAdditiveCount A (f 0) : Real)*(N : Real)^9 := by exact_mod_cast hNat
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ delta*(N : Real)^3) hcount 4
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  apply le_of_mul_le_mul_right (a := (N : Real)^9) _ (by positivity)
  calc delta^4*(N : Real)^3*(N : Real)^9 = (delta*(N : Real)^3)^4 := by ring
    _ ≤ (Q.card : Real)^4 := hpow
    _ ≤ _ := hR

/-- An unconditional Freiman extraction for one coordinate of a mixed
configuration family, using the existing Corollary 7.6 formalization. -/
theorem mixed_quadruples_freiman_piece {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (f : Fin 4 → ZMod N → ZMod N)
    (Q : Finset (Fin 4 → ZMod N)) (hQ : Q ⊆ mixedColumnQuadruples A f)
    {delta : Real} (hdelta : 0 < delta) (hcount : delta*(N : Real)^3 ≤ Q.card) :
    ∃ E ⊆ A, (2 : Real)^(-(1882 : Real))*(delta^4)^1164*N ≤ E.card ∧ FreimanHom 8 E (f 0) := by
  apply lineFreimanExtraction_eight N A (f 0) (delta^4) (by positivity)
  rw [energy_eq_phiAdditiveCount]
  exact mixed_quadruples_coordinate_energy A f Q hQ hdelta.le hcount

end LeanProofs.GowersSzemeredi
