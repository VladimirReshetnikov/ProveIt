import GowersSzemeredi.Proofs16PopularKernelStep

/-! Pigeonhole a finite collection of bad relations, then refine the Bohr
domain using a popular constant fibre. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A positive fraction of pairs covered by finitely many nontrivial
relations gives a quantitative strict relation-subspace increment. -/
theorem strict_relation_kernel_of_bad_relation_cover {N : Nat} [NeZero N] [Fact N.Prime]
    {κ H : Type*} [Fintype κ] [DecidableEq H]
    (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    (R : Finset H) (hR : R.Nonempty) (w v : H → κ → ZMod N) (z : H → ZMod N)
    (hbad : ∀ r ∈ R, w r ∉ relationSubmodule (bohr Gamma sigma) L ∨
      v r ∉ relationSubmodule (bohr Gamma sigma) L)
    (P : Finset (ZMod N × ZMod N)) (hP : P ⊆ C ×ˢ C)
    (hcover : ∀ p ∈ P, ∃ r ∈ R, (∑ j, w r j * L j p.1) + (∑ j, v r j * L j p.2) = z r)
    {theta : Real} (htheta : 0 < theta) (hpairs : theta * (C.card : Real)^2 ≤ P.card) :
    ∃ S : Finset (ZMod N),
      (S.card : Real) ≤ 16 * ((theta / R.card) * C.card / N) ^ (-(2 : Real)) ∧
      bohr S (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S (1 / (8 * Real.pi))) L := by
  let Wit := fun (p : ZMod N × ZMod N) (r : H) =>
    (∑ j, w r j * L j p.1) + (∑ j, v r j * L j p.2) = z r
  obtain ⟨r, hr, hpop⟩ := exists_popular_witness P R Wit hR hcover
  have hRpos : (0 : Real) < R.card := by exact_mod_cast hR.card_pos
  apply strict_relation_kernel_of_many_pairs_either Gamma hsigma L hL (w r) (v r) (z r)
    (hbad r hr) C hCne hC (div_pos htheta hRpos)
  have hsub : P.filter (fun p => Wit p r) ⊆ (C ×ˢ C).filter (fun p => Wit p r) :=
    Finset.filter_subset_filter _ hP
  have hcard : ((P.filter fun p => Wit p r).card : Real) ≤
      ((C ×ˢ C).filter fun p => Wit p r).card := by exact_mod_cast Finset.card_le_card hsub
  have hle := hpairs.trans (hpop.trans (mul_le_mul_of_nonneg_left hcard hRpos.le))
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hRpos).mpr
  nlinarith only [hle]

/-- The same increment with a specified upper bound on the witness count,
so subsequent iteration estimates need not track the exact finite set. -/
theorem strict_relation_kernel_of_bad_relation_cover_bound {N : Nat} [NeZero N] [Fact N.Prime]
    {κ H : Type*} [Fintype κ] [DecidableEq H]
    (Gamma : Finset (ZMod N)) {sigma : Real} (hsigma : 0 ≤ sigma)
    (L : κ → ZMod N → ZMod N) (hL : ∀ j, IsFreimanLinearOn (bohr Gamma sigma) (L j))
    (C : Finset (ZMod N)) (hCne : C.Nonempty) (hC : C ⊆ bohr Gamma (sigma / 4))
    (R : Finset H) (hR : R.Nonempty) (w v : H → κ → ZMod N) (z : H → ZMod N)
    (hbad : ∀ r ∈ R, w r ∉ relationSubmodule (bohr Gamma sigma) L ∨
      v r ∉ relationSubmodule (bohr Gamma sigma) L)
    (P : Finset (ZMod N × ZMod N)) (hP : P ⊆ C ×ˢ C)
    (hcover : ∀ p ∈ P, ∃ r ∈ R, (∑ j, w r j * L j p.1) + (∑ j, v r j * L j p.2) = z r)
    {theta M : Real} (htheta : 0 < theta) (hpairs : theta * (C.card : Real)^2 ≤ P.card)
    (hM : (R.card : Real) ≤ M) :
    ∃ S : Finset (ZMod N),
      (S.card : Real) ≤ 16 * ((theta / M) * C.card / N) ^ (-(2 : Real)) ∧
      bohr S (1 / (8 * Real.pi)) ⊆ bohr Gamma sigma ∧
      relationSubmodule (bohr Gamma sigma) L < relationSubmodule (bohr S (1 / (8 * Real.pi))) L := by
  obtain ⟨S, hS, hsub, hstrict⟩ := strict_relation_kernel_of_bad_relation_cover
    Gamma hsigma L hL C hCne hC R hR w v z hbad P hP hcover htheta hpairs
  have hRpos : (0 : Real) < R.card := by exact_mod_cast hR.card_pos
  have hMpos := hRpos.trans_le hM
  have hCpos : (0 : Real) < C.card := by exact_mod_cast hCne.card_pos
  have hN : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  refine ⟨S, hS.trans ?_, hsub, hstrict⟩
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (by norm_num)
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left htheta.le hRpos hM) hCpos.le) hN.le

end LeanProofs.GowersSzemeredi
