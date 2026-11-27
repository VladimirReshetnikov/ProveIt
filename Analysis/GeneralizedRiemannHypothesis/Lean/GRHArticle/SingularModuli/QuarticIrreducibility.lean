import GRHArticle.SingularModuli.QuarticDiskCertificates
import Mathlib.Algebra.GCDMonoid.IntegrallyClosed
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Irreducibility certificates for the two explicit quartics

Modulo two and three respectively, exact polynomial Bézout identities
exclude every possible irreducible factor of degree one or two.
-/

namespace GRHArticle.SingularModuli

open Polynomial

private theorem dvd_frobenius_of_small_irreducible {q : ℕ} [Fact (Nat.Prime q)]
    {g : Polynomial (ZMod q)} (hg : Irreducible g) (hsmall : g.natDegree ≤ 2) :
    g ∣ X ^ (q ^ 2) - X := by
  classical
  letI : Fact (Irreducible g) := ⟨hg⟩
  have hpos : 0 < g.natDegree := by
    by_contra! h
    have hzero : g.natDegree = 0 := Nat.eq_zero_of_le_zero h
    exact hg.not_isUnit (isUnit_iff_degree_eq_zero.mpr (by
      rw [degree_eq_natDegree hg.ne_zero, hzero, Nat.cast_zero]))
  have hrank : Module.finrank (ZMod q) (AdjoinRoot g) = g.natDegree :=
    finrank_quotient_span_eq_natDegree
  letI : Module.Finite (ZMod q) (AdjoinRoot g) :=
    Module.finite_of_finrank_pos (by rw [hrank]; exact hpos)
  letI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod q)
  letI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = q ^ g.natDegree := by
    rw [Fintype.card_eq_nat_card, Module.natCard_eq_pow_finrank (K := ZMod q),
      hrank, ← Fintype.card_eq_nat_card, ZMod.card]
  have hpow : (AdjoinRoot.root g) ^ (q ^ 2) = AdjoinRoot.root g := by
    have hdegree : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
    rcases hdegree with h₁ | h₂
    · simpa only [hcard, h₁, pow_one] using FiniteField.pow_card_pow 2 (AdjoinRoot.root g)
    · simpa only [hcard, h₂] using FiniteField.pow_card (AdjoinRoot.root g)
  apply AdjoinRoot.mk_eq_zero.mp
  rw [map_sub, map_pow, AdjoinRoot.mk_X, hpow, sub_self]

private theorem irreducible_of_quartic_coprime_frobenius {q : ℕ} [Fact (Nat.Prime q)]
    {f : Polynomial (ZMod q)} (hm : f.Monic) (hd : f.natDegree = 4)
    (hcop : IsCoprime f (X ^ (q ^ 2) - X)) : Irreducible f := by
  refine irreducible_iff.mpr ⟨?_, ?_⟩
  · intro hu
    have hzero := isUnit_iff_degree_eq_zero.mp hu
    rw [degree_eq_natDegree hm.ne_zero, hd] at hzero
    norm_num at hzero
  intro a b hab
  by_contra! h
  have ha₀ : a ≠ 0 := fun h₀ ↦ hm.ne_zero (by simp [hab, h₀])
  have hb₀ : b ≠ 0 := fun h₀ ↦ hm.ne_zero (by simp [hab, h₀])
  have hdeg : a.natDegree + b.natDegree = 4 := by
    rw [← natDegree_mul ha₀ hb₀, ← hab, hd]
  have hex : ∃ u : Polynomial (ZMod q), u ∣ f ∧ u.natDegree ≤ 2 ∧ ¬IsUnit u ∧ u ≠ 0 := by
    by_cases ha : a.natDegree ≤ 2
    · exact ⟨a, ⟨b, hab⟩, ha, h.1, ha₀⟩
    · exact ⟨b, ⟨a, hab.trans (mul_comm _ _)⟩, by omega, h.2, hb₀⟩
  obtain ⟨u, huf, hu, huunit, hu₀⟩ := hex
  obtain ⟨v, hvirr, hvu⟩ := WfDvdMonoid.exists_irreducible_factor huunit hu₀
  have hv := (natDegree_le_of_dvd hvu hu₀).trans hu
  exact hvirr.not_isUnit
    (hcop.isUnit_of_dvd' (hvu.trans huf) (dvd_frobenius_of_small_irreducible hvirr hv))

private theorem isCoprime_mod_of_integer_bezout (q : ℕ) {f g u v w : Polynomial ℤ}
    (h : u * f + v * g = 1 + C (q : ℤ) * w) :
    IsCoprime (f.map (Int.castRingHom (ZMod q))) (g.map (Int.castRingHom (ZMod q))) := by
  refine ⟨u.map (Int.castRingHom (ZMod q)), v.map (Int.castRingHom (ZMod q)), ?_⟩
  have hmod := congrArg (Polynomial.map (Int.castRingHom (ZMod q))) h
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_one, Polynomial.map_C,
    Int.coe_castRingHom, Int.cast_natCast, ZMod.natCast_self, C_0, zero_mul, add_zero] using hmod

private noncomputable def quartic55Reduction : Polynomial ℤ := 1 + X + X^2 + X^3 + X^4

private noncomputable def quartic68Reduction : Polynomial ℤ := 2 + X + X^4

private theorem quartic55_reduction :
    quartic55Int.map (Int.castRingHom (ZMod 2)) =
      quartic55Reduction.map (Int.castRingHom (ZMod 2)) := by
  have h₀ : ((-18577989025032784359375 : ℤ) : ZMod 2) = 1 := by decide
  have h₁ : ((172576736359017890625 : ℤ) : ZMod 2) = 1 := by decide
  have h₂ : ((-20948398473375 : ℤ) : ZMod 2) = 1 := by decide
  have h₃ : ((13136684625 : ℤ) : ZMod 2) = 1 := by decide
  simp only [quartic55Int, quartic55Reduction, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_one,
    Int.coe_castRingHom, h₀, h₁, h₂, h₃, C_1, one_mul]

private theorem quartic68_reduction :
    quartic68Int.map (Int.castRingHom (ZMod 3)) =
      quartic68Reduction.map (Int.castRingHom (ZMod 3)) := by
  have h₀ : ((-2089297506304000000000000 : ℤ) : ZMod 3) = 2 := by decide
  have h₁ : ((-318507038720000000000 : ℤ) : ZMod 3) = 1 := by decide
  have h₂ : ((-75843692160000000 : ℤ) : ZMod 3) = 0 := by decide
  have h₃ : ((-178211040000 : ℤ) : ZMod 3) = 0 := by decide
  simp only [quartic68Int, quartic68Reduction, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, Polynomial.map_ofNat,
    Int.coe_castRingHom, h₀, h₁, h₂, h₃, C_ofNat, C_1, C_0, one_mul, zero_mul, add_zero]

private theorem quartic55_coprime :
    IsCoprime (quartic55Int.map (Int.castRingHom (ZMod 2))) (X ^ (2 ^ 2 : ℕ) - X) := by
  have h :
      (1 + X + X^3) * quartic55Reduction + (X^2 + X^3) * (X^4 - X) =
        1 + C (2 : ℤ) * (X + X^2 + X^3 + X^4 + X^5 + X^6 + X^7) := by
    unfold quartic55Reduction
    simp only [C_ofNat]
    ring
  rw [quartic55_reduction, show (2 ^ 2 : ℕ) = 4 by decide]
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using
    isCoprime_mod_of_integer_bezout 2 h

private theorem quartic68_coprime :
    IsCoprime (quartic68Int.map (Int.castRingHom (ZMod 3))) (X ^ (3 ^ 2 : ℕ) - X) := by
  have h :
      (2 + 2*X + X^2 + X^3 + 2*X^4 + X^5 + 2*X^6 + 2*X^8) * quartic68Reduction +
        (X + X^3) * (X^9 - X) =
        1 + C (3 : ℤ) *
          (1 + 2*X + X^2 + X^3 + 2*X^4 + 2*X^5 + 2*X^6 + X^7 + 2*X^8 +
            X^9 + X^10 + X^12) := by
    unfold quartic68Reduction
    simp only [C_ofNat]
    ring
  rw [quartic68_reduction, show (3 ^ 2 : ℕ) = 9 by decide]
  simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using
    isCoprime_mod_of_integer_bezout 3 h

/-- The explicit quartic at -55 is irreducible over the rationals. -/
theorem quartic55_irreducible : Irreducible quartic55 := by
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  let φ := Int.castRingHom (ZMod 2)
  have hmod := irreducible_of_quartic_coprime_frobenius (quartic55Int_monic.map φ)
    ((quartic55Int_monic.natDegree_map φ).trans quartic55Int_natDegree) quartic55_coprime
  exact quartic55Int_monic.irreducible_iff_irreducible_map_fraction_map.mp
    (Monic.irreducible_of_irreducible_map φ quartic55Int quartic55Int_monic hmod)

/-- The explicit quartic at -68 is irreducible over the rationals. -/
theorem quartic68_irreducible : Irreducible quartic68 := by
  letI : IsIntegrallyClosed ℤ := GCDMonoid.toIsIntegrallyClosed
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  let φ := Int.castRingHom (ZMod 3)
  have hmod := irreducible_of_quartic_coprime_frobenius (quartic68Int_monic.map φ)
    ((quartic68Int_monic.natDegree_map φ).trans quartic68Int_natDegree) quartic68_coprime
  exact quartic68Int_monic.irreducible_iff_irreducible_map_fraction_map.mp
    (Monic.irreducible_of_irreducible_map φ quartic68Int quartic68Int_monic hmod)

end GRHArticle.SingularModuli
