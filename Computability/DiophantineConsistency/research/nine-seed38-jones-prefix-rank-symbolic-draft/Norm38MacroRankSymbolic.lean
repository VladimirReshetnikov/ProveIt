import DiophantineConsistency.Norm38MacroRankValuesOther

/-! Candidate d11 symbolic rankCode value; finite sums remain symbolic. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroRankSymbolic
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroPrefixGroup05 Norm38MacroRankComposition Norm38MacroRankValues ExecutableJones

theorem d11_rank_symbolic {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d11.values a (Fin.last 10) =
      NinePolynomial.rankCode (1 : R) (indexZ seed 0 : R) (base a)
        (∑ k ∈ codingStar 38 4,
          ((indexZ seed 0 : R) + (pCoefficient seed k : R)) *
            (base a ^ (5 : Nat)) ^ ((5 ^ 39 : Nat) - codingExpo 38 4 k))
        (a ⟨1, by decide⟩ + ((1 : Int) : R))
        (∑ j ∈ Finset.range 38, (base a ^ (5 : Nat)) ^ (5 ^ (j + 1)))
        (((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat))
        ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat))
        (base a ^ (5 : Nat) - ((2 : Int) : R) * (indexZ seed 0 : R))
        (∑ j ∈ Finset.range (4 * (5 ^ 39 : Nat)), (base a ^ (5 : Nat)) ^ j) := by
  rw [d11_rankCode]
  change NinePolynomial.rankCode (1 : R) (indexZ seed 0 : R)
        (d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 7).castSucc.castSucc))
        (d10.values a ((Fin.last 5).castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 8).castSucc))
        (d10.values a ((Fin.last 6).castSucc.castSucc.castSucc)) = _
  rw [d10_b_value, d10_e_value, d10_g_value, d10_ell_value,
    d10_N, d10_q, d10_theta_value, d10_lambda_value]

#print axioms d11_rank_symbolic
end DiophantineConsistency.Norm38MacroRankSymbolic
