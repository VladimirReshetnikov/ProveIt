import DiophantineConsistency.Norm38MacroRankRaw

/-! Candidate application of the checked d10 preservation cuts. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Norm38MacroRankCarry
open Norm38MacroLanguage Norm38MacroPrefixes Norm38MacroPrefixGroup01
  Norm38MacroPrefixGroup05 Norm38MacroPrefixGroup06 Norm38MacroRankRaw ExecutableJones

theorem d11_rank_carried {R : Type*} [CommRing R] (a : Fin 9 → R) :
    d11.values a (Fin.last 10) =
      rankRaw (indexZ seed 0 : R)
        (d9.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d9.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        ((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat))
        (((base a ^ (5 : Nat)) ^ (5 ^ 39 : Nat)) ^ (16 : Nat))
        (d5.values a (Fin.last 4)) (d6.values a (Fin.last 5))
        (d7.values a (Fin.last 6)) (d8.values a (Fin.last 7))
        (d9.values a (Fin.last 8)) := by
  rw [d11_rank_raw]
  change rankRaw (indexZ seed 0 : R)
        (d10.values a ((Fin.last 0).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 1).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 2).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 3).castSucc.castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 4).castSucc.castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 5).castSucc.castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 6).castSucc.castSucc.castSucc))
        (d10.values a ((Fin.last 7).castSucc.castSucc))
        (d10.values a ((Fin.last 8).castSucc)) = _
  rw [d10_b_carry, d10_B_carry, d10_q, d10_N, d10_e_carry,
    d10_ell_carry, d10_lambda_carry, d10_g_carry, d10_theta_carry]

#print axioms d11_rank_carried
end DiophantineConsistency.Norm38MacroRankCarry
