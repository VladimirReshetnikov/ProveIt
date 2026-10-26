import DiophantineConsistency.Carrier65

/-!
# Exact ordinary perturbation of the native rank

MF below is the source high-mask port: Carrier65 already includes its single
beta shift. The F increment is an ordinary equality supplied explicitly,
not a consequence of a congruence or an assertion of safe digit mutation.
-/

namespace DiophantineConsistency.NativeRankVariation

set_option Elab.async false
set_option maxRecDepth 10000

section Ring
variable {R : Type*} [CommRing R]

/-- Rank in the explicit window coordinates, retaining the source MF port. -/
def windowRank (q C F MC MF J : R) : R :=
  (q*(q-F)-C)*(q^2-1)+(MC+q*MF)*J

/-- The positive controller step, when its integer sign hypotheses hold.
D is an arbitrary increment coefficient, not the unrelated Pell block D. -/
def rankGamma (q A D : R) : R := D*(q^2-1)*(1+q*A)

/-- Exact binding to the actual fourteen-variable arithmetic front. -/
theorem core_rank (p : Fin 4 → R) (v : Fin 14 → R) :
    (Carrier65.core p v).rank =
      windowRank (Carrier65.core p v).q (Carrier65.core p v).C (v 1) (p 2) (p 3) (v 0) := by
  rw [Carrier65.rank_shape]
  have hC : (Carrier65.core p v).C = (Carrier65.core p v).q-v 1-v 2 := rfl
  rw [hC]
  unfold windowRank
  ring

/-- The whole rank identity uses ordinary C and F increments over any
commutative ring, without division, congruence, or positivity assumptions. -/
theorem rank_variation (q C F MC MF J A δ : R) :
    windowRank q (C+δ) (F+A*δ) MC MF J =
      windowRank q C F MC MF J-δ*(q^2-1)*(1+q*A) := by
  unfold windowRank
  ring

/-- A positional increment yields exactly -Gamma times its place value. -/
theorem rank_power_variation (q C F MC MF J A D B : R) (j : ℕ) :
    windowRank q (C+D*B^j) (F+A*(D*B^j)) MC MF J =
      windowRank q C F MC MF J-rankGamma q A D*B^j := by
  rw [rank_variation]
  unfold rankGamma
  ring

/-- Adapter for two actual fronts with the same ports and fixed q,J.
All changed-field equalities are explicit; existence of such a mutation is
not asserted by this algebraic lemma. -/
theorem core_rank_variation (p : Fin 4 → R) (v v' : Fin 14 → R) (A δ : R)
    (hq : (Carrier65.core p v').q = (Carrier65.core p v).q)
    (hJ : v' 0 = v 0)
    (hC : (Carrier65.core p v').C = (Carrier65.core p v).C+δ)
    (hF : v' 1 = v 1+A*δ) :
    (Carrier65.core p v').rank = (Carrier65.core p v).rank-
      δ*((Carrier65.core p v).q^2-1)*(1+(Carrier65.core p v).q*A) := by
  rw [core_rank p v',hq,hJ,hC,hF,rank_variation,← core_rank p v]

theorem core_rank_power_variation (p : Fin 4 → R) (v v' : Fin 14 → R)
    (A D B : R) (j : ℕ)
    (hq : (Carrier65.core p v').q = (Carrier65.core p v).q)
    (hJ : v' 0 = v 0)
    (hC : (Carrier65.core p v').C = (Carrier65.core p v).C+D*B^j)
    (hF : v' 1 = v 1+A*(D*B^j)) :
    (Carrier65.core p v').rank = (Carrier65.core p v).rank-
      rankGamma (Carrier65.core p v).q A D*B^j := by
  rw [core_rank p v',hq,hJ,hC,hF,rank_power_variation,← core_rank p v]

/-- At q=1 the variable part disappears, so strict decrease cannot follow. -/
theorem rankGamma_one (A D : R) : rankGamma 1 A D = 0 := by simp [rankGamma]

theorem rank_variation_one (C F MC MF J A δ : R) :
    windowRank 1 (C+δ) (F+A*δ) MC MF J = windowRank 1 C F MC MF J := by
  simp [windowRank]

end Ring

/-- Every factor of Gamma is strictly positive at the stated integer inputs. -/
theorem rankGamma_pos (q A D : ℤ) (hq : 1 < q) (hA : 0 ≤ A) (hD : 0 < D) :
    0 < rankGamma q A D := by
  have hq0 : 0 ≤ q := by omega
  have hs : 0 < q^2-1 := by nlinarith
  have hqa : 0 ≤ q*A := mul_nonneg hq0 hA
  exact mul_pos (mul_pos hD hs) (by omega)

/-- Positive ordinary increments strictly decrease the rank. No positivity
of the old/new rank, window entries, or mask ports is needed. -/
theorem rank_strict_decrease (q C F MC MF J A δ : ℤ)
    (hq : 1 < q) (hA : 0 ≤ A) (hδ : 0 < δ) :
    windowRank q (C+δ) (F+A*δ) MC MF J < windowRank q C F MC MF J := by
  have hg := rankGamma_pos q A δ hq hA hδ
  rw [rank_variation]
  change 0 < δ*(q^2-1)*(1+q*A) at hg
  omega

theorem core_rank_strict_decrease (p : Fin 4 → ℤ) (v v' : Fin 14 → ℤ) (A δ : ℤ)
    (hq : (Carrier65.core p v').q = (Carrier65.core p v).q)
    (hJ : v' 0 = v 0)
    (hC : (Carrier65.core p v').C = (Carrier65.core p v).C+δ)
    (hF : v' 1 = v 1+A*δ)
    (hql : 1 < (Carrier65.core p v).q) (hA : 0 ≤ A) (hδ : 0 < δ) :
    (Carrier65.core p v').rank < (Carrier65.core p v).rank := by
  rw [core_rank p v',hq,hJ,hC,hF,core_rank p v]
  exact rank_strict_decrease _ _ _ _ _ _ A δ hql hA hδ

end DiophantineConsistency.NativeRankVariation
