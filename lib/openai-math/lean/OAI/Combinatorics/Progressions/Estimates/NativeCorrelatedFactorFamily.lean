/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import OAI.Combinatorics.Progressions.Estimates.NativeSharedFrozenCorrelations

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
  {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (w : σ → ℕ)

theorem polynomialOrbit_coefficient_grid_value (q : ℕ)
    (g : F.realification.PolynomialOrbit w) (hg : CoefficientGrid (b.baseChange ℝ) q g.log)
    (x : σ → ℤ) :
    (b.baseChange ℝ).equivFun (F.realification.polynomialOrbitEval w x g).coord ∈ realDenominatorGrid q := by
  have h := F.polynomialRationalGrid_value b w q (F.realification.polynomialOrbitCoordinates w g)
    ((F.polynomialRationalGrid_iff_formal b w q _).mpr hg) x
  simpa only [F.polynomialOrbitCoordinates_realValue] using h

omit [Fintype ι] in
theorem polynomialOrbit_coefficient_bound_value
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (hw : ∀ i, 0 < w i) (T : σ → ℝ) (hT : ∀ i, 0 < T i) {M : ℝ} (hM : 0 ≤ M)
    (g : F.realification.PolynomialOrbit w) (hg : CoefficientBound (b.baseChange ℝ) T M g.log)
    (x : σ → ℤ) (hx : ∀ i, |(x i : ℝ)| ≤ T i) (i : ι) :
    |(b.baseChange ℝ).repr (F.realification.polynomialOrbitEval w x g).coord i| ≤
      ((s : ℝ) + 1) * ((Fintype.card σ : ℝ) + 1) ^ s * M := by
  have h := F.polynomialSlowBound_value b w hw T hT hM (F.realification.polynomialOrbitCoordinates w g)
    ((F.polynomialSlowBound_iff_formal b w T M _).mpr hg) (fun j => (x j : ℝ)) hx i
  simpa only [F.polynomialOrbitCoordinates_realValue] using h

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

theorem exists_bounded_frozen_constants (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L : Type*} [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d N : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d) (p : ℝ),
      0 ≤ p → D.GeometryComplexityLE p → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∀ ε γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
          CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
            (Real.exp ((p + 2) ^ a)) ε.log →
          CoefficientGrid (D.basis.baseChange ℝ) q γ.log → ∀ y : ZMod N,
          (∀ i, |(D.basis.baseChange ℝ).repr
            (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
              (fun _ => (y.val : ℤ)) ε).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ r : D.RealGroup,
            (∀ i, |(D.basis.baseChange ℝ).repr r.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (D.basis.baseChange ℝ).equivFun r.coord ∈ realDenominatorGrid m ∧
            ∃ δ ∈ D.realLattice,
              D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                (fun _ => (y.val : ℤ)) γ = r * δ := by
  obtain ⟨b, _, hrep⟩ := exists_native_rational_representatives s
  let k := (s + 1) * 2 ^ s
  let Q : Polynomial ℕ := (Polynomial.X + 2) ^ a + Polynomial.C k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Polynomial.X + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro L _ _ _ _ _ _ d N _ D p hp hD q hq hqp
  have htotal : (p + 2) ^ a + (k : ℝ) + (p + b) ^ b ≤ (p + C) ^ C := by
    simpa [Q, Polynomial.eval₂_pow] using hbudget p hp
  have hpow : 0 ≤ (p + b) ^ b := by positivity
  have hsmall : (p + 2) ^ a + (k : ℝ) ≤ (p + C) ^ C := by linarith
  have hrepC : (p + b) ^ b ≤ (p + C) ^ C := by
    have hpowa : 0 ≤ (p + 2) ^ a := by positivity
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    linarith
  obtain ⟨m, hm, hmp, hsolve⟩ := hrep D p hp hD q hq hqp
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hrepC), ?_⟩
  intro ε γ hε hγ y
  refine ⟨?_, ?_⟩
  · intro i
    have hv := D.filtration.polynomialOrbit_coefficient_bound_value D.basis (fun _ : Unit => 1)
      (fun _ => Nat.zero_lt_one) (fun _ : Unit => (N : ℝ))
      (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (Real.exp_pos _).le ε hε
      (fun _ => (y.val : ℤ)) (fun _ => by
        simpa only [Int.cast_natCast, abs_of_nonneg (show (0 : ℝ) ≤ y.val from Nat.cast_nonneg _)]
          using (Nat.cast_le.mpr y.val_lt.le : (y.val : ℝ) ≤ N)) i
    have hke : (k : ℝ) ≤ Real.exp k := by linarith [Real.add_one_le_exp (k : ℝ)]
    have hk : ((s : ℝ) + 1) * ((Fintype.card Unit : ℝ) + 1) ^ s = (k : ℝ) := by
      simp only [k, Fintype.card_unit, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      norm_num
    rw [hk] at hv
    exact hv.trans ((mul_le_mul_of_nonneg_right hke (Real.exp_pos _).le).trans
      (by rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)))
  · obtain ⟨⟨r, hr, hrgrid, δ, hδ, heq⟩, _⟩ := hsolve
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) γ)
      (D.filtration.polynomialOrbit_coefficient_grid_value D.basis (fun _ : Unit => 1) q γ hγ _)
    exact ⟨r, fun i => (hr i).trans (Real.exp_le_exp.mpr hrepC), hrgrid, δ, hδ, heq⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

theorem right_lattice_factor_mk_eq {G : Type*} [Group G] (Γ : Subgroup G)
    (a x u δ : G) (hδ : δ ∈ Γ) :
    (QuotientGroup.mk (a * x * (u * δ)) : G ⧸ Γ) = QuotientGroup.mk (a * x * u) := by
  apply QuotientGroup.eq.mpr
  convert Γ.inv_mem hδ using 1
  group

namespace RationalFilteredNilmanifold

open VectorPolynomial
open scoped TensorProduct

theorem exists_native_frozen_orbit_cover (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L I : Type*} [LieRing L] [LieAlgebra ℚ L] [Fintype I]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d r N : ℕ} [NeZero N] (D : RationalFilteredNilmanifold L s d)
      (R : D.DegreeRankStructure r) (p : ℝ), 0 ≤ p → R.ComplexityLE p →
      ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp p →
      ∃ Λ : Subgroup D.filtration.Group, Λ ≤ D.lattice ∧
        (Λ.subgroupOf D.lattice).Characteristic ∧ (Λ.subgroupOf D.lattice).Normal ∧
        (Λ.subgroupOf D.lattice).FiniteIndex ∧ (Λ.relIndex D.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates D.basis Λ)
          (hout : bchSubgroupCoordinates D.basis Λ ⊆ denominatorGrid m),
          (R.withLattice Λ m hm hin hout).ComplexityLE ((p + C) ^ C) ∧
          ∀ (V : D.UnitVerticalObservable (R.realSubgroup s r) I p)
            (ε γ : D.filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            CoefficientBound (D.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
              (Real.exp ((p + 2) ^ a)) ε.log →
            CoefficientGrid (D.basis.baseChange ℝ) q γ.log → ∀ y : ZMod N,
            ∃ U : (D.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((R.withLattice Λ m hm hin hout).realSubgroup s r) I ((p + C) ^ C),
              U.frequency = V.frequency ∧ ∀ i x,
                U.observable i (QuotientGroup.mk x) = V.observable i (QuotientGroup.mk
                  (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (fun _ => (y.val : ℤ)) ε * x *
                   D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (fun _ => (y.val : ℤ)) γ)) := by
  obtain ⟨b, _, hconstants⟩ := exists_bounded_frozen_constants s a
  obtain ⟨c, _, hcover⟩ := exists_uniform_unit_frozen_cover s 1
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C b) ^ b + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro L I _ _ _ _ _ _ _ d r N _ D R p hp hR q hq hqp
  let t := p + (p + b) ^ b + 2
  have hb : 0 ≤ (p + b) ^ b := by positivity
  have ht : 0 ≤ t := by dsimp only [t]; positivity
  have hpt : p ≤ t := by dsimp only [t]; linarith
  have hbt : (p + b) ^ b ≤ t := by dsimp only [t]; linarith
  have hsum : t + (t + c) ^ c ≤ (p + C) ^ C := by
    simpa [P, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : (t + c) ^ c ≤ (p + C) ^ C := by linarith
  obtain ⟨l, hl, hlb, hsolve⟩ := hconstants (N := N) D p hp hR.1 q hq hqp
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout, hRank, hU⟩ :=
    hcover (I := I) D R t ht (hR.mono R hpt) l hl (hlb.trans (Real.exp_le_exp.mpr hbt))
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr htC),
    m, hm, hin, hout, hRank.mono _ htC, ?_⟩
  intro V ε γ hε hγ y
  obtain ⟨ha, u, hu, hugrid, δ, hδ, heq⟩ := hsolve ε γ hε hγ y
  let a₀ := D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
    (fun _ => (y.val : ℤ)) ε
  obtain ⟨U, hfreq, hval⟩ := hU (V.mono hpt) a₀ u
    (fun i => (ha i).trans (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))) hugrid
  refine ⟨U.mono htC, hfreq, ?_⟩
  intro i x
  calc
    _ = V.observable i (QuotientGroup.mk (a₀ * x * u)) := hval i x
    _ = _ := by
      rw [heq]
      exact congrArg (V.observable i) (right_lattice_factor_mk_eq D.realLattice a₀ x u δ hδ).symm

end RationalFilteredNilmanifold
end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_native_shared_frozen_orbit_correlations (s k : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      0 ≤ P → p ≤ P → ∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.exp P →
      ∀ (H : Finset (ZMod N))
        (ε γ b : ZMod N → W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (y : ZMod N → ZMod N), H.Nonempty →
      (∀ h ∈ H, CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P + 2) ^ k)) (ε h).log) →
      (∀ h ∈ H, CoefficientGrid (W.family.model.basis.baseChange ℝ) q (γ h).log) →
      (∀ h ∈ H, Nonempty (NativeVectorCorrelation (s - 1) N P
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (b h) (γ h) (y h) x)))) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (m : ℕ) (hm : 0 < m)
          (hin : scaledIntegerGrid m ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid m),
          (W.family.rank.withLattice Λ m hm hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ H' : Finset (ZMod N), H' ⊆ H ∧ H'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * H.card ≤ (H'.card : ℝ) ∧
            ∃ U : (W.family.model.withLattice Λ m hm hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ m hm hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              U.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ H', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                  (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (b h)))))) := by
  obtain ⟨a₀, _, hconstants⟩ := exists_bounded_frozen_constants s k
  obtain ⟨b₀, _, hshared⟩ := exists_native_shared_frozen_correlations s 1
  let Q : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C a₀) ^ a₀ + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (Q + (Q + Polynomial.C b₀) ^ b₀)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P F W hF hP hpP q hq hqP H ε γ b y hH hε hγ hcorr
  classical
  let T := P + (P + a₀) ^ a₀ + 2
  have hA : 0 ≤ (P + a₀) ^ a₀ := by positivity
  have hPT : P ≤ T := by dsimp only [T]; linarith
  have hAT : (P + a₀) ^ a₀ ≤ T := by dsimp only [T]; linarith
  have hT : 0 ≤ T := hP.trans hPT
  have hsum : T + (T + b₀) ^ b₀ ≤ (P + C) ^ C := by
    simpa [Q, T, Polynomial.eval₂_pow] using hbudget P hP
  have hTC : (T + b₀) ^ b₀ ≤ (P + C) ^ C := by linarith
  obtain ⟨l, hl, hlbound, hsolve⟩ := hconstants (N := N) W.family.model P hP
    (W.family.complexity.1.mono _ hpP) q hq hqP
  have hreps (h : {h // h ∈ H}) := (hsolve (ε h) (γ h) (hε h h.property) (hγ h h.property) (y h)).2
  choose u hu hugrid δ hδ heq using hreps
  let u' (h : ZMod N) : W.family.model.RealGroup := if hh : h ∈ H then u ⟨h, hh⟩ else 1
  let a (h : ZMod N) := W.family.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => ((y h).val : ℤ)) (ε h)
  let b' (h x : ZMod N) := W.family.model.filtration.realification.polynomialOrbitEval
    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (b h)
  have hbound : Real.exp ((P + a₀) ^ a₀) ≤ Real.exp ((T + 2) ^ 1) :=
    Real.exp_le_exp.mpr (by simp only [pow_one]; linarith)
  have ha (h : ZMod N) (hh : h ∈ H) (i : Fin W.family.dim) :
      |(W.family.model.basis.baseChange ℝ).repr (a h).coord i| ≤ Real.exp ((T + 2) ^ 1) :=
    ((hsolve (ε h) (γ h) (hε h hh) (hγ h hh) (y h)).1 i).trans hbound
  have hu' (h : ZMod N) (hh : h ∈ H) (i : Fin W.family.dim) :
      |(W.family.model.basis.baseChange ℝ).repr (u' h).coord i| ≤ Real.exp ((T + 2) ^ 1) := by
    simpa only [u', dite_eq_left hh] using (hu ⟨h, hh⟩ i).trans hbound
  have hugrid' (h : ZMod N) (hh : h ∈ H) :
      (W.family.model.basis.baseChange ℝ).equivFun (u' h).coord ∈ realDenominatorGrid l := by
    simpa only [u', dite_eq_left hh] using hugrid ⟨h, hh⟩
  have hc (h : ZMod N) (hh : h ∈ H) : Nonempty (NativeVectorCorrelation (s - 1) N T
      (W.replacedRankResidual h (fun i x => W.family.vertical.observable i
        (QuotientGroup.mk (a h * b' h x * u' h))))) := by
    have hfun : (fun i x => W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x * u' h))) =
        (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (b h) (γ h) (y h) x) := by
      funext i x
      change W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x * u' h)) =
        W.family.vertical.observable i (QuotientGroup.mk (a h * b' h x *
          W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => ((y h).val : ℤ)) (γ h)))
      rw [heq ⟨h, hh⟩]
      simp only [u', dite_eq_left hh]
      exact congrArg (W.family.vertical.observable i)
        (right_lattice_factor_mk_eq W.family.model.realLattice (a h) (b' h x) (u ⟨h, hh⟩)
          (δ ⟨h, hh⟩) (hδ ⟨h, hh⟩)).symm
    rw [hfun]
    exact ⟨(Classical.choice (hcorr h hh)).mono hPT⟩
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, m, hm, hin, hout,
      hRank, H', hsub, hnonempty, hdense, U, hfreq, hU⟩ :=
    hshared W hF hT (hpP.trans hPT) l hl
      (hlbound.trans (Real.exp_le_exp.mpr hAT)) H a u' b' hH ha hu' hugrid' hc
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hTC),
    m, hm, hin, hout, hRank.mono _ hTC, H', hsub, hnonempty, ?_, U.mono hTC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hTC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact ⟨(Classical.choice (hU h hh)).mono hTC⟩

end Erdos3

end

section

namespace Erdos3

open RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff

theorem exists_shared_factor_correlations (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {r N : ℕ} [NeZero N] {p P : ℝ} {f : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p f), (∀ x, ‖f x‖ ≤ 1) →
      2 ≤ P → p ≤ P → ∀ (m M : ℕ), 0 < m → (m : ℝ) ≤ Real.exp P →
      0 < M → (M : ℝ) ≤ Real.exp P →
      ∀ (J : Finset (ZMod N)), J ⊆ W.shifts → J.Nonempty →
      ∀ ε a ρ : ZMod N → W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
      (∀ h ∈ J, ε h * a h * ρ h = W.family.orbit h) →
      (∀ h ∈ J, CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp ((P + 2) ^ 1)) (ε h).log) →
      (∀ h ∈ J, CoefficientGrid (W.family.model.basis.baseChange ℝ) m (ρ h).log) →
      (∀ h ∈ J, ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
        (QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) x (ρ h)) : W.family.model.Space) =
        QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
          (fun _ : Unit => 1) y (ρ h))) →
      Real.exp ((P + C) ^ C) ≤ (N : ℝ) →
      ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
        (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
        (Λ.subgroupOf W.family.model.lattice).Normal ∧
        (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
        (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((P + C) ^ C) ∧
        ∃ (l : ℕ) (hl : 0 < l)
          (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
          (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid l),
          (W.family.rank.withLattice Λ l hl hin hout).ComplexityLE ((P + C) ^ C) ∧
          ∃ J' : Finset (ZMod N), J' ⊆ J ∧ J'.Nonempty ∧
            Real.exp (-((P + C) ^ C)) * J.card ≤ (J'.card : ℝ) ∧
            ∃ V : (W.family.model.withLattice Λ l hl hin hout).UnitVerticalObservable
                ((W.family.rank.withLattice Λ l hl hin hout).realSubgroup s r)
                (Fin W.family.outputDim) ((P + C) ^ C),
              V.frequency = W.family.vertical.frequency ∧
              ∀ h ∈ J', Nonempty (NativeVectorCorrelation (s - 1) N ((P + C) ^ C)
                (W.replacedRankResidual h (fun i x => V.observable i (QuotientGroup.mk
                  (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (a h)))))) := by
  obtain ⟨b, _, hfreeze⟩ := exists_native_frozen_rank_correlation s 1 hs
  obtain ⟨c, _, hshared⟩ := exists_native_shared_frozen_orbit_correlations s 1
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C b) ^ b + Polynomial.X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (B + (B + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro r N _ p P f W hf hP hpP m M hm hmP hM hMP J hJW hJ ε a ρ hprod hε hρ hperiod hN
  classical
  let P₁ := (P + b) ^ b + P + 2
  have hP0 : 0 ≤ P := by linarith
  have hb0 : 0 ≤ (P + b) ^ b := by positivity
  have hP₁ : 0 ≤ P₁ := by dsimp only [P₁]; positivity
  have hPP₁ : P ≤ P₁ := by dsimp only [P₁]; linarith
  have hbP₁ : (P + b) ^ b ≤ P₁ := by dsimp only [P₁]; linarith
  have hsum : P₁ + (P₁ + c) ^ c ≤ (P + C) ^ C := by
    simpa [P₁, B, Polynomial.eval₂_pow] using hbudget P hP0
  have hP₁C : P₁ ≤ (P + C) ^ C :=
    (le_add_of_nonneg_right (by positivity : 0 ≤ (P₁ + c) ^ c)).trans hsum
  have hcC : (P₁ + c) ^ c ≤ (P + C) ^ C := (le_add_of_nonneg_left hP₁).trans hsum
  have hchoose (h : {h // h ∈ J}) : ∃ y : ZMod N,
      Nonempty (NativeVectorCorrelation (s - 1) N P₁
        (W.replacedRankResidual h.val (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h.val) (a h.val) (ρ h.val) y x))) := by
    obtain ⟨y, _, hy⟩ := hfreeze W hf ⟨h.val, hJW h.property⟩ P hP hpP M hM hMP
      (ε h.val) (a h.val) 1 (ρ h.val) (by simpa only [mul_one] using hprod h.val h.property)
      (hε h.val h.property) (hperiod h.val h.property)
      ((Real.exp_le_exp.mpr (hbP₁.trans hP₁C)).trans hN)
    refine ⟨y, ?_⟩
    simpa only [mul_one] using
      (show Nonempty _ from ⟨(Classical.choice hy).mono hbP₁⟩)
  choose y hy using hchoose
  let y' (h : ZMod N) := if hh : h ∈ J then y ⟨h, hh⟩ else 0
  have hcorr (h : ZMod N) (hh : h ∈ J) :
      Nonempty (NativeVectorCorrelation (s - 1) N P₁
        (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) (ε h) (a h) (ρ h) (y' h) x))) := by
    simpa only [y', dite_eq_left hh] using hy ⟨h, hh⟩
  have hε' (h : ZMod N) (hh : h ∈ J) :
      CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
        (Real.exp ((P₁ + 2) ^ 1)) (ε h).log :=
    CoefficientBound.mono _ _ (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (hε h hh)
      (Real.exp_le_exp.mpr (by simpa only [pow_one] using (show P + 2 ≤ P₁ + 2 by linarith)))
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, l, hl, hin, hout,
      hRank, J', hsub, hnonempty, hdense, V, hfreq, hV⟩ :=
    hshared W hf hP₁ (hpP.trans hPP₁) m hm
      (hmP.trans (Real.exp_le_exp.mpr hPP₁)) J ε ρ a y' hJ hε' hρ hcorr
  refine ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hcC),
    l, hl, hin, hout, hRank.mono _ hcC, J', hsub, hnonempty, ?_, V.mono hcC, hfreq, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hcC))
      (Nat.cast_nonneg _)).trans hdense
  · intro h hh
    exact ⟨(Classical.choice (hV h hh)).mono hcC⟩

noncomputable def sharedFactorCorrelationConstant (s : ℕ) (hs : 2 ≤ s) : ℕ :=
  (exists_shared_factor_correlations s hs).choose

end Erdos3

end

end OAI
