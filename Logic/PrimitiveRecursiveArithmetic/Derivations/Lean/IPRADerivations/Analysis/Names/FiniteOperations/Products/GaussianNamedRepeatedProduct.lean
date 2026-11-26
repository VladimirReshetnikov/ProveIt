import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedFiniteProductFamily

/-!
# Finite repeated products of a named Gaussian value

The constant row program reads the original value at the requested
precision. Its finite product is exactly the rational power of that
observation, with the empty product equal to one.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianNamedRepeatedProduct

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ rowBoundsAt)
open GaussianNamedFiniteProductName (rowBounds rowRegular)
open GaussianRationalReciprocal (power power_zero power_succ bound_congr)
open GaussianRationalMetric (bounded)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def repeatF (f : PR 2) : PR 3 := PTm.toPR (ap2 f (var 0) (var 2) : PTm 3)

theorem row_at (f : PR 2) (p i x : PTm n) : Γ ⊢[PRAAx] ap3 (repeatF f) p i x ≐ ap2 f p x := by
  simpa [repeatF,ap3] using toPR_eq (Γ := Γ) (ap2 f (var 0) (var 2) : PTm 3) ![p,i,x]

def repeatLaw (f : PR 2) (p N x : PTm n) : Fm PTm n :=
  sample (repeatF f) p N x ≐ power (ap2 f p x) N

ipra_subst repeatLaw

theorem sample_power (f : PR 2) (p N x : PTm n) : Γ ⊢[PRAAx] repeatLaw f p N x := by
  have all : Γ ⊢[PRAAx] .all (repeatLaw f (Syn.shift p) (var 0) (Syn.shift x)) := by
    ipra_qfind [subst_repeatLaw]
    · exact (sample_zero (repeatF f) p x).eqTrans (power_zero (ap2 f p x)).eqSymm
    · exact (sample_succ (repeatF f) _ _ _).eqTrans
        ((qmul_congr Prf.hyp0 (row_at f _ _ _)).eqTrans (power_succ _ _).eqSymm)
  simpa only [subst_repeatLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE N

def bounds (f : PR 2) (R x : PTm n) : Fm PTm n :=
  .all (bounded (ap2 f (var 0) (Syn.shift x)) (Syn.shift R) one)

ipra_subst bounds [one, Syn.subst_shift, Syn.shift_subst]

theorem bound_at (f : PR 2) (p R x : PTm n) (h : Γ ⊢[PRAAx] bounds f R x) :
    Γ ⊢[PRAAx] bounded (ap2 f p x) R one := by simpa [bounds,one] using h.allE p

theorem repeated_row_bounds (f : PR 2) (N R x : PTm n) (h : Γ ⊢[PRAAx] bounds f R x) :
    Γ ⊢[PRAAx] rowBounds (repeatF f) N R x := by
  refine .allI (.allI (.impI ?_))
  let sh := fun t : PTm n => Syn.shift (Syn.shift t)
  let Δ := lt (var 0) (sh N) :: (Γ.map Fm.shift).map Fm.shift
  have b : Δ ⊢[PRAAx] bounds f (sh R) (sh x) := by
    simpa [Fm.shift,Syn.shift,Δ,sh] using h.shift.shift.wk
  simpa [rowBounds,rowBoundsAt,Syn.shift,Δ,sh] using
    bound_congr (row_at f (var 1) (var 0) (sh x)).eqSymm (.eqRefl _) (.eqRefl _)
      (bound_at f (var 1) (sh R) (sh x) b)

theorem repeated_row_regular (f : PR 2) (N x : PTm n) (h : Γ ⊢[PRAAx] pointCN f x) :
    Γ ⊢[PRAAx] rowRegular (repeatF f) N one x := by
  have rows : Γ ⊢[PRAAx] GaussianNamedFiniteProductFamily.regularRows f (var 1) N x :=
    .allI (.impI (GaussianEuclideanDistanceName.shift_pointCN h).wk)
  exact GaussianNamedFiniteProductFamily.family_regular f (var 1) N x rows

theorem actual_named_repeated_product_sample_closed (f : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (repeatLaw f (var 0) (var 1) (var 2)) :=
  closeUniv 3 (sample_power f _ _ _)

end LeanProofs.IPRA.Analysis.GaussianNamedRepeatedProduct
