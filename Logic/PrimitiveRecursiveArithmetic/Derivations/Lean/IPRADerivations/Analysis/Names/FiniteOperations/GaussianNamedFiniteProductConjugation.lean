import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamily
import IPRADerivations.Analysis.Names.GaussianNameConjugation

/-!
# Conjugation of actual finite Gaussian name products

Conjugating each row commutes with the ascending rational product,
including the empty product. Each named family retains the precision
normalizer computed from its own rows.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductConjugation

open_ipra
open GaussianNameEquivalence (crossEquivalent)
open GaussianNamedFiniteProduct (sample sample_zero sample_succ)
open GaussianNamedFiniteProductFamily (rowF row_at regularRows regular_at radius productData family_bounds family_regular)
open GaussianRationalConjugation (point point_congr point_one point_mul)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Conj" => GaussianNameConjugation.nameF
local notation "Product" => GaussianNamedFiniteProductName.nameF
local notation "rawF" => GaussianNamedFiniteProductName.rawF
local notation "rawData" => GaussianNamedFiniteProductName.rawData

theorem row_at_conjugate (f : PR 2) (body : PTm 2) (p i x : PTm n) : Γ ⊢[PRAAx]
    point (ap3 (rowF f body) p i x) ≐ ap3 (rowF (Conj f) body) p i x :=
  (point_congr (row_at f body p i x)).eqTrans
    ((row_at (Conj f) body p i x).eqTrans (GaussianNameConjugation.sample_at f p _)).eqSymm

private def sampleLaw (f : PR 2) (body : PTm 2) (p r x : PTm n) : Fm PTm n :=
  point (sample (rowF f body) p r x) ≐ sample (rowF (Conj f) body) p r x

@[simp] private theorem subst_sampleLaw {m : ℕ} (σ : Fin n → PTm m)
    (f : PR 2) (body : PTm 2) (p r x : PTm n) :
    (sampleLaw f body p r x).subst σ = sampleLaw f body (Syn.subst σ p) (Syn.subst σ r) (Syn.subst σ x) := by
  simp [sampleLaw]

theorem sample_conjugate (f : PR 2) (body : PTm 2) (p r x : PTm n) : Γ ⊢[PRAAx]
    point (sample (rowF f body) p r x) ≐ sample (rowF (Conj f) body) p r x := by
  have h : Γ ⊢[PRAAx] .all (sampleLaw f body (Syn.shift p) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (point_congr (sample_zero (rowF f body) p x)).eqTrans
        (point_one.eqTrans (sample_zero (rowF (Conj f) body) p x).eqSymm)
    · simp only [subst_sampleLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      let P := Syn.shift p
      let X := Syn.shift x
      let i : PTm (n+1) := var 0
      let F := rowF f body
      let G := rowF (Conj f) body
      let Δ := sampleLaw f body P i X :: Γ.map Fm.shift
      have ih : Δ ⊢[PRAAx] sampleLaw f body P i X := Prf.hyp0
      exact (point_congr (sample_succ F P i X)).eqTrans ((point_mul _ _).eqTrans
        ((qmul_congr ih (row_at_conjugate f body P i X)).eqTrans (sample_succ G P i X).eqSymm))
  have h' : Γ ⊢[PRAAx] sampleLaw f body p r x := by
    simpa only [subst_sampleLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using h.allE r
  exact h'

theorem rows_regular (f : PR 2) (body : PTm 2) (r x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f body r x) : Γ ⊢[PRAAx] regularRows (Conj f) body r x := by
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift r) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] regularRows f body (Syn.shift r) (Syn.shift x) := by
    simpa [Δ,Fm.shift,Syn.shift] using h.shift.wk
  exact GaussianNameConjugation.regular f _
    (regular_at f body (Syn.shift r) (Syn.shift x) (var 0) hs Prf.hyp0)

theorem family_cross (f : PR 2) (body : PTm 2) (r x : PTm n)
    (h : Γ ⊢[PRAAx] regularRows f body r x) : Γ ⊢[PRAAx]
    crossEquivalent (Conj (Product (rowF f body))) (Product (rowF (Conj f) body))
      (productData f body r x) (productData (Conj f) body r x) := by
  let F := rowF f body
  let G := rowF (Conj f) body
  let R := radius f body r x
  let S := radius (Conj f) body r x
  have hs := rows_regular f body r x h
  have regF := GaussianNamedFiniteProductName.raw_regular F r R one x
    (family_bounds f body r x h) (family_regular f body r x h)
  have regG := GaussianNamedFiniteProductName.raw_regular G r S one x
    (family_bounds (Conj f) body r x hs) (family_regular (Conj f) body r x hs)
  apply GaussianNameConjugation.normalized_transport _ _ _ _ _ _ regF regG
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let p : PTm (n+1) := var 0
  let N := Syn.shift r
  let X := Syn.shift x
  have a := GaussianNamedFiniteProductName.raw_at (Γ := Δ) F p N X
  have b := GaussianNamedFiniteProductName.raw_at (Γ := Δ) G p N X
  simpa only [GaussianNameConjugation.covariance,GaussianNamedFiniteProductName.subst_rawData,Syn.shift,Δ,p,N,X] using
    (point_congr a).eqTrans ((sample_conjugate f body p N X).eqTrans b.eqSymm)

theorem actual_named_finite_product_conjugation_closed (f : PR 2) (body : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (regularRows f body (var 0) (var 1) ⟶
        crossEquivalent (Conj (Product (rowF f body))) (Product (rowF (Conj f) body))
          (productData f body (var 0) (var 1)) (productData (Conj f) body (var 0) (var 1))) :=
  closeUniv 2 (.impI (family_cross f body _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianNamedFiniteProductConjugation
