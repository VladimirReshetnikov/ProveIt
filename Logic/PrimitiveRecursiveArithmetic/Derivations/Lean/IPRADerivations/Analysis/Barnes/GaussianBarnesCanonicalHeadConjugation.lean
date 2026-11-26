import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalHead
import IPRADerivations.Analysis.Barnes.GaussianBarnesCanonicalFactorConjugation
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductConjugation
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductFamilyCongruence

/-!
# Conjugation of the original finite Barnes head and segments

The conjugation identity compares the original named products at
one rational argument and its Gaussian conjugate. It holds at
every start and length, even when a factor vanishes.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadConjugation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBarnesCanonicalHead (source nameF data parameters body)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedFiniteProductFamily (rowF productData)
open GaussianNamedFiniteProductFamilyCongruence (equalRows family_product_cross)
open GaussianRationalReciprocal (conjugate)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Conj" => GaussianNameConjugation.nameF
local notation "F" => GaussianBarnesCanonicalFactor.nameF

theorem conjugate_source (z R B : PTm n) (h : Γ ⊢[PRAAx] source z R B) :
    Γ ⊢[PRAAx] source (conjugate z) R B :=
  .andI h.andE₁ (GaussianGammaFiniteConjugation.native_disk z (R*B) h.andE₂)

theorem rows_cross (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    equalRows (Conj F) F body body r (parameters z R B N) (parameters (conjugate z) R B N) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := lt (var 0) (sh r) :: Γ.map Fm.shift
  let i : PTm (n+1) := var 0
  let k := succ (sh N+i)
  have hs : Δ ⊢[PRAAx] source (sh z) (sh R) (sh B) := by
    simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift.wk
  have e := GaussianBarnesCanonicalFactorConjugation.factor_cross (sh z) (sh R) (sh B) k
    (.andI hs.andE₁ (.andI (zero_lt_succ _) hs.andE₂))
  have left := GaussianBarnesCanonicalHead.body_at (Γ := Δ) i (sh z) (sh R) (sh B) (sh N)
  have right := GaussianBarnesCanonicalHead.body_at (Γ := Δ) i (conjugate (sh z)) (sh R) (sh B) (sh N)
  simpa only [equalRows,GaussianBarnesCanonicalHead.subst_parameters,GaussianRationalReciprocal.subst_conjugate,
    Syn.shift,Δ,sh,i] using
    GaussianGammaCompactCutoffAlignment.cross_data_congr (Conj F) F _ _ _ _ left.eqSymm right.eqSymm e

theorem segment_cross (z R B N r : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (Conj nameF) nameF (data z R B N r) (data (conjugate z) R B N r) := by
  let w := conjugate z
  let X := parameters z R B N
  let Y := parameters w R B N
  let G := GaussianNamedFiniteProductName.nameF (rowF (Conj F) body)
  have hz := GaussianBarnesCanonicalHead.rows_regular z R B N r h
  have hw := GaussianBarnesCanonicalHead.rows_regular w R B N r (conjugate_source z R B h)
  have first := GaussianNamedFiniteProductConjugation.family_cross F body r X hz
  have last := family_product_cross (Conj F) F body body r X Y
    (GaussianNamedFiniteProductConjugation.rows_regular F body r X hz) hw (rows_cross z R B N r h)
  exact cross_trans (Conj nameF) G nameF (data z R B N r) (productData (Conj F) body r X) (data w R B N r) first last

theorem actual_Barnes_canonical_segment_conjugation_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (let z := var 0
       let R := var 1
       let B := var 2
       let N := var 3
       let r := var 4
       source z R B ⟶ crossEquivalent (Conj nameF) nameF (data z R B N r) (data (conjugate z) R B N r)) :=
  closeUniv 5 (.impI (segment_cross _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalHeadConjugation
