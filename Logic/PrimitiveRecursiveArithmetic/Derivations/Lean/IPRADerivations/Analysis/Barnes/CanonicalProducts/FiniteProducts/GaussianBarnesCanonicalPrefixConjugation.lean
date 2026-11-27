import IPRADerivations.Analysis.Barnes.CanonicalProducts.FiniteProducts.GaussianBarnesCanonicalProduct
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalHeadConjugation
import IPRADerivations.Analysis.Barnes.Prefactors.GaussianBarnesCanonicalPrefactorConjugation

/-!
# Conjugation of the original literal finite Barnes product

The original prefactor and finite head conjugate at every common
cutoff. The identity includes the empty head and vanishing factors.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixConjugation

open_ipra
open GaussianBarnesCanonicalLogCofinal (source)
open GaussianBarnesCanonicalProduct (literalData)
open GaussianBarnesCanonicalValue (prefixF)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianRationalReciprocal (conjugate)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Conj" => GaussianNameConjugation.nameF
local notation "P" => GaussianBarnesCanonicalPrefactor.nameF
local notation "H" => GaussianBarnesCanonicalHead.nameF

theorem prefix_cross (z R B N : PTm n) (h : Γ ⊢[PRAAx] source z R B) : Γ ⊢[PRAAx]
    crossEquivalent (Conj prefixF) prefixF (literalData z R B N) (literalData (conjugate z) R B N) := by
  let w := conjugate z
  let x := GaussianBarnesCanonicalPrefactor.data z B
  let y := GaussianBarnesCanonicalPrefactor.data w B
  let u := GaussianBarnesCanonicalHead.data z R B zero N
  let v := GaussianBarnesCanonicalHead.data w R B zero N
  have hp := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) z B
  have hp' := GaussianBarnesCanonicalPrefactor.regular (Γ := Γ) w B
  have hh := GaussianBarnesCanonicalHead.regular z R B zero N h
  have hh' := GaussianBarnesCanonicalHead.regular w R B zero N
    (GaussianBarnesCanonicalHeadConjugation.conjugate_source z R B h)
  have first := GaussianNameConjugation.multiply_cross P H x u hp hh
  have last := GaussianGammaAdjacentCutoff.multiply_cross (Conj P) P (Conj H) H x y u v
    (GaussianNameConjugation.regular _ _ hp) hp' (GaussianNameConjugation.regular _ _ hh) hh'
    (GaussianBarnesCanonicalPrefactorConjugation.prefactor_cross z B h.andE₁)
    (GaussianBarnesCanonicalHeadConjugation.segment_cross z R B zero N h)
  exact cross_trans _ _ _ _ _ _ first last

theorem actual_Barnes_literal_prefix_conjugation_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (let z := var 0
     let R := var 1
     let B := var 2
     let N := var 3
     source z R B ⟶ crossEquivalent (Conj prefixF) prefixF (literalData z R B N) (literalData (conjugate z) R B N)) :=
  closeUniv 4 (.impI (prefix_cross _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPrefixConjugation
