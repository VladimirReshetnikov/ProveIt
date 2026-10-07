import OAI.Combinatorics.Progressions.Polynomial.AntisymmetricPairPolynomial
import OAI.Combinatorics.Progressions.Polynomial.ProductPolynomialMaps

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

namespace NativeMultidegreeNilcharacter

variable {p : ℝ} (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)

noncomputable def pairComponentPolynomial (out : Fin W.outputDim) (a b : Fin 2) :
    (W.model.filtration.realification.adaptedPolynomialFiltration (fun _ : Fin 2 => 1)).Group :=
  ⟨⟨(W.pairComponent out a b).orbit.log, (W.pairComponent out a b).orbit.property⟩⟩

theorem pairComponentPolynomial_out_eq (i j : Fin W.outputDim) (a b : Fin 2) :
    W.pairComponentPolynomial i a b = W.pairComponentPolynomial j a b := rfl

end NativeMultidegreeNilcharacter

namespace NativeSampleCorrelation

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ)))

theorem antisymmetricPairProjection_layers (k : Fin 2) (a : ℕ)
    (x : V.AntisymmetricPairAlgebra) (hx : x ∈ (pi V.antisymmetricPairModels).filtration.layer a) :
    V.antisymmetricPairProjection k x ∈ W.model.filtration.layer a :=
  (NilpotentLieFiltration.mem_pi_layer (fun l => (V.antisymmetricPairModels l).filtration) a x).mp hx (some k)

noncomputable def antisymmetricPairPolynomialMap (k : Fin 2) :
    ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group →*
        (W.model.filtration.realification.adaptedPolynomialFiltration (fun _ : Fin 2 => 1)).Group :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1)

theorem antisymmetricPairPolynomialMap_log (k : Fin 2)
    (g : ((pi V.antisymmetricPairModels).filtration.realification.adaptedPolynomialFiltration
      (fun _ : Fin 2 => 1)).Group) :
    ((V.antisymmetricPairPolynomialMap k g).coord : VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] W.L)) =
      VectorPolynomial.map ((realificationLieHom (V.antisymmetricPairProjection k)).toLinearMap.restrictScalars ℚ)
        (g.coord : VectorPolynomial (Fin 2) ℚ (ℝ ⊗[ℚ] V.AntisymmetricPairAlgebra)) := rfl

theorem antisymmetricPairPolynomialMap_eq (k : Fin 2) (out : Fin W.outputDim) :
    V.antisymmetricPairPolynomialMap k V.antisymmetricPairPolynomial =
      W.pairComponentPolynomial out k k.rev := by
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  change VectorPolynomial.map ((realificationLieHom (liePiEval (some k))).toLinearMap.restrictScalars ℚ)
    (NilpotentLieFiltration.piRealOrbit (fun l => (V.antisymmetricPairModels l).filtration)
      (fun l => (V.antisymmetricPairTests l).orbit)).log = (W.pairComponent out k k.rev).orbit.log
  rw [NilpotentLieFiltration.piRealOrbit_projection_log]
  fin_cases k <;> rfl

theorem antisymmetricPairPolynomialMap_constant (k : Fin 2)
    (c : (pi V.antisymmetricPairModels).RealGroup) :
    V.antisymmetricPairPolynomialMap k
        ((pi V.antisymmetricPairModels).filtration.realification.adaptedConstantGroupHom
          (fun _ : Fin 2 => 1) c) =
      W.model.filtration.realification.adaptedConstantGroupHom (fun _ : Fin 2 => 1)
        (productProjectionHom V.antisymmetricPairModels (some k) c) :=
  (pi V.antisymmetricPairModels).filtration.realPolynomialGroupMap_constant W.model.filtration
    (V.antisymmetricPairProjection k) (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1) c

theorem antisymmetricPairProjection_lattice (k : Fin 2)
    (c : (pi V.antisymmetricPairModels).RealGroup) (hc : c ∈ (pi V.antisymmetricPairModels).realLattice) :
    productProjectionHom V.antisymmetricPairModels (some k) c ∈ W.model.realLattice :=
  NilpotentLieBCHGroup.realificationMap_subgroup _ _ _
    (productProjection_lattice V.antisymmetricPairModels (some k)) hc

noncomputable def antisymmetricPairCoordinateIndex (k : Fin 2) (a : Fin W.dim) :
    Fin (Fintype.card (Σ l : Option (Fin 2), Fin (optionDimension V.dim (fun _ : Fin 2 => W.dim) l))) :=
  Fintype.equivFin (Σ l : Option (Fin 2), Fin (optionDimension V.dim (fun _ : Fin 2 => W.dim) l)) ⟨some k, a⟩

theorem antisymmetricPairProjection_repr (k : Fin 2) (x : V.AntisymmetricPairAlgebra) (a : Fin W.dim) :
    W.model.basis.repr (V.antisymmetricPairProjection k x) a =
      (pi V.antisymmetricPairModels).basis.repr x (V.antisymmetricPairCoordinateIndex k a) :=
  productFinBasis_repr_component V.antisymmetricPairModels x (some k) a

end NativeSampleCorrelation

end Erdos3

end

end OAI
