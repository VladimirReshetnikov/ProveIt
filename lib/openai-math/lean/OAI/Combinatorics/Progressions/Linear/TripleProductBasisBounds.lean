import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module

variable {ι : Type*} [Fintype ι] {L : ι → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))

noncomputable def productBasisWeight (weight : ∀ i, Fin (d i) → ℕ)
    (k : Fin (Fintype.card (Σ i, Fin (d i)))) : ℕ :=
  let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
  weight z.1 z.2

theorem productFinBasis_repr (x : ∀ i, L i) (k : Fin (Fintype.card (Σ i, Fin (d i)))) :
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    (pi D).basis.repr x k = (D z.1).basis.repr (x z.1) z.2 := by
  change (productFinBasis D).repr x k = _
  rw [productFinBasis, Basis.repr_reindex_apply, Pi.basis_repr]

theorem pi_layer_span (weight : ∀ i, Fin (d i) → ℕ)
    (hF : ∀ i n, (D i).filtration.layer n =
      Submodule.span ℚ ((D i).basis '' {k | n ≤ weight i k})) (n : ℕ) :
    (pi D).filtration.layer n =
      Submodule.span ℚ ((pi D).basis '' {k | n ≤ productBasisWeight weight k}) := by
  classical
  ext x
  change x ∈ (NilpotentLieFiltration.pi (fun i => (D i).filtration)).layer n ↔ _
  rw [NilpotentLieFiltration.mem_pi_layer]
  constructor
  · intro hx
    apply (pi D).basis.mem_span_image.mpr
    intro k hk
    have hcoeff : (pi D).basis.repr x k ≠ 0 := Finsupp.mem_support_iff.mp hk
    rw [productFinBasis_repr D] at hcoeff
    let z := (Fintype.equivFin (Σ i, Fin (d i))).symm k
    have hm := hx z.1
    rw [hF z.1 n] at hm
    exact (D z.1).basis.mem_span_image.mp hm (Finsupp.mem_support_iff.mpr hcoeff)
  · intro hx i
    rw [hF i n]
    apply (D i).basis.mem_span_image.mpr
    intro k hk
    let q := (Fintype.equivFin (Σ i, Fin (d i))) ⟨i, k⟩
    have hq : (Fintype.equivFin (Σ i, Fin (d i))).symm q = ⟨i, k⟩ :=
      Equiv.symm_apply_apply _ _
    have hrepr : (pi D).basis.repr x q = (D i).basis.repr (x i) k :=
      (productFinBasis_repr D x q).trans
        (congrArg (fun z : Σ i, Fin (d i) => (D z.1).basis.repr (x z.1) z.2) hq)
    have hcoeff : (pi D).basis.repr x q ≠ 0 := by
      rw [hrepr]
      exact Finsupp.mem_support_iff.mp hk
    have hw := (pi D).basis.mem_span_image.mp hx (Finsupp.mem_support_iff.mpr hcoeff)
    change n ≤ productBasisWeight weight q at hw
    have hweight : productBasisWeight weight q = weight i k :=
      congrArg (fun z : Σ i, Fin (d i) => weight z.1 z.2) hq
    exact hw.trans_eq hweight

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L s d)

theorem triple_product_basis_logHeight (x : L × L × L) {p : ℝ}
    (hx : ∀ k, rationalLogHeight (D.basis.repr x.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2.1 k) ≤ p ∧
      rationalLogHeight (D.basis.repr x.2.2 k) ≤ p)
    (k : Fin (Fintype.card (Σ _ : Fin 3, Fin d))) :
    rationalLogHeight ((pi (fun _ : Fin 3 => D)).basis.repr (tripleToPi x) k) ≤ p := by
  have h (j : Fin 3) (l : Fin d) :
      rationalLogHeight (D.basis.repr (tripleToPi x j) l) ≤ p := by
    fin_cases j
    · exact (hx l).1
    · exact (hx l).2.1
    · exact (hx l).2.2
  rw [productFinBasis_repr]
  exact h _ _

end Erdos3.RationalFilteredNilmanifold

end

end OAI
