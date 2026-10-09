import GowersSzemeredi.Proofs16ColumnModelPacking

/-! Bounded classes of alternating tuples. Each tuple is compared with
one representative; pairwise identities inside a class use only that
representative's spectrum, independently of the number of classes. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Dense representation families admit a bounded class assignment with
exact local-map identities inside each class. -/
theorem column_tuple_class_cover {I : Type*} [Inhabited I] {N d k : Nat}
    [NeZero N] [Fact N.Prime]
    (A : Finset I) (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (anchors : I → List (ZMod N))
    (F : I → Finset (ColumnWord N (k+1))) (c : ZMod N) {rho r delta : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho) (hd : 0 < delta)
    (hT : ∀ x ∈ X, (T x).card ≤ d)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (hlen : ∀ i ∈ A, (anchors i).length = k+1)
    (ha : ∀ i ∈ A, ∀ x ∈ anchors i, x ∈ X)
    (hw : ∀ i ∈ A, ∀ w ∈ F i, ∀ x ∈ columnWordEntries w, x ∈ X)
    (hval : ∀ i ∈ A, ∀ w ∈ F i, columnWordValue w = c)
    (hmass : ∀ i ∈ A, delta*(N : Real)^(3*k+2) ≤ (F i).card)
    (hident : ∀ i ∈ A, ∀ w ∈ F i, ColumnListIdentity T L r (anchors i) (columnWordEntries w))
    (hN1 : refinementKernelCap (2*(k+1)*d) (3*(k+1)*d) rho r < N)
    (hN2 : refinementKernelCap (2*(k+1)*d) ((k+1)*d) rho
      (refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho r) < N) :
    let s := refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho r
    let t := refinementKernelRadius (2*(k+1)*d) ((k+1)*d) rho s
    ∃ J ⊆ A, (J.card : Real)*delta ≤ 1 ∧ ∃ classOf : I → I,
      (∀ i ∈ A, classOf i ∈ J ∧ ColumnListIdentity T L s (anchors i) (anchors (classOf i))) ∧
      ∀ i ∈ A, ∀ j ∈ A, classOf i = classOf j → ColumnListIdentity T L t (anchors i) (anchors j) := by
  obtain ⟨J, hJA, hJ, hcover⟩ := column_model_packing A X T L anchors F c
    hrho hr hrle hd hT hL hzero hlen ha hw hval hmass hident hN1
  have hs : 0 < refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho r :=
    refinementKernelRadius_pos _ _ hrho hr
  have hsle : refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho r ≤ rho := by
    unfold refinementKernelRadius
    have hcap : (1 : Real) ≤ refinementKernelCap (2*(k+1)*d) (3*(k+1)*d) rho r := by
      exact_mod_cast refinementKernelCap_pos _ _ hrho hr
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  let classOf : I → I := fun i => if hi : i ∈ A then (hcover i hi).choose else default
  have hclass : ∀ i ∈ A, classOf i ∈ J ∧
      ColumnListIdentity T L (refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho r)
        (anchors i) (anchors (classOf i)) := by
    intro i hi
    simpa only [classOf, dif_pos hi] using (hcover i hi).choose_spec
  refine ⟨J, hJA, hJ, classOf, hclass, ?_⟩
  intro i hi j hj heq
  have hiC := hclass i hi
  have hjC := hclass j hj
  apply columnListIdentity_trans_shrink X T L hrho hs hsle hT hL hzero
    (anchors i) (anchors (classOf i)) (anchors j) (ha i hi) (ha _ (hJA hiC.1)) (ha j hj)
    (by rw [hlen i hi, hlen j hj]; omega)
    (by rw [hlen _ (hJA hiC.1)]) hiC.2 _ hN2
  rw [heq]
  exact hjC.2.symm

end LeanProofs.GowersSzemeredi
