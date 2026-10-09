import GowersSzemeredi.Proofs16DenseFamilyPacking
import GowersSzemeredi.Proofs16ColumnWordValueFibres
import GowersSzemeredi.Proofs16ColumnListIdentity

/-! A bounded collection of anchor lists models all lists with dense
representations in one fixed-value fibre. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem column_model_packing {I : Type*} {N d k : Nat} [NeZero N] [Fact N.Prime]
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
    (hN : refinementKernelCap (2*(k+1)*d) (3*(k+1)*d) rho r < N) :
    ∃ J ⊆ A, (J.card : Real)*delta ≤ 1 ∧
      ∀ i ∈ A, ∃ j ∈ J,
        ColumnListIdentity T L (refinementKernelRadius (2*(k+1)*d) (3*(k+1)*d) rho r)
          (anchors i) (anchors j) := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  obtain ⟨J,hJA,_,hJ,hcover⟩ := dense_family_packing A (columnWordValueFibre (k := k) c) F hd
    (by positivity : (0 : Real) < (N : Real)^(3*k+2))
    (by exact_mod_cast columnWordValueFibre_card_le (k := k) c)
    (fun i hi w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,hval i hi w hw⟩) hmass
  refine ⟨J,hJA,hJ,?_⟩
  intro i hi
  obtain ⟨j,hj,w,hwF⟩ := hcover i hi
  obtain ⟨hwi,hwj⟩ := Finset.mem_inter.mp hwF
  refine ⟨j,hj,?_⟩
  apply columnListIdentity_trans_shrink X T L hrho hr hrle hT hL hzero
    (anchors i) (columnWordEntries w) (anchors j) (ha i hi) (hw i hi w hwi) (ha j (hJA hj))
    (by rw [hlen i hi,hlen j (hJA hj)]; omega)
    (by rw [columnWordEntries_length])
    (hident i hi w hwi) (hident j (hJA hj) w hwj).symm hN

end LeanProofs.GowersSzemeredi
