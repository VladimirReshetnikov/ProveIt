import OAI.Combinatorics.Progressions.Lattices.CubeResidueSupport

namespace OAI

section

namespace Erdos3

theorem integerScalarCube_mono {I : Type*} [Fintype I] {K L : ℕ}
    (hKL : K ≤ L) {x : Option I → ℤ} (hx : IntegerScalarCube K x) : IntegerScalarCube L x := by
  intro t
  exact ⟨(hx t).1, (hx t).2.trans_le (by exact_mod_cast hKL)⟩

def integerScalarCubeBoxEmbed (I : Type*) (K L : ℕ) (hKL : K ≤ L)
    (x : IntegerScalarCubeBox I K) : IntegerScalarCubeBox I L := fun i =>
  ⟨(x i : ℤ), Finset.mem_Ico.mpr (by
    have hi := Finset.mem_Ico.mp (x i).property
    constructor <;> omega)⟩

noncomputable def scalarCubeWindowResidueSet (I : Type*) [Fintype I]
    (L K : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) :
    Finset (IntegerScalarCubeBox I L) := by
  classical
  exact Finset.univ.filter (fun x => IntegerScalarCube K (fun i => (x i : ℤ)) ∧
    ∀ i, ((x i : ℤ) : ZMod (m i)) = r i)

theorem mem_scalarCubeWindowResidueSet {I : Type*} [Fintype I]
    (L K : ℕ) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (x : IntegerScalarCubeBox I L) :
    x ∈ scalarCubeWindowResidueSet I L K m r ↔
      IntegerScalarCube K (fun i => (x i : ℤ)) ∧ ∀ i, ((x i : ℤ) : ZMod (m i)) = r i := by
  classical
  simp only [scalarCubeWindowResidueSet, Finset.mem_filter, Finset.mem_univ, true_and]

theorem scalarCubeWindowResidueSet_subset {I : Type*} [Fintype I]
    (L K : ℕ) (hKL : K ≤ L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) :
    scalarCubeWindowResidueSet I L K m r ⊆ integerScalarCubeSet I L := by
  intro x hx
  exact (mem_integerScalarCubeSet L x).mpr
    (integerScalarCube_mono hKL ((mem_scalarCubeWindowResidueSet L K m r x).mp hx).1)

noncomputable def scalarCubeWindowResidueEquiv (I : Type*) [Fintype I] [DecidableEq I]
    (L K : ℕ) (hKL : K ≤ L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) :
    ↥((integerScalarCubeSet I K) ∩ scalarCubeResidueSet I K m r) ≃
      ↥(scalarCubeWindowResidueSet I L K m r) where
  toFun x := by
    have hx := Finset.mem_inter.mp x.property
    exact ⟨integerScalarCubeBoxEmbed I K L hKL x.val,
      (mem_scalarCubeWindowResidueSet L K m r _).mpr
        ⟨(mem_integerScalarCubeSet K x.val).mp hx.1,
          (mem_scalarCubeResidueSet K m r x.val).mp hx.2⟩⟩
  invFun y := by
    have hy := (mem_scalarCubeWindowResidueSet L K m r y.val).mp y.property
    let x : IntegerScalarCubeBox I K := fun i =>
      ⟨(y.val i : ℤ), Finset.mem_Ico.mpr
        ⟨(integerScalarCube_coordinates hy.1 i).1.le, (integerScalarCube_coordinates hy.1 i).2⟩⟩
    exact ⟨x, Finset.mem_inter.mpr ⟨(mem_integerScalarCubeSet K x).mpr hy.1,
      (mem_scalarCubeResidueSet K m r x).mpr hy.2⟩⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl
  right_inv y := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    rfl

theorem scalarCubeWindowResidueSet_card (I : Type*) [Fintype I] [DecidableEq I]
    (L K : ℕ) (hKL : K ≤ L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) :
    (scalarCubeWindowResidueSet I L K m r).card =
      ((integerScalarCubeSet I K) ∩ scalarCubeResidueSet I K m r).card := by
  simpa only [Fintype.card_coe] using
    (Fintype.card_congr (scalarCubeWindowResidueEquiv I L K hKL m r)).symm

theorem scalarCubeWindowResidueSet_card_lower (I : Type*) [Fintype I] [DecidableEq I]
    (L K M H : ℕ) (hKL : K ≤ L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hH : 0 < H)
    (hbudget : (Fintype.card I + 1) * (M * H) ≤ K) :
    H ^ (Fintype.card I + 1) ≤ (scalarCubeWindowResidueSet I L K m r).card := by
  rw [scalarCubeWindowResidueSet_card I L K hKL m r]
  exact scalarCubeResidueSet_card_lower I K M H m r hm hmM hH hbudget

end Erdos3

end

end OAI
