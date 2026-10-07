import OAI.Combinatorics.Progressions.Lattices.SpatialSiteResidueIdentity
import OAI.Combinatorics.Progressions.Lattices.TupleResidueConditioning
import OAI.Combinatorics.Progressions.Probability.SmoothVectorSpatialLaw

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix

theorem rootDifferenceMatrix_vertex {I J : Type*} [Fintype J]
    (root : J → ℤ) (D : Matrix I J ℤ) (a : ℤ) (v : J → ℤ) (t : Finset I) :
    a + ∑ j, integerAffineCube root D t j * v j =
      (rootDifferenceMatrix root D *ᵥ Sum.elim (fun _ : Unit => a) v) (Sum.inl ()) +
        ∑ i ∈ t, (rootDifferenceMatrix root D *ᵥ Sum.elim (fun _ : Unit => a) v) (Sum.inr i) := by
  rw [rootDifferenceMatrix_mulVec]
  have hs : (∑ j, ∑ i ∈ t, D i j * v j) = ∑ i ∈ t, ∑ j, D i j * v j := Finset.sum_comm
  simp only [integerAffineCube, add_mul, Finset.sum_add_distrib, Finset.sum_mul,
    Sum.elim_inl, Sum.elim_inr, Matrix.mulVec, dotProduct]
  rw [hs]
  ring

theorem integerAffineCube_shifted_scalar {I J : Type*} [Fintype I] {L : ℕ}
    (x : J → IntegerScalarCubeBox I L) (c : J → ℤ) (t : Finset I) :
    integerAffineCube (fun j => c j + (x j none : ℤ)) (scalarCubeDifferenceMatrix x) t =
      fun j => c j + integerScalarCubeValue (fun i => (x j i : ℤ)) t := by
  funext j
  change (c j + (x j none : ℤ)) + ∑ i ∈ t, (x j (some i) : ℤ) =
    c j + ((x j none : ℤ) + ∑ i ∈ t, (x j (some i) : ℤ))
  ring

theorem scalarCubeWindow_root_bound {I : Type*} [Fintype I] {L K : ℕ}
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (x : IntegerScalarCubeBox I L) (c : ℤ)
    (hc : 0 ≤ c) (hcK : c + K ≤ L) (hx : x ∈ scalarCubeWindowResidueSet I L K m r) :
    |c + (x none : ℤ)| ≤ (L : ℤ) := by
  have h := ((mem_scalarCubeWindowResidueSet L K m r x).mp hx).1 ∅
  simp only [integerScalarCubeValue, Finset.sum_empty, add_zero] at h
  apply abs_le.mpr
  constructor <;> omega

theorem affineScalarCubeWindowWeights_root_bound {I : Type*} [Fintype I] [DecidableEq I]
    (L K M D : ℕ) (c : ℤ) (hL : 0 < L) (hKL : K ≤ L) (hDK : L ≤ D * K)
    (m : Option I → ℕ) (r : ∀ i, ZMod (m i)) (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M)
    (hsize : (Fintype.card I + 1) * M ≤ K) (x : IntegerScalarCubeBox I L)
    (hc : 0 ≤ c) (hcK : c + K ≤ L)
    (hx : (affineScalarCubeWindowWeights I L K M D c hL hKL hDK m r hm hmM hsize).weight x ≠ 0) :
    |c + (x none : ℤ)| ≤ (L : ℤ) := by
  classical
  apply scalarCubeWindow_root_bound m (shiftScalarCubeResidues c m r) x c hc hcK
  by_contra hnot
  apply hx
  simp only [affineScalarCubeWindowWeights, scalarCubeWindowWeights, FiniteProbabilityWeights.condition,
    hnot, ite_false, zero_div]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix BigOperators

def scalarTupleColumn {I : Type*} (c : ℤ) (x : Option I → ℤ) : (Unit ⊕ I) → ℤ :=
  Sum.elim (fun _ => c + x none) (fun i => x (some i))

def scalarTupleSpatialColumns {I N : Type*} (T : N → ℕ) (c : N → ℤ)
    (x : ∀ j, IntegerScalarCubeBox I (T j)) : Matrix (Unit ⊕ I) N ℤ :=
  tupleColumnMatrix (fun j x => scalarTupleColumn (c j) (fun i => (x i : ℤ))) x

theorem scalarTupleColumn_residue_iff {I : Type*} (c : ℤ) (x : Option I → ℤ)
    (m : ℕ) (r : (Unit ⊕ I) → ZMod m) :
    integerResidueMap (Unit ⊕ I) m (scalarTupleColumn c x) = r ↔
      ((c + x none : ℤ) : ZMod m) = r (.inl ()) ∧
      ∀ i, (x (some i) : ZMod m) = r (.inr i) := by
  constructor
  · intro h
    exact ⟨congrFun h (.inl ()), fun i => congrFun h (.inr i)⟩
  · rintro ⟨hroot, hdiff⟩
    funext i
    cases i with
    | inl i => cases i; exact hroot
    | inr i => exact hdiff i

theorem scalarTupleColumn_bound {I : Type*} {T : ℕ} (c : ℤ)
    (x : IntegerScalarCubeBox I T) (i : Unit ⊕ I) :
    |scalarTupleColumn c (fun k => (x k : ℤ)) i| ≤ |c| + (T : ℤ) := by
  have hx (k : Option I) : |(x k : ℤ)| ≤ (T : ℤ) := by
    have h := Finset.mem_Ico.mp (x k).property
    exact abs_le.mpr ⟨h.1, h.2.le⟩
  cases i with
  | inl i => exact (abs_add_le c (x none)).trans (add_le_add le_rfl (hx none))
  | inr i => exact (hx (some i)).trans (le_add_of_nonneg_left (abs_nonneg c))

theorem scalarTupleSpatialColumns_scaled_bound {I N : Type*}
    (T : N → ℕ) (c : N → ℤ) (Q : N → ℝ) (hQ : ∀ j, 0 ≤ Q j) {ξ H : ℝ}
    (hwidth : ∀ j, ((|c j| : ℤ) + (T j : ℤ) : ℝ) * Q j ≤ ξ * H)
    (x : ∀ j, IntegerScalarCubeBox I (T j)) (i : Unit ⊕ I) (j : N) :
    |(scalarTupleSpatialColumns T c x i j : ℝ)| * Q j ≤ ξ * H := by
  have h : |(scalarTupleSpatialColumns T c x i j : ℝ)| ≤ ((|c j| : ℤ) + (T j : ℤ) : ℝ) := by
    exact_mod_cast scalarTupleColumn_bound (c j) (x j) i
  exact (mul_le_mul_of_nonneg_right h (hQ j)).trans (hwidth j)

theorem scalarTupleSpatialColumns_vertex {I N : Type*} [Fintype I] [Fintype N]
    (T : N → ℕ) (c : N → ℤ) (x : ∀ j, IntegerScalarCubeBox I (T j))
    (v : N → ℤ) (t : Finset I) :
    (scalarTupleSpatialColumns T c x *ᵥ v) (.inl ()) +
        ∑ i ∈ t, (scalarTupleSpatialColumns T c x *ᵥ v) (.inr i) =
      ∑ j, (c j + integerScalarCubeValue (fun i => (x j i : ℤ)) t) * v j := by
  have hs : (∑ i ∈ t, ∑ j, (x j (some i) : ℤ) * v j) =
      ∑ j, ∑ i ∈ t, (x j (some i) : ℤ) * v j := Finset.sum_comm
  simp only [scalarTupleSpatialColumns, tupleColumnMatrix, scalarTupleColumn,
    Matrix.mulVec, dotProduct, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr,
    integerScalarCubeValue, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  rw [hs]
  ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Matrix

def principalSpatialColumns {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (y : PrincipalIntegerTuples B h α L) : Matrix (Unit ⊕ α) N ℤ :=
  scalarTupleSpatialColumns (fun n => L (index n)) c (fun n => y (index n))

def principalSpatialResidueColumns {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    (m : ℕ) (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) : Matrix (Unit ⊕ α) N (ZMod m) :=
  fun i n => Sum.elim (fun _ => (c n : ZMod m)+r (index n) none)
    (fun j => r (index n) (some j)) i

theorem principalSpatialColumns_residue {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (m : ℕ) (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (y : PrincipalIntegerTuples B h α L) :
    integerResidueMatrix (principalSpatialColumns c index y) m =
      principalSpatialResidueColumns m c index (principalResidueLabel m y) := by
  ext i n
  cases i <;> simp [integerResidueMatrix, principalSpatialColumns, scalarTupleSpatialColumns,
    tupleColumnMatrix, scalarTupleColumn, principalSpatialResidueColumns, principalResidueLabel]

theorem principalSpatialColumns_scaled_bound {D α N : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (c : N → ℤ) (index : N → PrincipalTupleIndex B h)
    (Q : N → ℝ) (hQ : ∀ n, 0 ≤ Q n) {ξ H : ℝ}
    (hwidth : ∀ n, ((|c n| : ℤ)+(L (index n) : ℤ) : ℝ)*Q n ≤ ξ*H)
    (y : PrincipalIntegerTuples B h α L) (i : Unit ⊕ α) (n : N) :
    |(principalSpatialColumns c index y i n : ℝ)| * Q n ≤ ξ*H :=
  scalarTupleSpatialColumns_scaled_bound (fun n => L (index n)) c Q hQ hwidth (fun n => y (index n)) i n

theorem principalSpatialColumns_vertex {D α N : Type*} [Fintype α] [Fintype N]
    {B : D → Type*} {h : D → ℕ} {L : PrincipalTupleIndex B h → ℕ}
    (c : N → ℤ) (index : N → PrincipalTupleIndex B h) (y : PrincipalIntegerTuples B h α L)
    (v : N → ℤ) (t : Finset α) :
    (principalSpatialColumns c index y *ᵥ v) (.inl ()) +
      ∑ i ∈ t, (principalSpatialColumns c index y *ᵥ v) (.inr i) =
      ∑ n, (c n+integerScalarCubeValue (fun i => (y (index n) i : ℤ)) t)*v n :=
  scalarTupleSpatialColumns_vertex (fun n => L (index n)) c (fun n => y (index n)) v t

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem smoothVectorSpatial_site_error {D I J N : Type*}
    [Fintype D] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype N] [DecidableEq N]
    {L B : ℕ} {ρ ξ r : ℝ} (s : I ↪ J) (x : J → IntegerScalarCubeBox I L) (root : J → ℤ)
    (hB : 0 < B) (hL : 0 < L) (hx : GoodScalarKernelTuple s (1 / (B : ℝ)) B x)
    (hroot : ∀ j, |root j| ≤ (L : ℤ)) (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (C : D → Matrix (Unit ⊕ I) N ℤ) (H : D → ℝ) (Q : D → N → ℝ)
    (hH : ∀ d, 0 < H d) (hQ : ∀ d j, 0 < Q d j) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hC : ∀ d i j, |(C d i j : ℝ)| * Q d j ≤ ξ * H d)
    (hρ : 0 < ρ) (hscale : ∀ d, ρ ≤ H d / L) (hscaleQ : ∀ d j, ρ ≤ Q d j)
    (hlarge : smoothSpatialMeshThreshold I J N L ≤ ρ) (hr : 0 < r)
    (v : D → (Unit ⊕ I) → ℤ)
    (hv : ∀ d i, |((spatialStar (v d) i : ℤ) : ℝ) / H d| ≤ 1) :
    let A := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let A' := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hA := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hB)) hx
    let f := fun d => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hA
      (H d) L (hH d) (by exact_mod_cast hL)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ I)
    let E := smoothSpatialError N s B L ρ ξ
    ‖(((∏ d, ∏ _i : Unit ⊕ I, H d) *
        (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x) C H L Q hH
          (by exact_mod_cast hL) hQ v).toReal : ℝ) : ℂ) -
      ∏ d, spatialSiteApprox A (Matrix.fromCols A' (liftResidueMatrix (integerResidueMatrix (C d) m)))
        m (f d) (H d) 1 r (v d)‖ ≤
      Fintype.card D * (E + 4*G*smoothSpatialDensityLip s B*r) *
        (1 + G*smoothSpatialDensityCap s B + E)^Fintype.card D := by
  dsimp only
  rw [smoothVectorSpatialOutputLaw_scaled]
  have hpfull (d : D) : integerScalarLattice (Unit ⊕ I) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) (C d)) := by
    rw [pivotFullImage_split]
    exact hp.trans le_sup_left
  have hi (d : D) :
      ((pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (Matrix.fromCols (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) (C d))).toAddSubgroup.index : ℝ)
        ≤ (m : ℝ)^Fintype.card (Unit ⊕ I) := by
    exact_mod_cast residueLatticeImage_index_le _ m (hpfull d)
  have h := vectorSpatialSiteApprox_error _ _ m hpfull _
    (fun d => (smoothSpatialKernelDensity_bounds s x root hB hL (hH d) hx hroot).2)
    H _ (by positivity) (smoothSpatialDensityCap_nonneg s B)
    (smoothSpatialError_nonneg N s B L hρ.le hξ0) zero_lt_one hr hi
    (fun d => (smoothSpatialKernelDensity_bounds s x root hB hL (hH d) hx hroot).1)
    (fun d => smoothSpatial_original_error s x root hB hL (hH d) hx hroot (C d) (Q d) (hQ d)
      hξ0 hξ1 (hC d) hρ (hscale d) (hscaleQ d) hlarge) v hv
  rw [Real.coe_toNNReal _ (smoothSpatialDensityLip_nonneg s B)] at h
  have hid (d : D) := congrFun (spatialSiteApprox_eq_residue
    (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
    (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s) (C d) m hp
    (smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x)
      (goodScalarKernelTuple_spatial_det_ne_zero s x root
        (one_div_pos.mpr (by exact_mod_cast hB)) hx) (H d) L (hH d) (by exact_mod_cast hL))
    (H d) 1 r) (v d)
  simpa only [← hid] using h

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem principalVectorSpatial_site_error {D A α J N : Type*}
    [Fintype A] [Fintype α] [DecidableEq α] [Fintype J] [DecidableEq J]
    [Fintype N] [DecidableEq N] {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} {ℓ M : ℕ} {ρ ξ r : ℝ}
    (s : α ↪ J) (x : J → IntegerScalarCubeBox α ℓ) (root : J → ℤ)
    (hM : 0 < M) (hℓ : 0 < ℓ) (hx : GoodScalarKernelTuple s (1/(M : ℝ)) M x)
    (hroot : ∀ j, |root j| ≤ (ℓ : ℤ)) (m : ℕ) [NeZero m]
    (hp : integerScalarLattice (Unit ⊕ α) (m : ℤ) ≤
      pivotFullImage (selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s)
        (selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s))
    (c : A → N → ℤ) (index : A → N → PrincipalTupleIndex B h)
    (H : A → ℝ) (Q : A → N → ℝ) (hH : ∀ a, 0 < H a) (hQ : ∀ a n, 0 < Q a n)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hwidth : ∀ a n, ((|c a n| : ℤ)+(L (index a n) : ℤ) : ℝ)*Q a n ≤ ξ*H a)
    (hρ : 0 < ρ) (hscale : ∀ a, ρ ≤ H a/ℓ) (hscaleQ : ∀ a n, ρ ≤ Q a n)
    (hlarge : smoothSpatialMeshThreshold α J N ℓ ≤ ρ) (hr : 0 < r)
    (y : PrincipalIntegerTuples B h α L) (v : A → (Unit ⊕ α) → ℤ)
    (hv : ∀ a i, |((spatialStar (v a) i : ℤ) : ℝ)/H a| ≤ 1) :
    let P := selectedSpatialPivot root (scalarCubeDifferenceMatrix x) s
    let F := selectedSpatialFreeColumns root (scalarCubeDifferenceMatrix x) s
    let hP := goodScalarKernelTuple_spatial_det_ne_zero s x root
      (one_div_pos.mpr (by exact_mod_cast hM)) hx
    let f := fun a => smoothSpatialKernelDensity s root (scalarCubeDifferenceMatrix x) hP
      (H a) ℓ (hH a) (by exact_mod_cast hℓ)
    let G := (m : ℝ)^Fintype.card (Unit ⊕ α)
    let E := smoothSpatialError N s M ℓ ρ ξ
    ‖(((∏ a, ∏ _i : Unit ⊕ α, H a)*
        (smoothVectorSpatialOutputLaw root (scalarCubeDifferenceMatrix x)
          (fun a => principalSpatialColumns (c a) (index a) y) H ℓ Q hH
          (by exact_mod_cast hℓ) hQ v).toReal : ℝ) : ℂ) -
      ∏ a, spatialSiteApprox P
        (Matrix.fromCols F (liftResidueMatrix
          (principalSpatialResidueColumns m (c a) (index a) (principalResidueLabel m y))))
        m (f a) (H a) 1 r (v a)‖ ≤
      Fintype.card A*(E+4*G*smoothSpatialDensityLip s M*r)*
        (1+G*smoothSpatialDensityCap s M+E)^Fintype.card A := by
  dsimp only
  have he := smoothVectorSpatial_site_error s x root hM hℓ hx hroot m hp
    (fun a => principalSpatialColumns (c a) (index a) y) H Q hH hQ hξ0 hξ1
    (fun a i n => principalSpatialColumns_scaled_bound (c a) (index a) (Q a)
      (fun n => (hQ a n).le) (hwidth a) y i n)
    hρ hscale hscaleQ hlarge hr v hv
  simpa only [principalSpatialColumns_residue] using he

end Erdos3

end

end OAI
