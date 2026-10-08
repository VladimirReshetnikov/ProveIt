import GowersSzemeredi.Proofs16ReadoutMultilinear
import GowersSzemeredi.Proofs16PolyBaseCase

/-! Good partitions give multiply-linear covers, with no loss set.

`MultiplyLinearWith` asks, for every proper box `P` and every `θ`, for a
partition of `P` into proper cells of width at least `P.width^E`. On each
cell, the graph over a `(1 − θ)`-dense set `H` must be covered by few
multilinear maps.

Take the graph `Γ` of a Freiman bihomomorphism `Φ` on `V`, restricted to a
set `S`. Call a cell *good* if it misses `S` or lies inside `V`. Then one
multilinear map covers each good cell, and `H = P` works:
* a cell that misses `S` carries no graph points;
* on a cell inside `V`, `Φ` is bi-affine (`freiman_bihom_biaffine_on_product`),
  hence multilinear in the coordinates.

So no `θ`-budget is spent, and no regularity of `V` is needed. With the deep
form of Milićević's structure (`Proofs16DeepAgreement`), take `S = V(ρ/2)`.
A cell meeting `V(ρ/2)`, on which every variety condition oscillates by at
most `ρN/2` between any two points, lies in `V(ρ)`
(`Proofs16CellOscillation`). The remaining input is therefore the existence of
good partitions (`GoodPartitionsExist`), stated here as a hypothesis.

* `biaffine_of_affine_rows_cols_any`, `freiman_bihom_biaffine_on_product_any`,
  `freiman_bihom_multilinearOn_product_any`: the readout for every length,
  including width-one cells.
* `mem_box_two`: membership in a two-dimensional `Box`.
* `multilinearOn_box_of_subset`: for prime `N`, a Freiman bihomomorphism on
  `V` is `MultilinearOn` every box inside `V`. A zero common difference
  makes the box a single point.
* `cell_cover_of_good`, `multiplyLinearWith_of_good_partitions`. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

open Classical

/-- Affine rows and columns give the bi-affine formula, for all lengths. -/
theorem biaffine_of_affine_rows_cols_any {G : Type*} [AddCommGroup G] (f : Nat → Nat → G)
    (L₁ L₂ : Nat)
    (hrow : ∀ j, j < L₂ → ∀ i, i < L₁ → f i j = f 0 j + i • (f 1 j - f 0 j))
    (hcol : ∀ i, i < L₁ → ∀ j, j < L₂ → f i j = f i 0 + j • (f i 1 - f i 0)) :
    ∀ i j, i < L₁ → j < L₂ →
      f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
        (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) := by
  intro i j hi hj
  by_cases h₁ : 2 ≤ L₁
  · by_cases h₂ : 2 ≤ L₂
    · exact biaffine_of_affine_rows_cols f L₁ L₂ hrow hcol h₁ h₂ i j hi hj
    · have hj0 : j = 0 := by omega
      subst hj0
      rw [hrow 0 hj i hi]
      simp
  · have hi0 : i = 0 := by omega
    subst hi0
    rw [hcol 0 hi j hj]
    simp

/-- **Readout, all lengths.** -/
theorem freiman_bihom_biaffine_on_product_any {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0})
    (a d b e : ZMod N) (L₁ L₂ : Nat)
    (hsub : ∀ i j, i < L₁ → j < L₂ → (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V) :
    let f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
    ∀ i j, i < L₁ → j < L₂ →
      f i j = f 0 0 + i • (f 1 0 - f 0 0) + j • (f 0 1 - f 0 0) +
        (i * j) • (f 1 1 - f 1 0 - f 0 1 + f 0 0) := by
  intro f
  apply biaffine_of_affine_rows_cols_any f L₁ L₂
  · intro j hj
    apply affine_of_second_difference (fun i => f i j) L₁
    intro i hi
    have hq := hΦ.1 (a + ((i + 2 : Nat) : ZMod N) * d) (a + (i : ZMod N) * d)
      (a + ((i + 1 : Nat) : ZMod N) * d) (a + ((i + 1 : Nat) : ZMod N) * d)
      (b + (j : ZMod N) * e) (by push_cast; ring)
      (hsub _ _ hi hj) (hsub _ _ (by omega) hj) (hsub _ _ (by omega) hj) (hsub _ _ (by omega) hj)
    have hq0 : f (i + 2) j + f i j - f (i + 1) j - f (i + 1) j = 0 := hq
    show f (i + 2) j - f (i + 1) j = f (i + 1) j - f i j
    linear_combination hq0
  · intro i hi
    apply affine_of_second_difference (fun j => f i j) L₂
    intro j hj
    have hq := hΦ.2 (a + (i : ZMod N) * d) (b + ((j + 2 : Nat) : ZMod N) * e) (b + (j : ZMod N) * e)
      (b + ((j + 1 : Nat) : ZMod N) * e) (b + ((j + 1 : Nat) : ZMod N) * e)
      (by push_cast; ring)
      (hsub _ _ hi hj) (hsub _ _ hi (by omega)) (hsub _ _ hi (by omega)) (hsub _ _ hi (by omega))
    have hq0 : f i (j + 2) + f i j - f i (j + 1) - f i (j + 1) = 0 := hq
    show f i (j + 2) - f i (j + 1) = f i (j + 1) - f i j
    linear_combination hq0

/-- **Readout in multilinear form, all lengths.** -/
theorem freiman_bihom_multilinearOn_product_any {N : Nat} {V : Finset (ZMod N × ZMod N)}
    {Φ : ZMod N × ZMod N → ZMod N} (hΦ : IsEBihomomorphism V Φ {0})
    (a d b e : ZMod N) (hd : IsUnit d) (he : IsUnit e) (L₁ L₂ : Nat)
    (hsub : ∀ i j, i < L₁ → j < L₂ → (a + (i : ZMod N) * d, b + (j : ZMod N) * e) ∈ V) :
    MultilinearOn ((Finset.range L₁ ×ˢ Finset.range L₂).image fun ij =>
        (![a + (ij.1 : ZMod N) * d, b + (ij.2 : ZMod N) * e] : Point N 2))
      (fun x => Φ (x 0, x 1)) := by
  have hba := freiman_bihom_biaffine_on_product_any hΦ a d b e L₁ L₂ hsub
  set f : Nat → Nat → ZMod N := fun i j => Φ (a + (i : ZMod N) * d, b + (j : ZMod N) * e)
  set A := f 0 0
  set B := f 1 0 - f 0 0
  set C := f 0 1 - f 0 0
  set D := f 1 1 - f 1 0 - f 0 1 + f 0 0
  obtain ⟨di, hdi⟩ := hd.exists_left_inv
  obtain ⟨ei, hei⟩ := he.exists_left_inv
  refine ⟨fun x : Point N 2 =>
      (A - B * di * a - C * ei * b + D * di * ei * (a * b)) + (B * di - D * di * ei * b) * x 0 +
        (C * ei - D * di * ei * a) * x 1 + (D * di * ei) * (x 0 * x 1),
    isMultilinear_two _ _ _ _, ?_⟩
  intro x hx
  obtain ⟨⟨i, j⟩, hij, rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hij
  have hi' : i < L₁ := Finset.mem_range.mp hi
  have hj' : j < L₂ := Finset.mem_range.mp hj
  have h := hba i j hi' hj'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  change f i j = _
  rw [h]
  simp only [nsmul_eq_mul]
  push_cast
  linear_combination (-(B * (i : ZMod N)) - D * (i : ZMod N) * (j : ZMod N)) * hdi +
    (-(C * (j : ZMod N)) - D * (i : ZMod N) * (j : ZMod N) * (di * d)) * hei

/-- Membership in a two-dimensional box. -/
theorem mem_box_two {N : Nat} [NeZero N] (Q : Box N 2) (x : Point N 2) :
    x ∈ Q.carrier ↔
      (∃ i, i < (Q.axis 0).length ∧ (Q.axis 0).start + (i : ZMod N) * Q.commonDiff = x 0) ∧
      (∃ j, j < (Q.axis 1).length ∧ (Q.axis 1).start + (j : ZMod N) * Q.commonDiff = x 1) := by
  have hax : ∀ (t : Fin 2) (z : ZMod N), z ∈ (Q.axis t).carrier ↔
      ∃ i, i < (Q.axis t).length ∧ (Q.axis t).start + (i : ZMod N) * Q.commonDiff = z := by
    intro t z
    unfold ModAP.carrier
    rw [← Q.axis_step t]
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  unfold Box.carrier
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.forall_fin_two]
  rw [hax 0, hax 1]

/-- **Boxes inside `V` are read out multilinearly.** -/
theorem multilinearOn_box_of_subset {N : Nat} [NeZero N] [Fact N.Prime]
    {V : Finset (ZMod N × ZMod N)} {Φ : ZMod N × ZMod N → ZMod N}
    (hΦ : IsEBihomomorphism V Φ {0}) (Q : Box N 2)
    (hsub : ∀ x ∈ Q.carrier, (x 0, x 1) ∈ V) :
    MultilinearOn Q.carrier (fun x => Φ (x 0, x 1)) := by
  set a := (Q.axis 0).start
  set b := (Q.axis 1).start
  set d := Q.commonDiff
  by_cases hd : d = 0
  · refine ⟨fun x : Point N 2 => Φ (a, b) + 0 * x 0 + 0 * x 1 + 0 * (x 0 * x 1),
      isMultilinear_two _ _ _ _, ?_⟩
    intro x hx
    obtain ⟨⟨i, _, hi⟩, ⟨j, _, hj⟩⟩ := (mem_box_two Q x).mp hx
    have hd' : Q.commonDiff = 0 := hd
    rw [hd', mul_zero, add_zero] at hi hj
    show Φ (x 0, x 1) = Φ (a, b) + 0 * x 0 + 0 * x 1 + 0 * (x 0 * x 1)
    rw [← hi, ← hj]
    simp only [zero_mul, add_zero]
    rfl
  · have hunit : IsUnit d := Ne.isUnit hd
    have hgrid : ∀ i j, i < (Q.axis 0).length → j < (Q.axis 1).length →
        (a + (i : ZMod N) * d, b + (j : ZMod N) * d) ∈ V := by
      intro i j hi hj
      have := hsub ![a + (i : ZMod N) * d, b + (j : ZMod N) * d]
        ((mem_box_two Q _).mpr ⟨⟨i, hi, rfl⟩, ⟨j, hj, rfl⟩⟩)
      simpa using this
    obtain ⟨mu, hmu, hag⟩ := freiman_bihom_multilinearOn_product_any hΦ a d b d hunit hunit
      (Q.axis 0).length (Q.axis 1).length hgrid
    refine ⟨mu, hmu, fun x hx => ?_⟩
    obtain ⟨⟨i, hi, hix⟩, ⟨j, hj, hjx⟩⟩ := (mem_box_two Q x).mp hx
    have hxeq : x = ![a + (i : ZMod N) * d, b + (j : ZMod N) * d] := by
      funext t
      fin_cases t
      · exact hix.symm
      · exact hjx.symm
    apply hag x
    rw [hxeq]
    exact Finset.mem_image.mpr ⟨(i, j), Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr hi, Finset.mem_range.mpr hj⟩, rfl⟩

/-- A cell is good for `(S, V)` if it misses `S` or lies inside `V`. -/
def CellGood {N : Nat} [NeZero N] (S V : Finset (ZMod N × ZMod N)) (Q : Box N 2) : Prop :=
  (∀ x ∈ Q.carrier, (x 0, x 1) ∉ S) ∨ (∀ x ∈ Q.carrier, (x 0, x 1) ∈ V)

/-- `Γ` is (part of) the graph of `Φ` over `S`. -/
def IsGraphOver {N : Nat} (Gamma : Finset (Point N 2 × ZMod N)) (S : Finset (ZMod N × ZMod N))
    (Φ : ZMod N × ZMod N → ZMod N) : Prop :=
  ∀ p ∈ Gamma, (p.1 0, p.1 1) ∈ S ∧ p.2 = Φ (p.1 0, p.1 1)

/-- One multilinear map covers the graph on a good cell. -/
theorem cell_cover_of_good {N : Nat} [NeZero N] [Fact N.Prime]
    {S V : Finset (ZMod N × ZMod N)} {Φ : ZMod N × ZMod N → ZMod N}
    (hΦ : IsEBihomomorphism V Φ {0}) {Gamma : Finset (Point N 2 × ZMod N)}
    (hΓ : IsGraphOver Gamma S Φ) (Q : Box N 2) (hgood : CellGood S V Q) :
    ∃ mu : Point N 2 → ZMod N, IsMultilinear mu ∧
      ∀ x ∈ Q.carrier, ∀ y, (x, y) ∈ Gamma → y = mu x := by
  rcases hgood with hmiss | hin
  · refine ⟨fun x : Point N 2 => 0 + 0 * x 0 + 0 * x 1 + 0 * (x 0 * x 1),
      isMultilinear_two _ _ _ _, ?_⟩
    intro x hx y hxy
    exact absurd (hΓ _ hxy).1 (hmiss x hx)
  · obtain ⟨mu, hmu, hag⟩ := multilinearOn_box_of_subset hΦ Q hin
    refine ⟨mu, hmu, fun x hx y hxy => ?_⟩
    have hy : y = Φ (x 0, x 1) := (hΓ _ hxy).2
    rw [hy]
    exact hag x hx

/-- Good partitions with the required widths exist for every proper box.
This is the remaining input of the variety route; it is not asserted. -/
def GoodPartitionsExist {N : Nat} [NeZero N] (Eb : Real → Real)
    (S V : Finset (ZMod N × ZMod N)) : Prop :=
  ∀ theta : Real, 0 < theta → theta ≤ 1 → ∀ P : Box N 2, P.IsProper →
    ∃ M : Nat, ∃ Q : Fin M → Box N 2,
      IsBoxPartition Q P ∧ (∀ j, (Q j).IsProper) ∧
      (∀ j, (P.width : Real) ^ (Eb theta) ≤ (Q j).width) ∧ ∀ j, CellGood S V (Q j)

/-- **Good partitions give multiply-linear covers**, with one map per cell
and loss set `H = P`. -/
theorem multiplyLinearWith_of_good_partitions {N : Nat} [NeZero N] [Fact N.Prime]
    {S V : Finset (ZMod N × ZMod N)} {Φ : ZMod N × ZMod N → ZMod N}
    (hΦ : IsEBihomomorphism V Φ {0}) {Gamma : Finset (Point N 2 × ZMod N)}
    (hΓ : IsGraphOver Gamma S Φ) (Qb Eb : Real → Real)
    (hQb : ∀ theta : Real, 0 < theta → theta ≤ 1 → 1 ≤ Qb theta)
    (hgood : GoodPartitionsExist Eb S V) :
    MultiplyLinearWith Qb Eb Gamma := by
  intro theta htheta htheta1 P hP
  obtain ⟨M, Q, hpart, hprop, hwid, hg⟩ := hgood theta htheta htheta1 P hP
  choose mu hmu hcov using fun j => cell_cover_of_good hΦ hΓ (Q j) (hg j)
  refine ⟨M, 1, P.carrier, Q, fun j _ => mu j, subset_rfl, ?_, hpart, hprop, ?_, hwid,
    fun j _ => hmu j, ?_⟩
  · have hc : (0 : Real) ≤ P.carrier.card := Nat.cast_nonneg _
    nlinarith
  · simpa using hQb theta htheta htheta1
  · intro j x hx _ y hxy
    exact ⟨0, hcov j x hx y hxy⟩

end LeanProofs.GowersSzemeredi
