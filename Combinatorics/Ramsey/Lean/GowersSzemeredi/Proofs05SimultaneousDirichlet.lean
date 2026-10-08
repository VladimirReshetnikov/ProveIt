import GowersSzemeredi.Definitions

/-! Simultaneous Dirichlet approximation in `ZMod N`.

For any `K` multipliers `a i ∈ ZMod N` and any `M ≥ 1`, there is
`1 ≤ u ≤ M^K` with `|u · a i| ≤ N / M` for every `i` (centered absolute
value). The proof is pigeonhole on the `M^K` cells of the discrete torus.

This is the degree-one case of the simultaneous-small-values principle in
research notes J.3 and Part B. In terms of `t = M^K` the exponent is `1/K`:
polynomial in the number of forms. Gowers's per-form iteration (Corollary
5.11, Lemma 16.1) loses a fixed factor in the exponent for every form, so
its exponent is exponential in the number of forms. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The cell of `x ∈ ZMod N` among `M` consecutive intervals of `[0, N)`. -/
def dirichletCell {N : Nat} [NeZero N] (M : Nat) [NeZero M] (x : ZMod N) : Fin M :=
  ⟨x.val * M / N, Nat.div_lt_of_lt_mul (by
    have hx : x.val < N := ZMod.val_lt x
    have hM : 0 < M := NeZero.pos M
    calc x.val * M < N * M := Nat.mul_lt_mul_of_pos_right hx hM
      _ = N * M := rfl)⟩

/-- The centered absolute value is symmetric. -/
theorem centeredAbs_sub_comm {N : Nat} (x y : ZMod N) :
    centeredAbs (x - y) = centeredAbs (y - x) := by
  unfold centeredAbs
  rw [show y - x = -(x - y) by ring, ZMod.natAbs_valMinAbs_neg]

/-- The centered absolute value is at most the plain value. -/
theorem centeredAbs_le_val {N : Nat} [NeZero N] (x : ZMod N) : centeredAbs x ≤ x.val := by
  unfold centeredAbs
  rw [ZMod.valMinAbs_natAbs_eq_min]
  exact min_le_left _ _

theorem dirichletCell_close_of_le {N : Nat} [NeZero N] {M : Nat} [NeZero M] {x y : ZMod N}
    (h : dirichletCell M x = dirichletCell M y) (hyx : y.val ≤ x.val) :
    centeredAbs (x - y) * M < N := by
  have hN : 0 < N := NeZero.pos N
  have hcell : x.val * M / N = y.val * M / N := congrArg Fin.val h
  have h1 := Nat.div_add_mod (x.val * M) N
  have h2 := Nat.div_add_mod (y.val * M) N
  have hm1 := Nat.mod_lt (x.val * M) hN
  have hle : y.val * M ≤ x.val * M := Nat.mul_le_mul_right M hyx
  have hdiff : (x.val - y.val) * M < N := by
    rw [Nat.sub_mul]
    rw [hcell] at h1
    omega
  have hval : (x - y).val = x.val - y.val := ZMod.val_sub hyx
  calc centeredAbs (x - y) * M ≤ (x - y).val * M :=
        Nat.mul_le_mul_right M (centeredAbs_le_val _)
    _ = (x.val - y.val) * M := by rw [hval]
    _ < N := hdiff

/-- Two points in the same cell differ by less than `N / M`. -/
theorem dirichletCell_close {N : Nat} [NeZero N] {M : Nat} [NeZero M] {x y : ZMod N}
    (h : dirichletCell M x = dirichletCell M y) :
    centeredAbs (x - y) * M < N := by
  rcases le_total y.val x.val with hyx | hxy
  · exact dirichletCell_close_of_le h hyx
  · rw [centeredAbs_sub_comm]
    exact dirichletCell_close_of_le h.symm hxy

/-- **Simultaneous Dirichlet approximation in `ZMod N`.** Any `K`
multipliers are simultaneously smaller than `N / M` after multiplying by a
common `1 ≤ u ≤ M^K`. -/
theorem simultaneous_small_multiplier {N K M : Nat} [NeZero N] [NeZero M]
    (a : Fin K → ZMod N) :
    ∃ u : Nat, 0 < u ∧ u ≤ M ^ K ∧ ∀ i, centeredAbs ((u : ZMod N) * a i) * M < N := by
  classical
  let f : Nat → (Fin K → Fin M) := fun u i => dirichletCell M ((u : ZMod N) * a i)
  have hcard : (Finset.univ : Finset (Fin K → Fin M)).card < (Finset.range (M ^ K + 1)).card := by
    simp
  obtain ⟨u₁, hu₁, u₂, hu₂, hne, hf⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (f := f)
      (fun _ _ => Finset.mem_univ _)
  have hu₁' : u₁ ≤ M ^ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu₁)
  have hu₂' : u₂ ≤ M ^ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hu₂)
  -- order the two indices
  have key : ∀ v w : Nat, v ≤ M ^ K → w < v → f v = f w →
      ∃ u : Nat, 0 < u ∧ u ≤ M ^ K ∧ ∀ i, centeredAbs ((u : ZMod N) * a i) * M < N := by
    intro v w hv hwv hfvw
    refine ⟨v - w, by omega, by omega, fun i => ?_⟩
    have hcell : dirichletCell M ((v : ZMod N) * a i) = dirichletCell M ((w : ZMod N) * a i) :=
      congrFun hfvw i
    have hcast : ((v - w : Nat) : ZMod N) * a i = (v : ZMod N) * a i - (w : ZMod N) * a i := by
      rw [Nat.cast_sub hwv.le, sub_mul]
    rw [hcast]
    exact dirichletCell_close hcell
  rcases lt_or_gt_of_ne hne with h | h
  · exact key u₂ u₁ hu₂' h hf.symm
  · exact key u₁ u₂ hu₁' h hf

end LeanProofs.GowersSzemeredi
