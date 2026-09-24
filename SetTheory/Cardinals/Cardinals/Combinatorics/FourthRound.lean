/-
  COMBINATORIAL CORES OF THE FOURTH-ROUND RESULTS (synthesis §14: the Prikry model).

  Everything here is elementary and fully proved; no forcing is involved.

  * `fixed_of_insertion`: the logic of "decide, then insert" (Lemma 14.1(c));
  * `finiteChange_realize_insert`: inserting one point into a sequence rotates the
    block-coded tuple `a_i = {a_n + π⁻ⁿ(i)}` by `π`, up to finite change
    (proof of Theorem 14.4);
  * the finite algebra of Theorem 14.5 is `FiniteCycles.no_equivariant_selectors`;
  * `shift_ne`: no nontrivial shift fixes an ultrafilter on `ℤ` (Theorem 14.6(1));
  * `no_finite_invariant`: a nonempty finite set is not invariant under translation by an
    element of infinite order (Theorem 14.6(2),(3): phases in `ℤ` or in the profinite
    completion);
  * `residue_law`: a weight on `ℤ/ℓ` of total mass `1` invariant under the shift by `t`,
    `t` coprime to `ℓ`, is uniform (Theorem 14.6(4)).
-/
import Cardinals.FiniteLabel

universe u

namespace Cardinals.FourthRound

open Cardinals.Ultraexacting Cardinals.FiniteLabel

/-! ### Decide, then insert -/

/-- If a value is decided (the same for the two generics `a`, `d`) and insertion acts on
it by `ρ`, then it is fixed by `ρ`. -/
theorem fixed_of_insertion {Y : Type*} (ρ : Y → Y) (Ta Td : Y) (hdec : Td = Ta)
    (hrot : Td = ρ Ta) : ρ Ta = Ta := by
  rw [← hrot, hdec]

/-! ### Insertion rotates block-coded tuples -/

/-- If `d` is obtained from `a` by inserting one point (so `d (n+1) = a n` from some
point on), then the `π i`-th coded set of `d` is a finite change of the `i`-th coded set
of `a`: the coded tuple of classes is rotated by `π`. -/
theorem finiteChange_realize_insert {m : ℕ} (a d : ℕ → Ordinal.{u}) (l : ℕ)
    (h : ∀ n, l ≤ n → d (n + 1) = a n) (π : Equiv.Perm (Fin m)) (i : Fin m) :
    FiniteChange (realize d π (π i)) (realize a π i) := by
  have hpow : ∀ n : ℕ, (π⁻¹ ^ (n + 1)) (π i) = (π⁻¹ ^ n) i := by
    intro n
    rw [pow_succ, Equiv.Perm.mul_apply]
    simp
  let fd : ℕ → Ordinal.{u} := fun n => d n + (((π⁻¹ ^ n) (π i) : Fin m) : ℕ)
  let fa : ℕ → Ordinal.{u} := fun n => a n + (((π⁻¹ ^ n) i : Fin m) : ℕ)
  have hstep : ∀ n, l ≤ n → fd (n + 1) = fa n := by
    intro n hn
    show d (n + 1) + _ = a n + _
    rw [h n hn, hpow]
  unfold FiniteChange
  refine (((Set.finite_le_nat l).image fd).union ((Set.finite_lt_nat l).image fa)).subset ?_
  rintro x (⟨⟨n, rfl⟩, hnot⟩ | ⟨⟨n, rfl⟩, hnot⟩)
  · left
    by_cases hn : n ≤ l
    · exact ⟨n, hn, rfl⟩
    · exfalso
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      exact hnot ⟨k, hstep k (by omega)⟩
  · right
    by_cases hn : n < l
    · exact ⟨n, hn, rfl⟩
    · exfalso
      exact hnot ⟨n + 1, (hstep n (by omega)).symm⟩

/-! ### Shifts of ultrafilters on the integers -/

/-- No nontrivial shift fixes an ultrafilter on `ℤ`. -/
theorem shift_ne (E : Ultrafilter ℤ) (j : ℤ) (hj : j ≠ 0) : E.map (fun n => n + j) ≠ E := by
  intro hE
  let A : Set ℤ := {n | Even (n / j)}
  have key : (fun n => n + j) ⁻¹' A = Aᶜ := by
    ext n
    have h1 : (n + j) / j = n / j + 1 := by
      have := Int.add_mul_ediv_right n 1 hj
      rwa [one_mul] at this
    simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff, A, h1]
    exact Int.even_add_one
  have hiff : A ∈ E ↔ Aᶜ ∈ E := by
    conv_lhs => rw [← hE, Ultrafilter.mem_map, key]
  rcases E.mem_or_compl_mem A with hA | hA
  · have := Filter.inter_mem hA (hiff.mp hA)
    rw [Set.inter_compl_self] at this
    exact Filter.empty_notMem _ this
  · have := Filter.inter_mem (hiff.mpr hA) hA
    rw [Set.inter_compl_self] at this
    exact Filter.empty_notMem _ this

/-! ### No finite invariant set of phases -/

/-- A nonempty finite subset of a group is not invariant under translation by an element
of infinite order.  (Applied to the phases of a definable family of ultrafilters, in `ℤ`
or in its profinite completion, and the translation by `1`.) -/
theorem no_finite_invariant {G : Type*} [AddGroup G] (g : G)
    (hg : ∀ n : ℕ, 0 < n → n • g ≠ 0) (H : Set G) (hfin : H.Finite) (hne : H.Nonempty)
    (hinv : ∀ y ∈ H, y + g ∈ H) : False := by
  obtain ⟨x, hx⟩ := hne
  have hmem : ∀ n : ℕ, x + n • g ∈ H := by
    intro n
    induction n with
    | zero => simpa using hx
    | succ n ih =>
      have := hinv _ ih
      rwa [add_assoc, ← succ_nsmul] at this
  have hinj : Function.Injective (fun n : ℕ => x + n • g) := by
    intro n k hnk
    have h1 : n • g = k • g := add_left_cancel hnk
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have h2 : (k - n) • g + n • g = k • g := by rw [← add_nsmul, Nat.sub_add_cancel hlt.le]
      rw [← h1] at h2
      exact hg (k - n) (by omega) (add_eq_right.mp h2)
    · have h2 : (n - k) • g + k • g = n • g := by rw [← add_nsmul, Nat.sub_add_cancel hlt.le]
      rw [h1] at h2
      exact hg (n - k) (by omega) (add_eq_right.mp h2)
  exact Set.infinite_of_injective_forall_mem hinj hmem hfin

/-! ### The residue law -/

/-- A weight on the residues modulo `l` of total mass `1` that is invariant under the
shift by `t`, with `t` coprime to `l`, gives every residue mass `1 / l`.  (A family of
`h` charges is permuted by insertion with orbits of length `t ≤ h`; for a prime `l > h`
the length `t` is coprime to `l`.) -/
theorem residue_law (l : ℕ) [NeZero l] (t : ℕ) (ht : Nat.Coprime t l) (μ : ZMod l → ℝ)
    (hshift : ∀ r, μ (r + t) = μ r) (hsum : ∑ r, μ r = 1) (r : ZMod l) : μ r = 1 / l := by
  have hmul : ∀ k : ℕ, μ ((k : ZMod l) * t) = μ 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.cast_succ, add_mul, one_mul, hshift, ih]
  have hconst : ∀ r, μ r = μ 0 := by
    intro r
    have hunit : (t : ZMod l) * (t : ZMod l)⁻¹ = 1 := ZMod.coe_mul_inv_eq_one t ht
    have hr : r = (((r * (t : ZMod l)⁻¹).val : ℕ) : ZMod l) * t := by
      rw [ZMod.natCast_zmod_val, mul_assoc, mul_comm ((t : ZMod l)⁻¹), hunit, mul_one]
    rw [hr]
    exact hmul _
  have hl : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne l)
  have hm : μ 0 * l = 1 := by
    rw [← hsum, Finset.sum_congr rfl (fun r _ => hconst r)]
    simp [ZMod.card, mul_comm]
  rw [hconst r, eq_div_iff hl]
  exact hm

end Cardinals.FourthRound
