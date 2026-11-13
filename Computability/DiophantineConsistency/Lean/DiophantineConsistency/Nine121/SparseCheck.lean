import DiophantineConsistency.Nine121.SparseExtraction
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Kernel-cheap certificates for sparse coefficient extraction

`SparseExtraction.coeff_sum_monomial` needs, for each target exponent `E`, the exact set of
interaction indices landing on `E`: for the quadratic part these are triples
`(i, j, p) ∈ Fin n × Fin n × Fin m` with `w i + w j + pos p = E`. Deciding that set by brute
force over all `n²m` triples is far too expensive for the kernel at `31·31·39` (it ran out of
memory). Here the inner loop over `p` is replaced by one bit test of a position mask `M`
(any `M` with `pos p` among its set bits will do; extra bits can only make the check fail, never
lie), and `p` is recovered from the pair `(i, j)` by injectivity of `pos`. The remaining loop
over pairs is a structural Bool recursion over the weight list (`chkI`, `chkJ`, `chk1`), and
`quad_iff`/`lin_iff` turn a `true` result into the exact membership characterisation.
`coeff_sum_monomial_list` is the list form of `coeff_sum_monomial`. -/
set_option autoImplicit false
namespace Nine121.SparseCheck
open Polynomial

/-- Inner pair loop: for weights `y` (index `j`) with `a + y ≤ E` and bit `E - (a + y)` set in
`M`, the pair `(i, j)` must be listed in `S`. -/
def chkJ (E a i M : ℕ) (S : List (ℕ × ℕ)) : ℕ → List ℕ → Bool
  | _, [] => true
  | j, y :: ys =>
      (!(Nat.ble (a + y) E && Nat.testBit M (E - (a + y))) || S.contains (i, j)) &&
        chkJ E a i M S (j + 1) ys

/-- Outer pair loop over the first weight. -/
def chkI (E M : ℕ) (W : List ℕ) (S : List (ℕ × ℕ)) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, z :: zs => chkJ E z i M S 0 W && chkI E M W S (i + 1) zs

/-- Linear loop: for weights `z` (index `i`) with `z ≤ E` and bit `E - z` set, `i ∈ S`. -/
def chk1 (E M : ℕ) (S : List ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | i, z :: zs => (!(Nat.ble z E && Nat.testBit M (E - z)) || S.contains i) && chk1 E M S (i + 1) zs

theorem chkJ_spec (E a i M : ℕ) (S : List (ℕ × ℕ)) :
    ∀ (j0 : ℕ) (ys : List ℕ), chkJ E a i M S j0 ys = true →
      ∀ q < ys.length, a + ys.getD q 0 ≤ E → Nat.testBit M (E - (a + ys.getD q 0)) = true →
        (i, j0 + q) ∈ S
  | _, [], _, q, hq, _, _ => absurd hq (by simp)
  | j0, y :: ys, h, q, hq, hle, hbit => by
    simp only [chkJ, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    cases q with
    | zero =>
      simp only [List.getD_cons_zero] at hle hbit
      rcases h.1 with h1 | h1
      · have : Nat.ble (a + y) E = true := by rw [Nat.ble_eq]; exact hle
        simp [this, hbit] at h1
      · simpa using h1
    | succ q =>
      have := chkJ_spec E a i M S (j0 + 1) ys h.2 q (by simpa using hq)
        (by simpa using hle) (by simpa using hbit)
      rwa [show j0 + 1 + q = j0 + (q + 1) by omega] at this

theorem chkI_spec (E M : ℕ) (W : List ℕ) (S : List (ℕ × ℕ)) :
    ∀ (i0 : ℕ) (zs : List ℕ), chkI E M W S i0 zs = true →
      ∀ q < zs.length, ∀ q' < W.length, zs.getD q 0 + W.getD q' 0 ≤ E →
        Nat.testBit M (E - (zs.getD q 0 + W.getD q' 0)) = true → (i0 + q, q') ∈ S
  | _, [], _, q, hq, _, _, _, _ => absurd hq (by simp)
  | i0, z :: zs, h, q, hq, q', hq', hle, hbit => by
    simp only [chkI, Bool.and_eq_true] at h
    cases q with
    | zero =>
      simp only [List.getD_cons_zero] at hle hbit
      have := chkJ_spec E z i0 M S 0 W h.1 q' hq' hle hbit
      simpa using this
    | succ q =>
      have := chkI_spec E M W S (i0 + 1) zs h.2 q (by simpa using hq) q' hq'
        (by simpa using hle) (by simpa using hbit)
      rwa [show i0 + 1 + q = i0 + (q + 1) by omega] at this

theorem chk1_spec (E M : ℕ) (S : List ℕ) :
    ∀ (i0 : ℕ) (zs : List ℕ), chk1 E M S i0 zs = true →
      ∀ q < zs.length, zs.getD q 0 ≤ E → Nat.testBit M (E - zs.getD q 0) = true → i0 + q ∈ S
  | _, [], _, q, hq, _, _ => absurd hq (by simp)
  | i0, z :: zs, h, q, hq, hle, hbit => by
    simp only [chk1, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    cases q with
    | zero =>
      simp only [List.getD_cons_zero] at hle hbit
      rcases h.1 with h1 | h1
      · have : Nat.ble z E = true := by rw [Nat.ble_eq]; exact hle
        simp [this, hbit] at h1
      · simpa using h1
    | succ q =>
      have := chk1_spec E M S (i0 + 1) zs h.2 q (by simpa using hq) (by simpa using hle)
        (by simpa using hbit)
      rwa [show i0 + 1 + q = i0 + (q + 1) by omega] at this

/-- The quadratic index set at `E` is exactly `L`, from a `true` pair check. -/
theorem quad_iff {n m : ℕ} (w : Fin n → ℕ) (pos : Fin m → ℕ) (hpos : Function.Injective pos)
    (W : List ℕ) (hW : ∀ i : Fin n, w i = W.getD i 0) (hWl : W.length = n) (M : ℕ)
    (hM : ∀ p, Nat.testBit M (pos p) = true) (E : ℕ) (L : List (Fin n × Fin n × Fin m))
    (hmem : ∀ t ∈ L, w t.1 + w t.2.1 + pos t.2.2 = E)
    (hchk : chkI E M W (L.map fun t => ((t.1 : ℕ), (t.2.1 : ℕ))) 0 W = true) :
    ∀ t, w t.1 + w t.2.1 + pos t.2.2 = E ↔ t ∈ L := by
  rintro ⟨i, j, p⟩
  refine ⟨fun he => ?_, fun ht => hmem _ ht⟩
  have hle : W.getD i 0 + W.getD j 0 ≤ E := by rw [← hW, ← hW]; dsimp at he; omega
  have hbit : Nat.testBit M (E - (W.getD i 0 + W.getD j 0)) = true := by
    rw [← hW, ← hW, show E - (w i + w j) = pos p by dsimp at he; omega]
    exact hM p
  have h := chkI_spec E M W _ 0 W hchk i (by omega) j (by omega) hle hbit
  rw [zero_add, List.mem_map] at h
  obtain ⟨⟨i', j', p'⟩, ht', hij⟩ := h
  simp only [Prod.mk.injEq] at hij
  have hi : i' = i := Fin.ext hij.1
  have hj : j' = j := Fin.ext hij.2
  subst hi hj
  have h' := hmem _ ht'
  dsimp at h' he
  have hp : p' = p := hpos (by omega)
  subst hp
  exact ht'

/-- The linear index set at `E` is exactly `L`, from a `true` check. -/
theorem lin_iff {n m : ℕ} (w : Fin n → ℕ) (pos : Fin m → ℕ) (hpos : Function.Injective pos)
    (W : List ℕ) (hW : ∀ i : Fin n, w i = W.getD i 0) (hWl : W.length = n) (M : ℕ)
    (hM : ∀ p, Nat.testBit M (pos p) = true) (E : ℕ) (L : List (Fin n × Fin m))
    (hmem : ∀ t ∈ L, w t.1 + pos t.2 = E)
    (hchk : chk1 E M (L.map fun t => (t.1 : ℕ)) 0 W = true) :
    ∀ t, w t.1 + pos t.2 = E ↔ t ∈ L := by
  rintro ⟨i, p⟩
  refine ⟨fun he => ?_, fun ht => hmem _ ht⟩
  have hle : W.getD i 0 ≤ E := by rw [← hW]; dsimp at he; omega
  have hbit : Nat.testBit M (E - W.getD i 0) = true := by
    rw [← hW, show E - w i = pos p by dsimp at he; omega]
    exact hM p
  have h := chk1_spec E M _ 0 W hchk i (by omega) hle hbit
  rw [zero_add, List.mem_map] at h
  obtain ⟨⟨i', p'⟩, ht', hi⟩ := h
  have hi : i' = i := Fin.ext hi
  subst hi
  have h' := hmem _ ht'
  dsimp at h' he
  have hp : p' = p := hpos (by omega)
  subst hp
  exact ht'

/-- List form of `coeff_sum_monomial`. -/
theorem coeff_sum_monomial_list {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (e : ι → ℕ) (m : ι → R) (E : ℕ) (L : List ι) (hL : L.Nodup) (hS : ∀ t, e t = E ↔ t ∈ L) :
    (∑ t, monomial (e t) (m t)).coeff E = (L.map m).sum := by
  rw [SparseExtraction.coeff_sum_monomial e m E L.toFinset (fun t => by rw [hS, List.mem_toFinset]),
    List.sum_toFinset _ hL]

end Nine121.SparseCheck
