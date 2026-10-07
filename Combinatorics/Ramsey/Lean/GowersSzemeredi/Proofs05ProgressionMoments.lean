import GowersSzemeredi.Section05

/-! Second moments for progression sampling over arbitrary cyclic groups.
The subgroup averaging inequality does not assume a prime modulus: repeated
positions and noninvertible differences retain nonnegative covariance.
This is the variance input to the threshold-free route to Corollary 5.8. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

theorem sum_translate_real {G : Type*} [AddCommGroup G] [Fintype G]
    (f : G → Real) (a : G) : (∑ x, f (x + a)) = ∑ x, f x := by
  exact Equiv.sum_comp (Equiv.addRight a) f

theorem subgroup_sum_translation {G : Type*} [AddCommGroup G] [Fintype G]
    (h : G →+ G) (f : G → Real) (x d : G) :
    (∑ e, f (x + h d + h e)) = ∑ e, f (x + h e) := by
  calc
    _ = ∑ e, f (x + h (d + e)) := by
      simp only [map_add, add_assoc]
    _ = ∑ e, f (x + h e) := Equiv.sum_comp (Equiv.addLeft d) (fun e => f (x + h e))

theorem subgroup_average_correlation_lower {G : Type*} [AddCommGroup G] [Fintype G]
    (h : G →+ G) (f : G → Real) :
    (∑ x, f x) ^ 2 ≤ ∑ x, ∑ d, f x * f (x + h d) := by
  classical
  let T : G → Real := fun x => ∑ d, f (x + h d)
  let n : Real := Fintype.card G
  have hn : 0 < n := by
    dsimp [n]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card G)
  have hT (x d : G) : T (x + h d) = T x := subgroup_sum_translation h f x d
  have hsum : (∑ x, T x) = n * ∑ x, f x := by
    dsimp [T]
    rw [Finset.sum_comm]
    simp only [sum_translate_real, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
  have hpair (d : G) : (∑ x, f (x + h d) * T x) = ∑ x, f x * T x := by
    calc
      _ = ∑ x, f (x + h d) * T (x + h d) := by simp only [hT]
      _ = ∑ x, f x * T x := sum_translate_real (fun x => f x * T x) (h d)
  have hsquare : (∑ x, T x ^ 2) = n * ∑ x, f x * T x := by
    calc
      _ = ∑ x, ∑ d, f (x + h d) * T x := by
        simp only [← Finset.sum_mul, T, pow_two]
      _ = ∑ d, ∑ x, f (x + h d) * T x := Finset.sum_comm
      _ = n * ∑ x, f x * T x := by
        simp only [hpair, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, n]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : G => (1 : Real)) T
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, hsum, hsquare] at hcs
  have hresult : (∑ x, f x) ^ 2 ≤ ∑ x, f x * T x := by
    have hn2 : 0 < n ^ 2 := sq_pos_of_pos hn
    apply (mul_le_mul_iff_right₀ hn2).mp
    nlinarith [hcs]
  simpa only [T, Finset.mul_sum] using hresult

theorem cyclic_pair_correlation_lower {N : Nat} [NeZero N]
    (f : ZMod N → Real) (i j : ZMod N) :
    (∑ x, f x) ^ 2 ≤ ∑ d, ∑ a, f (a + i * d) * f (a + j * d) := by
  have h := subgroup_average_correlation_lower (AddMonoidHom.mulLeft (j - i)) f
  calc
    _ ≤ ∑ x, ∑ d, f x * f (x + (j - i) * d) := h
    _ = ∑ d, ∑ x, f x * f (x + (j - i) * d) := Finset.sum_comm
    _ = ∑ d, ∑ a, f (a + i * d) * f (a + j * d) := by
      apply Finset.sum_congr rfl
      intro d _
      have heq (a : ZMod N) : a + i * d + (j - i) * d = a + j * d := by ring
      simpa only [heq] using
        (sum_translate_real (fun x => f x * f (x + (j - i) * d)) (i * d)).symm

/-- Keep the diagonal terms in the second moment. All off-diagonal terms
are nonnegative even when the differences are nonunits modulo `N`. -/
theorem cyclic_progression_second_moment_lower {N : Nat} [NeZero N]
    (f : ZMod N → Real) (L : Nat) :
    (L : Real) * N * (∑ x, f x ^ 2) ≤
      ∑ d, ∑ a, (∑ i : Fin L, f (a + (i.val : ZMod N) * d)) ^ 2 := by
  classical
  let K (i j : Fin L) : Real :=
    ∑ d, ∑ a, f (a + (i.val : ZMod N) * d) * f (a + (j.val : ZMod N) * d)
  have hK (i j : Fin L) : 0 ≤ K i j :=
    (sq_nonneg _).trans (cyclic_pair_correlation_lower f i.val j.val)
  have hdiag (i : Fin L) : K i i = (N : Real) * ∑ x, f x ^ 2 := by
    dsimp [K]
    simp only [← pow_two]
    have ht (d : ZMod N) : (∑ a, f (a + (i.val : ZMod N) * d) ^ 2) =
        ∑ a, f a ^ 2 := sum_translate_real (fun a => f a ^ 2) _
    simp only [ht, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hexpand : (∑ d, ∑ a, (∑ i : Fin L, f (a + (i.val : ZMod N) * d)) ^ 2) =
      ∑ i, ∑ j, K i j := by
    simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
    calc
      _ = ∑ d, ∑ i : Fin L, ∑ a, ∑ j : Fin L,
          f (a + (i.val : ZMod N) * d) * f (a + (j.val : ZMod N) * d) := by
        apply Finset.sum_congr rfl
        intro d _
        rw [Finset.sum_comm]
      _ = ∑ i : Fin L, ∑ d, ∑ a, ∑ j : Fin L,
          f (a + (i.val : ZMod N) * d) * f (a + (j.val : ZMod N) * d) :=
        Finset.sum_comm
      _ = ∑ i, ∑ j, K i j := by
        apply Finset.sum_congr rfl
        intro i _
        calc
          _ = ∑ d, ∑ j : Fin L, ∑ a,
              f (a + (i.val : ZMod N) * d) * f (a + (j.val : ZMod N) * d) := by
            apply Finset.sum_congr rfl
            intro d _
            rw [Finset.sum_comm]
          _ = ∑ j, K i j := Finset.sum_comm
  rw [hexpand]
  calc
    _ = ∑ i : Fin L, K i i := by
      simp only [hdiag, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    _ ≤ ∑ i, ∑ j, K i j := by
      apply Finset.sum_le_sum
      intro i _
      exact Finset.single_le_sum (fun j _ => hK i j) (Finset.mem_univ i)

end LeanProofs.GowersSzemeredi
