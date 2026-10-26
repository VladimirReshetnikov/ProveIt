import DiophantineConsistency.PrimePowerOrder

/-! A nonzero first lift digit is sufficient input to the exact-order theorem.
The imported production module is from commit9f35798db4a63c25e435fca14d75931144657d7e. -/
namespace ProofSimplification.LiftSeed

/-- The residue itself supplies the natural-subtraction guard and the exact
first valuation. A separate c<p premise is unnecessary: the residue equality
already enforces it. -/
theorem first_lift_data {p g c : ℕ} (hp : 1 < p) (hc : 0 < c)
    (hseed : g % p ^ 2 = 1 + p * c) :
    1 < g ∧ p ∣ g - 1 ∧ ¬ p ^ 2 ∣ g - 1 := by
  have hpc : 0 < p * c := Nat.mul_pos (by omega) hc
  have hg : 1 < g := by
    have h := Nat.mod_le g (p ^ 2)
    rw [hseed] at h
    omega
  have hmod : g % p = 1 := by
    calc
      g % p = (g % p ^ 2) % p :=
        (Nat.mod_mod_of_dvd _ (dvd_pow_self p (by decide : 2 ≠ 0))).symm
      _ = 1 := by simp [hseed, Nat.add_mod, Nat.mod_eq_of_lt hp]
  have hd : p ∣ g - 1 := by
    apply (Nat.modEq_iff_dvd' hg.le).mp
    change 1 % p = g % p
    rw [hmod, Nat.mod_eq_of_lt hp]
  refine ⟨hg, hd, ?_⟩
  intro hs
  have he := (Nat.modEq_iff_dvd' hg.le).mpr hs
  change 1 % p ^ 2 = g % p ^ 2 at he
  have hsq : 1 < p ^ 2 := one_lt_pow₀ hp (by decide : 2 ≠ 0)
  rw [Nat.mod_eq_of_lt hsq, hseed] at he
  omega

/-- The public interface accepts exactly the certified first lift. -/
theorem order_from_first_lift {p g c : ℕ} (hp : Nat.Prime p) (ho : Odd p)
    (hc : 0 < c) (hseed : g % p ^ 2 = 1 + p * c) (k : ℕ) :
    orderOf (g : ZMod (p ^ (k + 1))) = p ^ k := by
  obtain ⟨_, hd, hs⟩ := first_lift_data hp.one_lt hc hseed
  exact DiophantineConsistency.PrimePowerOrder.order_succ hp ho hd hs k

#print axioms first_lift_data
#print axioms order_from_first_lift

end ProofSimplification.LiftSeed
