import DiophantineConsistency.Compact44.SparseRadix
set_option autoImplicit false
namespace GenericWindow

theorem adjacent_window (Y d t m : ℕ) (hd : 0 < d) (hmb : m ∣ d*t) :
    (Y / d) % m = ((Y % (d*t)) / d + (Y / (d*t) % (d*t)) * t) % m := by
  have hdvd : d * m ∣ (d*t) * (d*t) := Nat.mul_dvd_mul (dvd_mul_right d t) hmb
  have hmod : (Y / d) % m = ((Y % ((d*t)*(d*t))) / d) % m := by
    rw [← Nat.mod_mul_right_div_self, ← Nat.mod_mul_right_div_self,
      Nat.mod_mod_of_dvd _ hdvd]
  rw [hmod, Nat.mod_mul]
  have he : Y % (d*t) + (d*t) * (Y/(d*t)%(d*t)) =
      Y % (d*t) + d * ((Y/(d*t)%(d*t))*t) := by ring
  rw [he, Nat.add_mul_div_left _ _ hd]

#print axioms GenericWindow.adjacent_window
end GenericWindow
