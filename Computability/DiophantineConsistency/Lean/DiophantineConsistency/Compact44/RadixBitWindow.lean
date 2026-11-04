import DiophantineConsistency.Compact44.GenericWindow
set_option autoImplicit false
namespace RadixBitWindow

theorem window (Y s : ℕ) (hs : s < 67) :
    (Y / 2^s) % 256 =
      ((Y % (2^67)) / 2^s + (Y / (2^67) % (2^67)) * 2^(67-s)) % 256 := by
  have hb : 2^s * 2^(67-s) = 2^67 := by
    rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hs)]
  have hm : 256 ∣ 2^67 := by norm_num
  have hd : 0 < 2^s := by positivity
  have h := GenericWindow.adjacent_window Y (2^s) (2^(67-s)) 256 hd (by rw [hb]; exact hm)
  simpa only [hb] using h

#print axioms RadixBitWindow.window
end RadixBitWindow
