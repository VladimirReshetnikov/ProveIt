import ByteWindow
set_option autoImplicit false
namespace ByteWindowChecks

theorem crossing_byte : (Nat.ofDigits (2^67) [2^66, 1] / 2^(8*8)) % 256 = 12 := by
  have hb : ∀ x ∈ ([2^66, 1] : List ℕ), x < 2^67 := by norm_num
  have h := ByteWindow.byte [2^66, 1] hb 8
  norm_num [PaddedRadixDigits.digit] at h ⊢
  all_goals exact h

theorem zero_padding_byte : (Nat.ofDigits (2^67) [1] / 2^(8*9)) % 256 = 0 := by
  have hb : ∀ x ∈ ([1] : List ℕ), x < 2^67 := by norm_num
  have h := ByteWindow.byte [1] hb 9
  norm_num [PaddedRadixDigits.digit] at h ⊢

#print axioms ByteWindowChecks.crossing_byte
#print axioms ByteWindowChecks.zero_padding_byte
end ByteWindowChecks
