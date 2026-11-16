import DiophantineConsistency.IPRAPellSlack
import DiophantineConsistency.NativePellPower

/-! Check the positive witness interface at the maintained native Pell
consumer's natural-number premises. -/

set_option autoImplicit false

open DiophantineConsistency IPRAPellSlack

example {X Y r k c a R η ζ : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 1 ≤ r) (hR : R = 2 * r + 1)
    (ha : a = Y * (X + 1)) (hc : c = Pell.yn (by omega : 1 < a + 2) R)
    (hk : k = 2 * Pell.yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1))
    (hck : c = k * Y + η) (slack : natRow η k ζ) : X ^ r < 2 * (Y + 1) :=
  NativePellPower.power_lt_twice_Y hX hY hr hR ha hc hk hck slack.2 slack.1
