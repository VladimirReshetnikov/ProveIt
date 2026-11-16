import Std
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def maskSub (s t : Nat) : Bool := (s &&& t) == s

theorem maskSub_sound {s t i : Nat} (h : maskSub s t = true)
    (hs : s.testBit i = true) : t.testBit i = true := by
  have heq : s &&& t = s := by simpa [maskSub] using h
  have ht := congrArg (fun x : Nat => x.testBit i) heq
  simpa [hs] using ht

def incCheck (s t pos zer stride : Nat) : Bool :=
  maskSub ((s &&& pos) ||| ((s &&& zer) <<< stride)) t

theorem inc_positive {s t pos zer stride m : Nat}
    (hc : incCheck s t pos zer stride = true)
    (hm : s.testBit m = true) (hp : pos.testBit m = true) :
    t.testBit m = true := by
  apply maskSub_sound hc
  simp [hm, hp]

theorem inc_zero {s t pos zer stride m : Nat}
    (hc : incCheck s t pos zer stride = true)
    (hm : s.testBit m = true) (hz : zer.testBit m = true) :
    t.testBit (m + stride) = true := by
  apply maskSub_sound hc
  simp [Nat.testBit_shiftLeft, hm, hz]

#print axioms inc_positive
#print axioms inc_zero

def decCheck (s t u pos zer stride : Nat) : Bool :=
  maskSub (s &&& zer) t && maskSub ((s &&& pos) ||| ((s &&& pos) >>> stride)) u

theorem dec_zero {s t u pos zer stride m : Nat}
    (hc : decCheck s t u pos zer stride = true)
    (hm : s.testBit m = true) (hz : zer.testBit m = true) :
    t.testBit m = true := by
  have h : maskSub (s &&& zer) t = true := by
    simp [decCheck] at hc
    exact hc.1
  apply maskSub_sound h
  simp [hm, hz]

theorem dec_positive_retained {s t u pos zer stride m : Nat}
    (hc : decCheck s t u pos zer stride = true)
    (hm : s.testBit m = true) (hp : pos.testBit m = true) :
    u.testBit m = true := by
  have h : maskSub ((s &&& pos) ||| ((s &&& pos) >>> stride)) u = true := by
    simp [decCheck] at hc
    exact hc.2
  apply maskSub_sound h
  simp [hm, hp]

theorem dec_positive_cleared {s t u pos zer stride m : Nat}
    (hc : decCheck s t u pos zer stride = true)
    (hm : s.testBit m = true) (hp : pos.testBit m = true)
    (hle : stride ≤ m) : u.testBit (m - stride) = true := by
  have h : maskSub ((s &&& pos) ||| ((s &&& pos) >>> stride)) u = true := by
    simp [decCheck] at hc
    exact hc.2
  apply maskSub_sound h
  have heq : stride + (m - stride) = m := by omega
  simp [Nat.testBit_shiftRight, heq, hm, hp]

#print axioms dec_zero
#print axioms dec_positive_retained
#print axioms dec_positive_cleared
