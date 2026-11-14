import PA194AllTape
import M6.Zip
set_option autoImplicit false
set_option maxHeartbeats 0
namespace PA194ZipBridge
open PA194LocalQuotient

/-- An absolute tape seen from a zipper's current head. -/
def tapeAt (l r : List Bool) : Int → Bool
  | .ofNat n => r.getD n false
  | .negSucc n => l.getD n false

theorem getD_trim (l : List Bool) (n : Nat) :
    (M6.Zip.trim l).getD n false = l.getD n false := by
  induction l generalizing n with
  | nil => simp [M6.Zip.trim]
  | cons b l ih =>
    rw [M6.Zip.trim_cons]
    split
    · rename_i h
      cases n with
      | zero => simp [h.1]
      | succ n =>
        have hh : l.getD n false = false := by
          have := ih n
          simpa [h.2] using this.symm
        change false = l.getD n false
        exact hh.symm
    · cases n with
      | zero => simp
      | succ n => simpa using ih n

theorem tapeAt_trim (l r : List Bool) (i : Int) :
    tapeAt (M6.Zip.trim l) (M6.Zip.trim r) i = tapeAt l r i := by
  cases i with
  | ofNat n => exact getD_trim r n
  | negSucc n => exact getD_trim l n

/-- Updating an absolute tape at its head commutes with changing to local coordinates. -/
theorem update_recenter (t : Int → Bool) (p i : Int) (w : Bool) :
    Function.update t p w (p+i) = Function.update (fun j => t (p+j)) 0 w i := by
  simp only [Function.update_apply]
  have heq : p + i = p ↔ i = 0 := by omega
  simp [heq]

/-- Zipper operations and full-tape operations agree after a right move. -/
theorem tapeAt_right (l r : List Bool) (w : Bool) (i : Int) :
    Function.update (tapeAt l r) 0 w (1+i) = tapeAt (w::l) r.tail i := by
  cases i with
  | ofNat n =>
    simp only [Function.update_apply]
    have hn : (1 : Int) + Int.ofNat n ≠ 0 := by
      have hnn := Int.natCast_nonneg n
      simp only [Int.ofNat_eq_natCast] at *
      omega
    simp only [hn, if_false]
    have hn' : (1 : Int) + Int.ofNat n = Int.ofNat (n+1) := by
      simp only [Int.ofNat_eq_natCast]
      omega
    rw [hn']
    cases r <;> simp [tapeAt]
  | negSucc n =>
    cases n with
    | zero => simp [tapeAt]
    | succ n =>
      simp only [Function.update_apply]
      have hn : (1 : Int) + Int.negSucc (n+1) ≠ 0 := by omega
      simp only [hn, if_false]
      have hn' : (1 : Int) + Int.negSucc (n+1) = Int.negSucc n := by omega
      rw [hn']
      simp [tapeAt]

/-- Zipper operations and full-tape operations agree after a left move. -/
theorem tapeAt_left (l r : List Bool) (w : Bool) (i : Int) :
    Function.update (tapeAt l r) 0 w (-1+i) =
      tapeAt l.tail (l.headD false :: w :: r.tail) i := by
  cases i with
  | ofNat n =>
    cases n with
    | zero =>
      change Function.update (tapeAt l r) 0 w (-1) = l.headD false
      rw [Function.update_of_ne (by decide)]
      change l.getD 0 false = l.headD false
      cases l <;> rfl
    | succ n =>
      cases n with
      | zero => simp [tapeAt]
      | succ n =>
        simp only [Function.update_apply]
        have hn : (-1 : Int) + Int.ofNat (n+2) ≠ 0 := by
          have hnn := Int.natCast_nonneg n
          simp only [Int.ofNat_eq_natCast] at *
          omega
        simp only [hn, if_false]
        have hn' : (-1 : Int) + Int.ofNat (n+2) = Int.ofNat (n+1) := by
          simp only [Int.ofNat_eq_natCast]
          omega
        rw [hn']
        cases r <;> simp [tapeAt]
  | negSucc n =>
    simp only [Function.update_apply]
    have hn : (-1 : Int) + Int.negSucc n ≠ 0 := by omega
    simp only [hn, if_false]
    have hn' : (-1 : Int) + Int.negSucc n = Int.negSucc (n+1) := by omega
    rw [hn']
    cases l <;> simp [tapeAt]

/-- A full tape and zipper describe the same state and every cell relative to
their respective heads. -/
def Related (a : Configuration) (z : M6.Zip.Conf) : Prop :=
  a.state = z.q ∧ ∀ i, a.tape (a.pos+i) = tapeAt z.l z.r i

def fullAdvance (a : Configuration) (w direction : Bool) (q : Nat) : Configuration :=
  ⟨q, a.pos + (if direction then 1 else -1), Function.update a.tape a.pos w⟩

def zipAdvance (z : M6.Zip.Conf) (w direction : Bool) (q : Nat) : M6.Zip.Conf :=
  if direction then M6.Zip.zc q (w::z.l) z.r.tail
  else M6.Zip.zl q z.l (w::z.r.tail)

/-- One matching write and movement preserve the complete-tape representation. -/
theorem related_advance (a : Configuration) (z : M6.Zip.Conf)
    (hrel : Related a z) (w direction : Bool) (q : Nat) :
    Related (fullAdvance a w direction q) (zipAdvance z w direction q) := by
  have ht : (fun j => a.tape (a.pos+j)) = tapeAt z.l z.r := funext hrel.2
  constructor
  · cases direction <;> rfl
  · intro i
    cases direction with
    | false =>
      change Function.update a.tape a.pos w ((a.pos + -1)+i) =
        tapeAt (M6.Zip.trim z.l.tail)
          (M6.Zip.trim (z.l.headD false :: w :: z.r.tail)) i
      have heq : (a.pos + -1) + i = a.pos + (-1+i) := by omega
      rw [heq, update_recenter, ht, tapeAt_trim, tapeAt_left]
    | true =>
      change Function.update a.tape a.pos w ((a.pos + 1)+i) =
        tapeAt (M6.Zip.trim (w::z.l)) (M6.Zip.trim z.r.tail) i
      have heq : (a.pos + 1) + i = a.pos + (1+i) := by omega
      rw [heq, update_recenter, ht, tapeAt_trim, tapeAt_right]

#print axioms related_advance
#print axioms tapeAt_left
#print axioms tapeAt_right
#print axioms getD_trim
end PA194ZipBridge
