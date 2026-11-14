import Table

/-! A safe numerical execution linked to the exact imported zipper machines. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace CloseStartup
open M6.Zip
abbrev Conf := Nat × Nat × Nat

theorem table_matches_literal : ∀ q : Fin 196, ∀ b : Bool,
    rows.getD (2*q.val + b.toNat) (0,0,196) =
      ((PA196.Literal.transition q.val b).1.toNat,
       (PA196.Literal.transition q.val b).2.1.toNat,
       (PA196.Literal.transition q.val b).2.2) := by decide +kernel

def row (c : Conf) : Nat × Nat × Nat := rows.getD (2*c.1 + c.2.2%2) (0,0,196)
def next (c : Conf) : Conf :=
  if c.1 < 196 then
    let a := row c
    if a.2.1 = 1 then (a.2.2,2*c.2.1+a.1,c.2.2/2)
    else (a.2.2,c.2.1/2,c.2.1%2+2*(a.1+2*(c.2.2/2)))
  else c

def bits : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bits bs

theorem bits_trim (bs : List Bool) : bits (M6.Zip.trim bs) = bits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [M6.Zip.trim]
      split
      next h =>
        have hz : bits bs = 0 := by rw [← ih, h.2]; rfl
        simp [h.1, bits, hz]
      next h => simp [bits, ih]

theorem bits_head (bs : List Bool) : bits bs % 2 = (bs.headD false).toNat := by
  cases bs with
  | nil => rfl
  | cons b bs => cases b <;> simp [bits]

theorem bits_tail (bs : List Bool) : bits bs / 2 = bits bs.tail := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    cases b with
    | false => simp [bits]
    | true => simp only [bits, List.tail_cons, Bool.toNat_true]; omega

def encodeZip (c : M6.Zip.Conf) : Conf := (c.q, bits c.l, bits c.r)
def zipTotalStep (c : M6.Zip.Conf) : M6.Zip.Conf :=
  (M6.Zip.step PA196.Literal.machine c).getD c

/-- Numeric stepping agrees with the imported PA196 zipper step. -/
theorem zip_step_binding (c : M6.Zip.Conf) : next (encodeZip c) = encodeZip (zipTotalStep c) := by
  by_cases hq : c.q < 196
  · have ht := table_matches_literal ⟨c.q, hq⟩ (c.r.headD false)
    have hr : row (encodeZip c) =
        ((PA196.Literal.transition c.q (c.r.headD false)).1.toNat,
         (PA196.Literal.transition c.q (c.r.headD false)).2.1.toNat,
         (PA196.Literal.transition c.q (c.r.headD false)).2.2) := by
      simpa only [row, encodeZip, bits_head] using ht
    change row (c.q, bits c.l, bits c.r) = _ at hr
    simp only [next, encodeZip, hq, ↓reduceIte]
    rw [hr]
    simp only [zipTotalStep, M6.Zip.step, PA196.Literal.machine, hq, ↓reduceIte]
    generalize he : PA196.Literal.transition c.q (c.r.headD false) = a at *
    rcases a with ⟨w,d,q'⟩
    cases w <;> cases d <;>
      simp [M6.Zip.zc, M6.Zip.zl, bits_trim, bits, bits_head, bits_tail] <;> omega
  · simp [next, encodeZip, hq, zipTotalStep, M6.Zip.step, PA196.Literal.machine]

/-- Dense target for CD3, CD4, CD5, CD6, respectively. -/
def target (v : Fin 4) : Nat := match v.val with
  | 0 => 17 | 1 => 113 | 2 => 44 | _ => 21

def variant (v : Fin 4) : TMN := fun q b =>
  if q = 193 ∧ b = true then some (true,true,target v)
  else PA196.Literal.machine q b

def blank : M6.Zip.Conf := ⟨0, [], []⟩

def safe (c : Conf) : Bool := decide (c.1 < 196) && !(c.1 == 193 && c.2.2 % 2 == 1)
def safeRun : Nat → Conf → Option Conf
  | 0,c => some c
  | n+1,c => if safe c then safeRun n (next c) else none

theorem safe_run_add (n m : Nat) (c : Conf) :
    safeRun (n+m) c = (safeRun n c).bind (safeRun m) := by
  induction n generalizing c with
  | zero => simp [safeRun]
  | succ n ih =>
    simp only [Nat.succ_add,safeRun]
    split <;> simp_all

theorem safe_compose {n m : Nat} {a b c : Conf}
    (h : safeRun n a = some b) (k : safeRun m b = some c) :
    safeRun (n+m) a = some c := by
  rw [safe_run_add, h]
  exact k

theorem safe_step (c : M6.Zip.Conf) (h : safe (encodeZip c) = true) :
    ∃ c', step PA196.Literal.machine c = some c' ∧
      (∀ v : Fin 4, step (variant v) c = some c') ∧ next (encodeZip c) = encodeZip c' := by
  have hq : c.q < 196 := by simpa [safe, encodeZip] using (Bool.and_eq_true_iff.mp h).1
  have hbad : ¬ (c.q = 193 ∧ c.r.headD false = true) := by
    intro hb
    rcases hb with ⟨hq', hr⟩
    cases hlist : c.r with
    | nil => simp [hlist] at hr
    | cons bit tail =>
      cases bit <;> simp [safe, encodeZip, bits_head, hq', hlist] at h hr
  have hne : step PA196.Literal.machine c ≠ none := by
    simp only [M6.Zip.step, PA196.Literal.machine, hq, ↓reduceIte]
    rcases htr : PA196.Literal.transition c.q (c.r.headD false) with ⟨w,d,q⟩
    cases d <;> simp
  cases he : step PA196.Literal.machine c with
  | none => contradiction
  | some c' =>
    refine ⟨c', rfl, ?_, ?_⟩
    · intro v
      have hm : variant v c.q (c.r.headD false) = PA196.Literal.machine c.q (c.r.headD false) := by
        simp only [variant]
        split
        · rename_i hb
          exact False.elim (hbad hb)
        · rfl
      simpa only [M6.Zip.step, hm] using he
    · simpa [zipTotalStep, he] using zip_step_binding c

theorem safe_transfer (n : Nat) (c : M6.Zip.Conf) (d : Conf)
    (h : safeRun n (encodeZip c) = some d) :
    ∃ c', run PA196.Literal.machine n c = some c' ∧
      (∀ v : Fin 4, run (variant v) n c = some c') ∧ encodeZip c' = d := by
  induction n generalizing c with
  | zero =>
    simp only [safeRun, Option.some.injEq] at h
    subst d
    exact ⟨c, rfl, fun _ => rfl, rfl⟩
  | succ n ih =>
    simp only [safeRun] at h
    split at h
    · rename_i hs
      have hgood : safe (encodeZip c) = true := by simpa using hs
      obtain ⟨c', hlit, hvariants, henc⟩ := safe_step c hgood
      rw [henc] at h
      obtain ⟨final, hrun, hvrun, hfinal⟩ := ih c' h
      refine ⟨final, ?_, ?_, hfinal⟩
      · simpa [M6.Zip.run, hlit] using hrun
      · intro v
        simpa [M6.Zip.run, hvariants v] using hvrun v
    · contradiction

#print axioms table_matches_literal
#print axioms safe_transfer
end CloseStartup
