import PA194HXDispatch
import PA194Bounded
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace PA194HXZipBridge
open PA194Bounded (Conf bits bits_trim bits_head bits_tail)
def rows : List (ℕ × ℕ × ℕ) := PA194HXRows.rows

theorem table_matches_literal : ∀ q : Fin 194, ∀ b : Bool,
    rows.getD (2*q.val + b.toNat) (0,0,194) =
      ((PA194HX.Literal.transition q.val b).1.toNat,
       (PA194HX.Literal.transition q.val b).2.1.toNat,
       (PA194HX.Literal.transition q.val b).2.2) := by decide +kernel
def row (c : Conf) : ℕ × ℕ × ℕ :=
  rows.getD (2*c.1 + c.2.2%2) (0,0,194)
def next (c : Conf) : Conf :=
  if c.1 < 194 then
    let a := row c
    if a.2.1 = 1 then (a.2.2,2*c.2.1+a.1,c.2.2/2)
    else (a.2.2,c.2.1/2,c.2.1%2+2*(a.1+2*(c.2.2/2)))
  else c

def run (n : ℕ) : Conf := Nat.rec (0,0,0) (fun _ c => next c) n
def encodeZip (c : M6.Zip.Conf) : Conf := (c.q, bits c.l, bits c.r)
def zipTotalStep (c : M6.Zip.Conf) : M6.Zip.Conf :=
  (M6.Zip.step PA194HX.Literal.machine c).getD c

set_option linter.unnecessarySeqFocus false in
/-- The numeric transition agrees on every finite-support zipper tape. -/
theorem zip_step_binding (c : M6.Zip.Conf) : next (encodeZip c) = encodeZip (zipTotalStep c) := by
  by_cases hq : c.q < 194
  · have ht := table_matches_literal ⟨c.q, hq⟩ (c.r.headD false)
    have hr : row (encodeZip c) =
        ((PA194HX.Literal.transition c.q (c.r.headD false)).1.toNat,
         (PA194HX.Literal.transition c.q (c.r.headD false)).2.1.toNat,
         (PA194HX.Literal.transition c.q (c.r.headD false)).2.2) := by
      simpa only [row, encodeZip, bits_head] using ht
    change row (c.q, bits c.l, bits c.r) = _ at hr
    simp only [next, encodeZip, hq, ↓reduceIte]
    rw [hr]
    simp only [zipTotalStep, M6.Zip.step, PA194HX.Literal.machine, hq, ↓reduceIte]
    generalize he : PA194HX.Literal.transition c.q (c.r.headD false) = a at *
    rcases a with ⟨w,d,q'⟩
    cases w <;> cases d <;>
      simp [M6.Zip.zc, M6.Zip.zl, bits_trim, bits, bits_head, bits_tail] <;> omega
  · simp [next, encodeZip, hq, zipTotalStep, M6.Zip.step, PA194HX.Literal.machine]


def blankZip : M6.Zip.Conf := ⟨0, [], []⟩
def zipRun (n : ℕ) : M6.Zip.Conf := Nat.rec blankZip (fun _ c => zipTotalStep c) n

theorem zip_run_binding (n : ℕ) : encodeZip (zipRun n) = run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change encodeZip (zipTotalStep (zipRun n)) = next (run n)
    rw [← zip_step_binding, ih]

theorem zip_run_before (n : ℕ) (h : ∀ i < n, (zipRun i).q < 194) :
    M6.Zip.run PA194HX.Literal.machine n blankZip = some (zipRun n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := h n (by omega)
    have old := ih (by intro i hi; exact h i (by omega))
    cases he : M6.Zip.step PA194HX.Literal.machine (zipRun n) with
    | none =>
      have hne : M6.Zip.step PA194HX.Literal.machine (zipRun n) ≠ none := by
        simp only [M6.Zip.step, PA194HX.Literal.machine, hs, ↓reduceIte]
        rcases htr : PA194HX.Literal.transition (zipRun n).q ((zipRun n).r.headD false) with ⟨w,d,q⟩
        cases d <;> simp
      exact False.elim (hne he)
    | some c =>
      have hrun : M6.Zip.run PA194HX.Literal.machine (n+1) blankZip = some c := by
        rw [M6.Zip.run_add, old]
        simp [M6.Zip.run, he]
      change M6.Zip.run PA194HX.Literal.machine (n+1) blankZip = some (zipTotalStep (zipRun n))
      rw [zipTotalStep, he]
      exact hrun

theorem zip_run_some (n : ℕ) (c : M6.Zip.Conf)
    (h : M6.Zip.run PA194HX.Literal.machine n blankZip = some c) : zipRun n = c := by
  induction n generalizing c with
  | zero => simpa [M6.Zip.run, zipRun] using h
  | succ n ih =>
    rw [M6.Zip.run_add] at h
    cases he : M6.Zip.run PA194HX.Literal.machine n blankZip with
    | none => simp [he] at h
    | some prev =>
      simp only [he] at h
      cases hs : M6.Zip.step PA194HX.Literal.machine prev with
      | none => simp [M6.Zip.run, hs] at h
      | some dest =>
        have hd : dest = c := by simpa [M6.Zip.run, hs] using h
        have hp : zipRun n = prev := ih prev he
        change zipTotalStep (zipRun n) = c
        rw [hp, zipTotalStep, hs]
        exact hd


#print axioms table_matches_literal
#print axioms zip_step_binding
#print axioms zip_run_binding
#print axioms zip_run_some
end PA194HXZipBridge
