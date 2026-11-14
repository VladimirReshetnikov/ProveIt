import PA194MPGuardSteps
/-! Arithmetic proof adapted from M6.Source.MPGuard; every literal
source binding is reproved against the PA194 program. -/
set_option linter.unusedSimpArgs false
namespace PA194MPSource.MPGuard
open M6.Source

theorem drain_t (t h x : Nat) (f : Registers) :
    Steps PA194SourceProgram.sites (3*t+1) (config 3621 t h x f)
      (config 3624 0 h (x+t) f) := by
  induction t generalizing x with
  | zero =>
    apply Steps.cons
    rw [step3621]
    simp only [↓reduceIte,Nat.add_zero]
    exact Steps.refl _
  | succ t ih =>
    have hn : 3*(t+1)+1 = (3*t+1)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step3621]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step3622]
    apply Steps.cons
    rw [step3623]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (x+1)

theorem drain_h (t h x : Nat) (f : Registers) :
    Steps PA194SourceProgram.sites (2*h+1) (config 3629 t h x f) (config 3631 t 0 x f) := by
  induction h with
  | zero =>
    apply Steps.cons
    rw [step3629]
    simp only [↓reduceIte]
    exact Steps.refl _
  | succ h ih =>
    have hn : 2*(h+1)+1 = (2*h+1)+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step3629]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step3630]
    exact ih

theorem drain_x (t x : Nat) (f : Registers) :
    Steps PA194SourceProgram.sites (3*x+2) (config 3631 t 0 x f) (config 3660 t 0 0 f) := by
  induction x with
  | zero =>
    apply Steps.cons
    rw [step3631]
    simp only [↓reduceIte]
    apply Steps.cons
    rw [step3633]
    exact Steps.refl _
  | succ x ih =>
    have hn : 3*(x+1)+2 = (3*x+2)+1+1+1 := by omega
    rw [hn]
    apply Steps.cons
    rw [step3631]
    simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
    apply Steps.cons
    rw [step3632]
    apply Steps.cons
    rw [step3629]
    simp only [↓reduceIte]
    exact ih

theorem cleanup (t h x : Nat) (f : Registers) :
    Steps PA194SourceProgram.sites (2*h+3*x+3) (config 3629 t h x f) (config 3660 t 0 0 f) := by
  have hn : 2*h+3*x+3 = (2*h+1)+(3*x+2) := by omega
  rw [hn]
  exact (drain_h t h x f).append (drain_x t x f)

theorem compare (t h x : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps PA194SourceProgram.sites n (config 3624 t h x f)
      (config (if h = x then 3634 else 3660) t 0 0 f) := by
  induction h generalizing x with
  | zero =>
    cases x with
    | zero =>
      refine ⟨2,by omega,?_⟩
      apply Steps.cons
      rw [step3624]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step3628]
      simp only [↓reduceIte]
      exact Steps.refl _
    | succ x =>
      refine ⟨(3*x+3)+1+1,by omega,?_⟩
      apply Steps.cons
      rw [step3624]
      simp only [↓reduceIte,Nat.zero_ne_add_one]
      apply Steps.cons
      rw [step3628]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      simpa only [Nat.mul_zero,Nat.zero_add] using cleanup t 0 x f
  | succ h ih =>
    cases x with
    | zero =>
      refine ⟨(2*h+3)+1+1+1,by omega,?_⟩
      apply Steps.cons
      rw [step3624]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step3625]
      simp only [↓reduceIte]
      apply Steps.cons
      rw [step3627]
      simpa only [Nat.mul_zero,Nat.add_zero] using cleanup t h 0 f
    | succ x =>
      obtain ⟨n,hn,hs⟩ := ih x
      refine ⟨n+1+1+1,by omega,?_⟩
      apply Steps.cons
      rw [step3624]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel,Nat.add_right_cancel_iff]
      apply Steps.cons
      rw [step3625]
      simp only [Nat.add_eq_zero_iff,Nat.succ_ne_zero,↓reduceIte,Nat.add_sub_cancel]
      apply Steps.cons
      rw [step3626]
      exact hs

/-- The actual MP equality guard clears T,H,X on both paths, retaining the
entire unrelated frame; equality alone reaches the success push at3634. -/
theorem guard (t h : Nat) (f : Registers) :
    ∃ n, 0 < n ∧ Steps PA194SourceProgram.sites n (config 3621 t h 0 f)
      (config (if t = h then 3634 else 3660) 0 0 0 f) := by
  obtain ⟨n,hn,hs⟩ := compare 0 h t f
  have a := drain_t t h 0 f
  simp only [Nat.zero_add] at a
  refine ⟨3*t+1+n,by omega,?_⟩
  simpa only [eq_comm] using a.append hs

#print axioms guard
end PA194MPSource.MPGuard

