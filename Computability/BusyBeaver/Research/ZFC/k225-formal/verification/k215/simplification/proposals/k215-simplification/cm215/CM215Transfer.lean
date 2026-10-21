import CM215Data
import PositiveStuttering

/-! CM215 inherits K215 equihalting through a three-clause local invariant.
This proof is independent of the register program and numerical calculus. -/
namespace CM215
open PositiveStuttering
set_option maxRecDepth 10000
set_option maxHeartbeats 0

structure Cfg where
  q : State
  h : Int
  tape : Int → Bool

def put (t : Int → Bool) (h : Int) (w : Bool) : Int → Bool :=
  fun x => if x = h then w else t x

def act (c : Cfg) (r : Row) : Cfg := ⟨r.next, c.h + r.d, put c.tape c.h r.w⟩
def step (T : State → Bool → Row) (c : Cfg) : Cfg := act c (T c.q (c.tape c.h))
def φ (q : State) : State := if q = s176 then s52 else q
def lift (c : Cfg) : Cfg := { c with q := φ c.q }
def Halt (c : Cfg) : Prop := c.q = s254

def Inv (c : Cfg) : Prop :=
  (c.q = s52 → c.tape (c.h-1) = true) ∧
  (c.q = s176 → c.tape c.h = false → c.tape (c.h-1) = false) ∧
  (c.q = s156 → c.tape (c.h+1) = true)

-- Finite hypotheses. `decide` constructs kernel-checked proofs on all 432
-- totalized state/symbol inputs, not just those seen on the blank run.
private theorem incoming52 : ∀ q b, (K q b).next = s52 →
    (K q b).d = 1 ∧ (K q b).w = true := by decide +kernel
private theorem incoming156 : ∀ q b, (K q b).next = s156 →
    (K q b).d = -1 ∧ (K q b).w = true := by decide +kernel
private theorem incoming176 : ∀ q b, (K q b).next = s176 →
    ((K q b).d = 1 ∧ (K q b).w = false) ∨
    (q = s156 ∧ b = true ∧ (K q b).d = 1 ∧ (K q b).w = true) := by decide +kernel
private theorem ordinary : ∀ q b, q ≠ s52 → q ≠ s176 →
    M (φ q) b = { K q b with next := φ (K q b).next } := by decide +kernel
private theorem phi_terminal : ∀ q, φ q = s254 ↔ q = s254 := by decide +kernel

private theorem right_prev (c : Cfg) (r : Row) (hd : r.d = 1) :
    (act c r).tape ((act c r).h-1) = r.w := by
  simp [act, put, hd]
private theorem left_next (c : Cfg) (r : Row) (hd : r.d = -1) :
    (act c r).tape ((act c r).h+1) = r.w := by
  have he : c.h + (-1) + 1 = c.h := by omega
  simp [act, put, hd, he]
private theorem right_cur (c : Cfg) (r : Row) (hd : r.d = 1) :
    (act c r).tape (act c r).h = c.tape (c.h+1) := by
  have he : c.h + 1 ≠ c.h := by omega
  simp [act, put, hd, he]

/-- The third clause remembers the exceptional 189/1 → 156/1 route. -/
theorem invariant_step (c : Cfg) (hc : Inv c) : Inv (step K c) := by
  let r := K c.q (c.tape c.h)
  change (r.next = s52 → (act c r).tape ((act c r).h-1) = true) ∧
    (r.next = s176 → (act c r).tape (act c r).h = false →
      (act c r).tape ((act c r).h-1) = false) ∧
    (r.next = s156 → (act c r).tape ((act c r).h+1) = true)
  constructor
  · intro h
    obtain ⟨hd, hw⟩ := incoming52 c.q (c.tape c.h) h
    exact (right_prev c r hd).trans hw
  constructor
  · intro h hz
    rcases incoming176 c.q (c.tape c.h) h with ⟨hd, hw⟩ | ⟨hq, _, hd, _⟩
    · exact (right_prev c r hd).trans hw
    · have hn := hc.2.2 hq
      rw [right_cur c r hd, hn] at hz
      contradiction
  · intro h
    obtain ⟨hd, hw⟩ := incoming156 c.q (c.tape c.h) h
    exact (left_next c r hd).trans hw

private theorem put_same (t : Int → Bool) (h : Int) : put t h (t h) = t := by
  funext x
  by_cases hx : x = h
  · subst x; simp [put]
  · simp [put, hx]

@[simp] private theorem phi52 : φ s52 = s52 := rfl
@[simp] private theorem phi176 : φ s176 = s52 := rfl
@[simp] private theorem phi150 : φ s150 = s150 := rfl
@[simp] private theorem phi154 : φ s154 = s154 := rfl
@[simp] private theorem phi168 : φ s168 = s168 := rfl
@[simp] private theorem k52f : K s52 false = ⟨false, 1, s154⟩ := rfl
@[simp] private theorem k52t : K s52 true = ⟨true, 1, s150⟩ := rfl
@[simp] private theorem k176f : K s176 false = ⟨false, 1, s168⟩ := rfl
@[simp] private theorem k176t : K s176 true = ⟨true, 1, s150⟩ := rfl
@[simp] private theorem m52f : M s52 false = ⟨false, -1, s176⟩ := rfl
@[simp] private theorem m52t : M s52 true = ⟨true, 1, s150⟩ := rfl
@[simp] private theorem m176f : M s176 false = ⟨false, 1, s185⟩ := rfl
@[simp] private theorem m176t : M s176 true = ⟨true, 1, s129⟩ := rfl
@[simp] private theorem m185f : M s185 false = ⟨false, 1, s168⟩ := rfl
@[simp] private theorem m129f : M s129 false = ⟨false, 1, s154⟩ := rfl
@[simp] private theorem mH (b : Bool) : M s254 b = ⟨b, 0, s254⟩ := rfl

private theorem one_branch (c : Cfg) (hq : c.q = s52 ∨ c.q = s176)
    (hb : c.tape c.h = true) : step M (lift c) = lift (step K c) := by
  rcases hq with hq | hq
  all_goals simp only [step, lift, hq, phi52, phi176, hb, m52t, k52t, k176t, act, phi150]

private theorem ordinary_step (c : Cfg) (ha : c.q ≠ s52) (hb : c.q ≠ s176) :
    step M (lift c) = lift (step K c) := by
  simp only [step, lift]
  rw [ordinary c.q (c.tape c.h) ha hb]
  rfl

private theorem zero52 (c : Cfg) (hq : c.q = s52) (hz : c.tape c.h = false)
    (hm : c.tape (c.h-1) = true) :
    run (step M) 3 (lift c) = lift (step K c) := by
  have hw0 : put c.tape c.h false = c.tape := hz ▸ put_same c.tape c.h
  have hw1 : put c.tape (c.h-1) true = c.tape := hm ▸ put_same c.tape (c.h-1)
  have e1 : c.h + (-1) = c.h-1 := by omega
  have e2 : c.h-1+1 = c.h := by omega
  simp only [run, step, lift, hq, phi52, hz, hm, k52f, m52f, m176t,
    m129f, act, hw0, hw1, e1, e2, phi154]

private theorem zero176 (c : Cfg) (hq : c.q = s176) (hz : c.tape c.h = false)
    (hm : c.tape (c.h-1) = false) :
    run (step M) 3 (lift c) = lift (step K c) := by
  have hw0 : put c.tape c.h false = c.tape := hz ▸ put_same c.tape c.h
  have hw1 : put c.tape (c.h-1) false = c.tape := hm ▸ put_same c.tape (c.h-1)
  have e1 : c.h + (-1) = c.h-1 := by omega
  have e2 : c.h-1+1 = c.h := by omega
  simp only [run, step, lift, hq, phi176, hz, hm, k176f, m52f, m176f,
    m185f, act, hw0, hw1, e1, e2, phi168]

/-- Every old step has an exact positive-length macro, preserving the whole tape. -/
theorem simulate (c : Cfg) (hi : Inv c) :
    ∃ k, 1 ≤ k ∧ run (step M) k (lift c) = lift (step K c) := by
  by_cases ha : c.q = s52
  · cases hb : c.tape c.h with
    | false => exact ⟨3, by decide, zero52 c ha hb (hi.1 ha)⟩
    | true => exact ⟨1, by decide, one_branch c (Or.inl ha) hb⟩
  · by_cases hb : c.q = s176
    · cases hz : c.tape c.h with
      | false => exact ⟨3, by decide, zero176 c hb hz (hi.2.1 hb hz)⟩
      | true => exact ⟨1, by decide, one_branch c (Or.inr hb) hz⟩
    · exact ⟨1, by decide, ordinary_step c ha hb⟩

private theorem terminal_persistent (c : Cfg) (hc : Halt c) : Halt (step M c) := by
  change c.q = s254 at hc
  simp only [Halt, step, hc, mH, act]

/-- Arbitrary tape and arbitrary head; designated initial state 0. -/
theorem halts_iff (tape : Int → Bool) (head : Int) :
    (∃ n, Halt (run (step K) n ⟨s0, head, tape⟩)) ↔
    (∃ n, Halt (run (step M) n ⟨s0, head, tape⟩)) := by
  have hi : Inv ⟨s0, head, tape⟩ := by simp [Inv, s0, s52, s176, s156]
  exact equihalting (step K) (step M) lift Inv Halt Halt ⟨s0, head, tape⟩
    hi invariant_step terminal_persistent (fun c => phi_terminal c.q) simulate

#print axioms halts_iff
end CM215
