import Std.Tactic

/-! The list zipper definitions below follow the imported `M6/Zip.lean`.
     Halting is the existence of an execution prefix whose next step is absent. -/
namespace NativeDense
abbrev TM := Nat → Bool → Option (Bool × Bool × Nat)

def trim : List Bool → List Bool
  | [] => []
  | b :: l => if b = false ∧ trim l = [] then [] else b :: trim l

structure Conf where
  q : Nat
  l : List Bool
  r : List Bool
  deriving DecidableEq, Repr

def zc (q : Nat) (l r : List Bool) : Conf := ⟨q, trim l, trim r⟩
def zl (q : Nat) (l r : List Bool) : Conf := zc q l.tail (l.headD false :: r)

def step (M : TM) (c : Conf) : Option Conf :=
  match M c.q (c.r.headD false) with
  | none => none
  | some (w, true, q') => some (zc q' (w :: c.l) c.r.tail)
  | some (w, false, q') => some (zl q' c.l (w :: c.r.tail))

def run (M : TM) : Nat → Conf → Option Conf
  | 0, c => some c
  | k + 1, c => match step M c with
    | none => none
    | some c' => run M k c'

def Halts (M : TM) (c : Conf) : Prop := ∃ n, run M n c = none

/-- The imported zipper's reach-a-stuck-configuration formulation. -/
def ReachAndStop (M : TM) (c : Conf) : Prop :=
  ∃ c', (∃ n, run M n c = some c') ∧ step M c' = none

theorem run_none_has_stop (M : TM) (n : Nat) (c : Conf)
    (h : run M n c = none) : ReachAndStop M c := by
  induction n generalizing c with
  | zero => simp [run] at h
  | succ n ih =>
    cases hs : step M c with
    | none => exact ⟨c, ⟨0, rfl⟩, hs⟩
    | some c' =>
      have hn : run M n c' = none := by simpa [run,hs] using h
      obtain ⟨d,⟨k,hk⟩,hd⟩ := ih c' hn
      exact ⟨d,⟨k+1,by simpa [run,hs] using hk⟩,hd⟩

theorem run_succ_last (M : TM) (n : Nat) (c : Conf) :
    run M (n+1) c = (run M n c).bind (step M) := by
  induction n generalizing c with
  | zero => cases hs : step M c <;> simp [run,hs]
  | succ n ih =>
    cases hs : step M c with
    | none => simp [run,hs]
    | some c' => simpa [run,hs] using ih c'

theorem halts_iff_reach_and_stop (M : TM) (c : Conf) :
    Halts M c ↔ ReachAndStop M c := by
  constructor
  · rintro ⟨n,h⟩
    exact run_none_has_stop M n c h
  · rintro ⟨c',⟨n,h⟩,hs⟩
    refine ⟨n+1,?_⟩
    rw [run_succ_last,h]
    exact hs

def mapConf (label : Nat → Nat) (c : Conf) : Conf := ⟨label c.q, c.l, c.r⟩
def mapAction (label : Nat → Nat) (a : Bool × Bool × Nat) : Bool × Bool × Nat :=
  (a.1, a.2.1, label a.2.2)

/-- Transition conjugacy implies one-step conjugacy, including halt. -/
theorem step_conjugate {M N : TM} {label : Nat → Nat} {bound : Nat}
    (rows : ∀ q < bound, ∀ b, N (label q) b = (M q b).map (mapAction label))
    (c : Conf) (hq : c.q < bound) :
    step N (mapConf label c) = (step M c).map (mapConf label) := by
  rcases c with ⟨q,l,r⟩
  simp only [step,mapConf,rows q hq]
  cases he : M q (r.headD false) with
  | none => rfl
  | some a =>
    rcases a with ⟨w,d,t⟩
    cases d <;> rfl

theorem step_bounded {M : TM} {bound : Nat}
    (nextBound : ∀ q < bound, ∀ b w d t, M q b = some (w,d,t) → t < bound)
    {c c' : Conf} (hq : c.q < bound) (h : step M c = some c') : c'.q < bound := by
  unfold step at h
  cases he : M c.q (c.r.headD false) with
  | none => rw [he] at h; cases h
  | some a =>
    rcases a with ⟨w,d,t⟩
    have ht := nextBound c.q hq _ w d t he
    cases d <;> simp only [he,Option.some.injEq] at h <;> subst c' <;> exact ht

theorem run_conjugate {M N : TM} {label : Nat → Nat} {bound : Nat}
    (rows : ∀ q < bound, ∀ b, N (label q) b = (M q b).map (mapAction label))
    (nextBound : ∀ q < bound, ∀ b w d t, M q b = some (w,d,t) → t < bound)
    (n : Nat) (c : Conf) (hq : c.q < bound) :
    run N n (mapConf label c) = (run M n c).map (mapConf label) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [run, step_conjugate rows c hq]
    cases he : step M c with
    | none => rfl
    | some c' => simpa using ih c' (step_bounded nextBound hq he)

/-- Constructive transport: no excluded middle or consistency hypothesis. -/
theorem halts_conjugate {M N : TM} {label : Nat → Nat} {bound : Nat}
    (rows : ∀ q < bound, ∀ b, N (label q) b = (M q b).map (mapAction label))
    (nextBound : ∀ q < bound, ∀ b w d t, M q b = some (w,d,t) → t < bound)
    (c : Conf) (hq : c.q < bound) :
    Halts N (mapConf label c) ↔ Halts M c := by
  constructor
  · rintro ⟨n,h⟩
    rw [run_conjugate rows nextBound n c hq] at h
    cases he : run M n c with
    | none => exact ⟨n,he⟩
    | some c' => simp [he] at h
  · rintro ⟨n,h⟩
    refine ⟨n,?_⟩
    rw [run_conjugate rows nextBound n c hq,h]
    rfl

end NativeDense
