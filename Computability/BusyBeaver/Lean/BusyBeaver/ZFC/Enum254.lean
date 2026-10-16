import BusyBeaver.ZFC.Code254

/-!
The abstract proof enumerator of the base-4 ZFC machines, and L1.

One run of the machine's main loop is `enum_step` on six registers:
the proof list `pl`, the next candidate `np`, the current formula `tw`, the
theorem stack `ws` (a stream `P top rest`, with 0 the all-zero stream), the
additive parameter `d`, and the cached formula `h`. Commands are read from
the proof list with the pairing inverse `Cantor.ofNat`:

```text
0      MP   x       d += x; if Imp(tw, d) = h then tw := d, push 0 else tw := 0; h := 0
1      DROP x       d += x; push tw; tw := h
2      NIP  x       d += x; if h = 1 then HALT else h := pop
3 + c  AX   x y u   d += x; a := d; b := h + y; push tw, All(a,h), rho8 … rho1;
                    tw := (c = a or c = b ? 0 : bundle a b c); d := 0; h := 0
```

The first command of a candidate is read from the candidate number itself;
later commands from `pl - 1`. This is the frozen interface of the published
verification (upstream `ZF/m254/coq/logic/Enum254.v`), stated independently.

Main theorem `enum_halts_iff`: the enumerator halts from the zero state iff
the falsity code 1 is derivable in `C254`. Soundness is a stack invariant;
completeness compiles a derivation into command blocks and shows that every
candidate is eventually reached unless the run has already halted. This is
the abstract functional interface; its simulation by Prog254/RegisterPath
and the binary table are not proved in this module.
-/

namespace SetTheory.BusyBeaver.ZFC.Enum254

open SetTheory.BusyBeaver.ZFC.Code254

/- Closed codes such as `rho2 1 0 1` are astronomically large nested pairings;
   the pairing must never be evaluated, only manipulated through its lemmas. -/
attribute [local irreducible] P

abbrev unP (z : Nat) : Nat × Nat := Cantor.ofNat z

theorem unP_P' (x y : Nat) : unP (P x y) = (x, y) := unP_P x y

structure St where
  pl : Nat
  np : Nat
  tw : Nat
  ws : Nat
  d : Nat
  h : Nat

def s0 : St := ⟨0, 0, 0, 0, 0, 0⟩

/-- The stack after AX: `tw` first, then GEN of the cache, then rho8 … rho1. -/
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a b) (P (rho7 a b c) (P (rho8 a b c u) (P (wal a h) (P t w)))))))))

def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle a b c

/-- The register-level effect of one command, without the proof-list pointer. -/
inductive Cmd where
  | mp (x : Nat)
  | drop (x : Nat)
  | nip (x : Nat)
  | ax (c x y u : Nat)

/-- Working registers `(tw, ws, d, h)`. -/
structure W where
  tw : Nat
  ws : Nat
  d : Nat
  h : Nat

/-- One command on the working registers; `none` is the halting NIP. -/
def cstep : Cmd → W → Option W
  | .mp x, ⟨t, s, d, h⟩ =>
      if wim t (d + x) = h then some ⟨d + x, P 0 s, d + x, 0⟩ else some ⟨0, s, d + x, 0⟩
  | .drop x, ⟨t, s, d, h⟩ => some ⟨h, P t s, d + x, h⟩
  | .nip x, ⟨t, s, d, h⟩ =>
      if h = 1 then none else some ⟨t, (unP s).2, d + x, (unP s).1⟩
  | .ax c x y u, ⟨t, s, d, h⟩ =>
      some ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c u t s, 0, 0⟩

/-- Packing of a command in front of the rest pointer `r`. -/
def pack : Cmd → Nat → Nat
  | .mp x, r => P 0 (P x r)
  | .drop x, r => P 1 (P x r)
  | .nip x, r => P 2 (P x r)
  | .ax c x y u, r => P (c + 3) (P x (P y (P u r)))

/-- Encoding of a nonempty command list as a candidate number. -/
def encL : Cmd → List Cmd → Nat
  | c, [] => pack c 0
  | c, c' :: cs => pack c (encL c' cs + 1)

/-- The proof-list fetch: a new candidate when the list is exhausted. -/
def fetch (s : St) : Nat × Nat := if s.pl = 0 then (s.np, s.np + 1) else (s.pl - 1, s.np)

/-- Execute the command packed at `pl1`, with the next candidate `np1`. -/
def execAt (pl1 np1 : Nat) (s : St) : Option St :=
  match (unP pl1).1 with
  | 0 => some (if wim s.tw (s.d + (unP (unP pl1).2).1) = s.h
               then ⟨(unP (unP pl1).2).2, np1, s.d + (unP (unP pl1).2).1, P 0 s.ws,
                     s.d + (unP (unP pl1).2).1, 0⟩
               else ⟨(unP (unP pl1).2).2, np1, 0, s.ws, s.d + (unP (unP pl1).2).1, 0⟩)
  | 1 => some ⟨(unP (unP pl1).2).2, np1, s.h, P s.tw s.ws, s.d + (unP (unP pl1).2).1, s.h⟩
  | 2 => if s.h = 1 then none
         else some ⟨(unP (unP pl1).2).2, np1, s.tw, (unP s.ws).2, s.d + (unP (unP pl1).2).1,
                    (unP s.ws).1⟩
  | c + 3 =>
      some ⟨(unP (unP (unP (unP pl1).2).2).2).2, np1,
            gate (s.d + (unP (unP pl1).2).1) (s.h + (unP (unP (unP pl1).2).2).1) c,
            axStack (s.d + (unP (unP pl1).2).1) s.h (s.h + (unP (unP (unP pl1).2).2).1) c
              (unP (unP (unP (unP pl1).2).2).2).1 s.tw s.ws, 0, 0⟩

/-- One step of the enumerator. -/
def enumStep (s : St) : Option St := execAt (fetch s).1 (fetch s).2 s

def run : Nat → St → Option St
  | 0, s => some s
  | n + 1, s => match enumStep s with
    | some s' => run n s'
    | none => none

/-- The enumerator halts: some reachable state takes a halting step. -/
def Halts : Prop := ∃ n s, run n s0 = some s ∧ enumStep s = none

/-! ## Soundness -/

/-- The stream after dropping `k` entries. -/
def tailN : Nat → Nat → Nat
  | 0, z => z
  | k + 1, z => tailN k (unP z).2

/-- Every entry of a stream is derivable. -/
def Good (z : Nat) : Prop := ∀ k, C254 (unP (tailN k z)).1

theorem tailN_zero : ∀ k, tailN k 0 = 0
  | 0 => rfl
  | k + 1 => by
      have h0 : (unP 0).2 = 0 := rfl
      simp only [tailN, h0, tailN_zero k]

theorem good_zero : Good 0 := by
  intro k
  rw [tailN_zero k]; exact C254.truth

theorem good_cons {x z : Nat} (hx : C254 x) (hz : Good z) : Good (P x z) := by
  intro k
  cases k with
  | zero => simpa [tailN, unP_P'] using hx
  | succ k => simpa [tailN, unP_P'] using hz k

theorem good_head {z : Nat} (hz : Good z) : C254 (unP z).1 := hz 0

theorem good_tail {z : Nat} (hz : Good z) : Good (unP z).2 := fun k => hz (k + 1)

def Inv (s : St) : Prop := C254 s.tw ∧ C254 s.h ∧ Good s.ws

theorem gate_good (a b c : Nat) : C254 (gate a b c) := by
  unfold gate
  split
  · exact C254.truth
  · rename_i h
    exact C254.bundle a b c (fun e => h (Or.inl e)) (fun e => h (Or.inr e))

theorem axStack_good (a h b c u t w : Nat) (hh : C254 h) (ht : C254 t) (hw : Good w) :
    Good (axStack a h b c u t w) := by
  unfold axStack
  exact good_cons (C254.r1 a b) <| good_cons (C254.r2 a b c) <| good_cons (C254.r3 a b c) <|
    good_cons (C254.r4 a b c) <| good_cons (C254.r5 a b c) <| good_cons (C254.r6 a b) <|
    good_cons (C254.r7 a b c) <| good_cons (C254.r8 a b c u) <| good_cons (C254.gen a hh) <|
    good_cons ht hw

theorem step_inv {s s' : St} (hs : Inv s) (h : enumStep s = some s') : Inv s' := by
  obtain ⟨ht, hh, hw⟩ := hs
  unfold enumStep execAt at h
  generalize (fetch s).1 = pl1 at h
  generalize (fetch s).2 = np1 at h
  split at h
  · split at h
    · rename_i heq
      cases h
      refine ⟨?_, C254.truth, good_cons C254.truth hw⟩
      exact C254.mp ht (heq ▸ hh)
    · cases h
      exact ⟨C254.truth, C254.truth, hw⟩
  · cases h
    exact ⟨hh, hh, good_cons ht hw⟩
  · split at h
    · cases h
    · cases h
      exact ⟨ht, good_head hw, good_tail hw⟩
  · cases h
    exact ⟨gate_good _ _ _, C254.truth, axStack_good _ _ _ _ _ _ _ hh ht hw⟩

theorem halt_step {s : St} (hs : Inv s) (h : enumStep s = none) : C254 F := by
  obtain ⟨_, hh, _⟩ := hs
  unfold enumStep execAt at h
  generalize (fetch s).1 = pl1 at h
  generalize (fetch s).2 = np1 at h
  split at h
  · split at h <;> cases h
  · cases h
  · split at h
    · rename_i h1
      rw [h1] at hh
      exact hh
    · cases h
  · cases h

theorem run_inv : ∀ (n : Nat) {s s' : St}, Inv s → run n s = some s' → Inv s'
  | 0, s, s', hs, h => by cases h; exact hs
  | n + 1, s, s', hs, h => by
      unfold run at h
      split at h
      · rename_i s1 h1
        exact run_inv n (step_inv hs h1) h
      · cases h

/-- Soundness of the enumerator: halting yields a derivation of code 1. -/
theorem sound : Halts → C254 F := by
  rintro ⟨n, s, hrun, hstep⟩
  exact halt_step (run_inv n ⟨C254.truth, C254.truth, good_zero⟩ hrun) hstep

/-! ## Completeness: compiling derivations into candidates -/

def cexec : List Cmd → W → Option W
  | [], w => some w
  | c :: cs, w => match cstep c w with
    | some w' => cexec cs w'
    | none => none

theorem cexec_append (p q : List Cmd) (w : W) :
    cexec (p ++ q) w = match cexec p w with
      | some w' => cexec q w'
      | none => none := by
  induction p generalizing w with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.cons_append, cexec]
      cases cstep c w with
      | none => rfl
      | some w' => exact ih w'

def toW (s : St) : W := ⟨s.tw, s.ws, s.d, s.h⟩

theorem execAt_pack (c : Cmd) (r np1 : Nat) (s : St) :
    execAt (pack c r) np1 s =
      match cstep c (toW s) with
      | some w => some ⟨r, np1, w.tw, w.ws, w.d, w.h⟩
      | none => none := by
  cases c with
  | mp x =>
      simp only [execAt, pack, cstep, toW, unP_P']
      split <;> rfl
  | drop x => simp only [execAt, pack, cstep, toW, unP_P']
  | nip x =>
      simp only [execAt, pack, cstep, toW, unP_P']
      split <;> rfl
  | ax c x y u => simp only [execAt, pack, cstep, toW, unP_P']

theorem run_succ (n : Nat) (s s1 : St) (h : enumStep s = some s1) : run (n + 1) s = run n s1 := by
  simp only [run, h]

/-- If a candidate's command list halts, the enumerator halts from its start. -/
theorem exec_list : ∀ (cs : List Cmd) (c : Cmd) (s : St), (fetch s).1 = encL c cs →
    cexec (c :: cs) (toW s) = none → ∃ n s', run n s = some s' ∧ enumStep s' = none
  | [], c, s, hf, hx => by
      refine ⟨0, s, rfl, ?_⟩
      unfold enumStep
      rw [hf, encL, execAt_pack]
      simp only [cexec] at hx
      cases hw : cstep c (toW s) with
      | none => rfl
      | some w => rw [hw] at hx; simp at hx
  | c' :: cs', c, s, hf, hx => by
      simp only [cexec] at hx
      split at hx
      · rename_i w hw
        let s1 : St := ⟨encL c' cs' + 1, (fetch s).2, w.tw, w.ws, w.d, w.h⟩
        have hstep : enumStep s = some s1 := by
          unfold enumStep
          rw [hf, encL, execAt_pack, hw]
        have hf1 : (fetch s1).1 = encL c' cs' := by
          simp [fetch, s1]
        obtain ⟨n, s', hr, hs'⟩ := exec_list cs' c' s1 hf1 hx
        exact ⟨n + 1, s', by rw [run_succ n s s1 hstep]; exact hr, hs'⟩
      · rename_i hw
        refine ⟨0, s, rfl, ?_⟩
        unfold enumStep
        rw [hf, encL, execAt_pack, hw]

/-! ### Every candidate is reached -/

theorem run_add : ∀ (n m : Nat) (s s1 : St), run n s = some s1 → run (n + m) s = run m s1
  | 0, m, s, s1, h => by
      simp only [run] at h; cases h; simp
  | n + 1, m, s, s1, h => by
      simp only [run] at h
      split at h
      · rename_i s2 h2
        have := run_add n m s2 s1 h
        rw [show n + 1 + m = (n + m) + 1 by omega]
        simp only [run, h2]
        exact this
      · cases h

theorem unP_le (z : Nat) : (unP z).1 ≤ z ∧ (unP z).2 ≤ z := ofNat_le z

/-- A step inside a candidate shrinks the proof-list pointer. -/
theorem step_pl {s s1 : St} (hpl : s.pl ≠ 0) (h : enumStep s = some s1) :
    s1.pl < s.pl ∧ s1.np = s.np := by
  unfold enumStep fetch execAt at h
  simp only [hpl, if_false] at h
  have h1 := unP_le (s.pl - 1)
  have h2 := unP_le (unP (s.pl - 1)).2
  have h3 := unP_le (unP (unP (s.pl - 1)).2).2
  have h4 := unP_le (unP (unP (unP (s.pl - 1)).2).2).2
  split at h
  · split at h <;> (cases h; exact ⟨by simp only; omega, rfl⟩)
  · cases h; exact ⟨by simp only; omega, rfl⟩
  · split at h
    · cases h
    · cases h; exact ⟨by simp only; omega, rfl⟩
  · cases h; exact ⟨by simp only; omega, rfl⟩

theorem step_start {s s1 : St} (hpl : s.pl = 0) (h : enumStep s = some s1) : s1.np = s.np + 1 := by
  unfold enumStep fetch execAt at h
  simp only [hpl, if_true] at h
  split at h
  · split at h <;> (cases h; rfl)
  · cases h; rfl
  · split at h
    · cases h
    · cases h; rfl
  · cases h; rfl

/-- A candidate in progress finishes or the enumerator halts. -/
theorem drain : ∀ (m : Nat) (s : St), s.pl ≤ m →
    (∃ n s', run n s = some s' ∧ s'.pl = 0 ∧ s'.np = s.np) ∨
    (∃ n s', run n s = some s' ∧ enumStep s' = none)
  | m, s, hm => by
      by_cases hpl : s.pl = 0
      · exact Or.inl ⟨0, s, rfl, hpl, rfl⟩
      · match hs : enumStep s with
        | none => exact Or.inr ⟨0, s, rfl, hs⟩
        | some s1 =>
          obtain ⟨hlt, hnp⟩ := step_pl hpl hs
          cases m with
          | zero => omega
          | succ m =>
            rcases drain m s1 (by omega) with ⟨n, s', hr, h1, h2⟩ | ⟨n, s', hr, h1⟩
            · exact Or.inl ⟨n + 1, s', by rw [run_succ n s s1 hs]; exact hr, h1, h2.trans hnp⟩
            · exact Or.inr ⟨n + 1, s', by rw [run_succ n s s1 hs]; exact hr, h1⟩

theorem reach : ∀ N : Nat, (∃ n s, run n s0 = some s ∧ s.pl = 0 ∧ s.np = N) ∨ Halts
  | 0 => Or.inl ⟨0, s0, rfl, rfl, rfl⟩
  | N + 1 => by
      rcases reach N with ⟨n, s, hr, hpl, hnp⟩ | hh
      · match hs : enumStep s with
        | none => exact Or.inr ⟨n, s, hr, hs⟩
        | some s1 =>
          have hnp1 : s1.np = N + 1 := by rw [step_start hpl hs, hnp]
          have hr1 : run (n + 1) s0 = some s1 := by
            rw [run_add n 1 s0 s hr]; simp only [run, hs]
          rcases drain s1.pl s1 (Nat.le_refl _) with ⟨k, s', hr', h1, h2⟩ | ⟨k, s', hr', h1⟩
          · left
            exact ⟨n + 1 + k, s', by rw [run_add (n + 1) k s0 s1 hr1]; exact hr', h1, h2.trans hnp1⟩
          · right
            exact ⟨n + 1 + k, s', by rw [run_add (n + 1) k s0 s1 hr1]; exact hr', h1⟩
      · exact Or.inr hh

/-- Any command list that halts from every register state is eventually executed. -/
theorem halts_of_cexec (c : Cmd) (cs : List Cmd) (hall : ∀ w, cexec (c :: cs) w = none) : Halts := by
  rcases reach (encL c cs) with ⟨n, s, hr, hpl, hnp⟩ | hh
  · have hf : (fetch s).1 = encL c cs := by simp [fetch, hpl, hnp]
    obtain ⟨k, s', hr', hs'⟩ := exec_list cs c s hf (hall _)
    exact ⟨n + k, s', by rw [run_add n k s0 s hr]; exact hr', hs'⟩
  · exact hh

/-! ### Block contracts -/

def pushL : List Nat → Nat → Nat
  | [], S => S
  | x :: L, S => P x (pushL L S)

def nips : Nat → List Cmd
  | 0 => []
  | k + 1 => .nip 0 :: nips k

theorem cexec_nips_cons (k : Nat) (t x S d h : Nat) :
    cexec (nips (k + 1)) ⟨t, P x S, d, h⟩ =
      if h = 1 then none else cexec (nips k) ⟨t, S, d, x⟩ := by
  simp only [nips, cexec, cstep, unP_P', Nat.add_zero]
  by_cases h1 : h = 1 <;> simp [h1]

/-- Popping a pushed list whose entries before the last are not the falsity code. -/
theorem cexec_nips (t S d : Nat) : ∀ (L : List Nat) (h last : Nat),
    h ≠ 1 → (∀ x, x ∈ L → x ≠ 1) →
      cexec (nips (L.length + 1)) ⟨t, pushL (L ++ [last]) S, d, h⟩ = some ⟨t, S, d, last⟩
  | [], h, last, hh, _ => by
      simp only [List.nil_append, pushL, List.length_nil, Nat.zero_add]
      rw [cexec_nips_cons, if_neg hh]; rfl
  | x :: L, h, last, hh, hL => by
      simp only [List.cons_append, pushL, List.length_cons]
      rw [cexec_nips_cons, if_neg hh]
      exact cexec_nips t S d L x last (hL x (List.mem_cons_self ..))
        (fun y hy => hL y (List.mem_cons_of_mem _ hy))

theorem wim_ne_one (a b : Nat) : wim a b ≠ 1 := by simp only [wim]; omega
theorem wal_ne_one (a b : Nat) : wal a b ≠ 1 := by simp only [wal]; omega

theorem gate_ne_one (a b c : Nat) : gate a b c ≠ 1 := by
  unfold gate; split
  · omega
  · exact wim_ne_one _ _

/-- The first nine entries pushed by AX, top first; the tenth is the old `tw`. -/
def axList (a h b c u : Nat) : List Nat :=
  [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c, rho6 a b, rho7 a b c,
   rho8 a b c u, wal a h]

theorem axStack_eq (a h b c u t w : Nat) :
    axStack a h b c u t w = pushL (axList a h b c u ++ [t]) w := rfl

theorem axList_ne_one (a h b c u : Nat) : ∀ x, x ∈ axList a h b c u → x ≠ 1 := by
  intro x hx
  simp only [axList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact wim_ne_one _ _ | exact wal_ne_one _ _

/-- A block maps `(T, S, 0, 0)` to `(X, S, 0, 0)` or halts. -/
def Contract (p : List Cmd) (X : Nat) : Prop :=
  ∀ T S : Nat, cexec p ⟨T, S, 0, 0⟩ = none ∨ cexec p ⟨T, S, 0, 0⟩ = some ⟨X, S, 0, 0⟩

def discard : List Cmd := [.mp 1, .ax 1 0 0 0] ++ nips 10

theorem cstep_mp_fail (x T S d h : Nat) (hw : wim T (d + x) ≠ h) :
    cstep (.mp x) ⟨T, S, d, h⟩ = some ⟨0, S, d + x, 0⟩ := by
  simp [cstep, hw]

theorem cstep_ax (c x y u t S d h : Nat) :
    cstep (.ax c x y u) ⟨t, S, d, h⟩ =
      some ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c u t S, 0, 0⟩ := rfl

theorem gate_self (a b : Nat) : gate a b a = 0 := by simp [gate]

theorem cexec_discard (T S : Nat) : cexec discard ⟨T, S, 0, 0⟩ = some ⟨0, S, 0, 0⟩ := by
  have hw : wim T (0 + 1) ≠ 0 := by
    simp only [wim, Nat.zero_add]
    have := le_P_right T 1
    omega
  rw [discard, cexec_append]
  simp only [cexec]
  rw [cstep_mp_fail 1 T S 0 0 hw]
  simp only
  rw [cstep_ax]
  simp only
  rw [show gate (0 + 1) (0 + 0) 1 = 0 from gate_self _ _, axStack_eq]
  exact cexec_nips 0 S 0 (axList (0 + 1) 0 (0 + 0) 1 0) 0 0 (by omega) (axList_ne_one _ _ _ _ _)

theorem cexec_cons_some {c : Cmd} {cs : List Cmd} {w w' : W} (h : cstep c w = some w') :
    cexec (c :: cs) w = cexec cs w' := by
  simp only [cexec, h]

theorem cexec_cons_none {c : Cmd} {cs : List Cmd} {w : W} (h : cstep c w = none) :
    cexec (c :: cs) w = none := by
  simp only [cexec, h]

theorem cstep_nip (x t S d h : Nat) (hh : h ≠ 1) :
    cstep (.nip x) ⟨t, S, d, h⟩ = some ⟨t, (unP S).2, d + x, (unP S).1⟩ := by
  simp [cstep, hh]

theorem cstep_nip_one (x t S d : Nat) : cstep (.nip x) ⟨t, S, d, 1⟩ = none := by
  simp [cstep]

theorem cstep_drop (x t S d h : Nat) : cstep (.drop x) ⟨t, S, d, h⟩ = some ⟨h, P t S, d + x, h⟩ :=
  rfl

theorem cstep_mp_ok (x T S d h : Nat) (hw : wim T (d + x) = h) :
    cstep (.mp x) ⟨T, S, d, h⟩ = some ⟨d + x, P 0 S, d + x, 0⟩ := by
  simp [cstep, hw]

theorem pushL_append (L1 L2 : List Nat) (S : Nat) : pushL (L1 ++ L2) S = pushL L1 (pushL L2 S) := by
  induction L1 with
  | nil => rfl
  | cons x L ih => simp only [List.cons_append, pushL, ih]

theorem nips_append (j k : Nat) : nips (j + k) = nips j ++ nips k := by
  induction j with
  | zero => simp [nips]
  | succ j ih => rw [show j + 1 + k = (j + k) + 1 by omega]; simp [nips, ih]

theorem cexec_nips' (t S d : Nat) (L : List Nat) (h last : Nat) (rest : List Cmd)
    (hh : h ≠ 1) (hL : ∀ x, x ∈ L → x ≠ 1) :
    cexec (nips (L.length + 1) ++ rest) ⟨t, pushL (L ++ [last]) S, d, h⟩ =
      cexec rest ⟨t, S, d, last⟩ := by
  rw [cexec_append, cexec_nips t S d L h last hh hL]

/-- Pop down to a selected entry, make it current, and pop the rest. -/
theorem select_entry (L1 : List Nat) (x : Nat) (L2 : List Nat) (last g h0 S : Nat)
    (hh : h0 ≠ 1) (hg : g ≠ 1) (hx : x ≠ 1) (h1 : ∀ y, y ∈ L1 → y ≠ 1)
    (h2 : ∀ y, y ∈ L2 → y ≠ 1) :
    cexec (nips (L1.length + 1) ++ (.drop 0 :: nips (L2.length + 2)))
      ⟨g, pushL (L1 ++ x :: (L2 ++ [last])) S, 0, h0⟩ = some ⟨x, S, 0, last⟩ := by
  have hs : pushL (L1 ++ x :: (L2 ++ [last])) S = pushL (L1 ++ [x]) (pushL (L2 ++ [last]) S) := by
    rw [← pushL_append]; simp
  rw [hs, cexec_nips' g _ 0 L1 h0 x _ hh h1, cexec_cons_some (cstep_drop 0 g _ 0 x)]
  have := cexec_nips x S (0 + 0) (g :: L2) x last hx (fun y hy => by
    cases List.mem_cons.mp hy with
    | inl e => rw [e]; exact hg
    | inr hy => exact h2 y hy)
  rw [show L2.length + 2 = (g :: L2).length + 1 by simp]
  simpa [pushL] using this

/-- After `discard`, an AX command with `x = a`, `y = b` pushes the rows at `(a, b, c, u)`. -/
theorem cexec_discard_ax (T S a b c u : Nat) (rest : List Cmd) :
    cexec (discard ++ (.ax c a b u :: rest)) ⟨T, S, 0, 0⟩ =
      cexec rest ⟨gate a b c, pushL (axList a 0 b c u ++ [0]) S, 0, 0⟩ := by
  rw [cexec_append, cexec_discard]
  simp only
  rw [cexec_cons_some (cstep_ax c a b u 0 S 0 0)]
  simp only [Nat.zero_add]
  rfl

/-- The leaf block for one emitted row, by its position. -/
def leaf (j a b c u : Nat) : List Cmd :=
  discard ++ (.ax c a b u :: (nips j ++ (.drop 0 :: nips (11 - j))))

theorem rows_ne (a b c u : Nat) (L : List Nat)
    (hL : L ⊆ [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c, rho6 a b, rho7 a b c,
      rho8 a b c u, wal a 0]) : ∀ y, y ∈ L → y ≠ 1 := by
  intro y hy
  exact axList_ne_one a 0 b c u y (hL hy)

theorem leaf_contract (j a b c u x : Nat) (L1 L2 : List Nat)
    (hsplit : axList a 0 b c u = L1 ++ x :: L2)
    (hj : L1.length + 1 = j) (hk : L2.length + 2 = 11 - j) : Contract (leaf j a b c u) x := by
  intro T S
  right
  have hx : x ≠ 1 := axList_ne_one a 0 b c u x (by rw [hsplit]; simp)
  have h1 : ∀ y, y ∈ L1 → y ≠ 1 := fun y hy => axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  have h2 : ∀ y, y ∈ L2 → y ≠ 1 := fun y hy => axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  rw [leaf, cexec_discard_ax, hsplit, ← hk, ← hj]
  have := select_entry L1 x L2 0 (gate a b c) 0 S (by omega) (gate_ne_one a b c) hx h1 h2
  simpa [List.append_assoc] using this

theorem leaf1 (a b : Nat) : Contract (leaf 1 a b 0 0) (rho1 a b) :=
  leaf_contract 1 a b 0 0 _ [] _ rfl rfl rfl
theorem leaf2 (a b c : Nat) : Contract (leaf 2 a b c 0) (rho2 a b c) :=
  leaf_contract 2 a b c 0 _ [_] _ rfl rfl rfl
theorem leaf3 (a b c : Nat) : Contract (leaf 3 a b c 0) (rho3 a b c) :=
  leaf_contract 3 a b c 0 _ [_, _] _ rfl rfl rfl
theorem leaf4 (a b c : Nat) : Contract (leaf 4 a b c 0) (rho4 a b c) :=
  leaf_contract 4 a b c 0 _ [_, _, _] _ rfl rfl rfl
theorem leaf5 (a b c : Nat) : Contract (leaf 5 a b c 0) (rho5 a b c) :=
  leaf_contract 5 a b c 0 _ [_, _, _, _] _ rfl rfl rfl
theorem leaf6 (a b : Nat) : Contract (leaf 6 a b 0 0) (rho6 a b) :=
  leaf_contract 6 a b 0 0 _ [_, _, _, _, _] _ rfl rfl rfl
theorem leaf7 (a b c : Nat) : Contract (leaf 7 a b c 0) (rho7 a b c) :=
  leaf_contract 7 a b c 0 _ [_, _, _, _, _, _] _ rfl rfl rfl
theorem leaf8 (a b c u : Nat) : Contract (leaf 8 a b c u) (rho8 a b c u) :=
  leaf_contract 8 a b c u _ [_, _, _, _, _, _, _] _ rfl rfl rfl

/-- The bundle leaf. -/
def bundleLeaf (a b c : Nat) : List Cmd := discard ++ (.ax c a b 0 :: nips 10)

theorem bundle_contract (a b c : Nat) (h1 : c ≠ a) (h2 : c ≠ b) :
    Contract (bundleLeaf a b c) (bundle a b c) := by
  intro T S
  right
  rw [bundleLeaf, cexec_discard_ax]
  have hg : gate a b c = bundle a b c := by
    simp [gate, h1, h2]
  rw [hg, show nips 10 = nips ((axList a 0 b c 0).length + 1) from rfl]
  exact cexec_nips (bundle a b c) S 0 (axList a 0 b c 0) 0 0 (by omega) (axList_ne_one _ _ _ _ _)

/-- Generalization of a block's result. -/
def genBlock (i : Nat) (p : List Cmd) : List Cmd :=
  p ++ (.drop 0 :: .nip 0 :: .ax i i 0 0 :: (nips 9 ++ [.drop 0, .nip 0, .nip 0]))

theorem gen_contract (i : Nat) {p : List Cmd} {H : Nat} (hp : Contract p H) :
    Contract (genBlock i p) (wal i H) := by
  intro T S
  rcases hp T S with hn | hs
  · left; rw [genBlock, cexec_append, hn]
  · right
    rw [genBlock, cexec_append, hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 H S 0 0),
      cexec_cons_some (cstep_nip 0 0 (P H S) (0 + 0) 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    rw [cexec_cons_some (cstep_ax i i 0 0 0 S 0 H)]
    simp only [Nat.zero_add, Nat.add_zero]
    rw [show gate i H i = 0 from gate_self i H, axStack_eq]
    have hsplit : axList i H H i 0 ++ [0] =
        [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i H, rho7 i H i,
          rho8 i H i 0] ++ [wal i H] ++ [0] := rfl
    rw [hsplit, pushL_append, pushL_append]
    have hL : ∀ y, y ∈ [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i H,
        rho7 i H i, rho8 i H i 0] → y ≠ 1 := fun y hy =>
      axList_ne_one i H H i 0 y (by simp [axList] at hy ⊢; omega)
    rw [show nips 9 = nips ([rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i H,
        rho7 i H i, rho8 i H i 0].length + 1) from rfl, ← pushL_append]
    rw [cexec_nips' 0 (pushL [0] S) 0 _ 0 (wal i H) _ (by omega) hL]
    rw [cexec_cons_some (cstep_drop 0 0 (pushL [0] S) 0 (wal i H))]
    rw [cexec_cons_some (cstep_nip 0 (wal i H) (P 0 (pushL [0] S)) (0 + 0) (wal i H)
      (wal_ne_one i H))]
    simp only [unP_P', pushL, Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 (wal i H) (P 0 S) 0 0 (by omega))]
    simp [unP_P', cexec]

/-- Modus ponens on two blocks. -/
def mpBlock (B : Nat) (pa pab : List Cmd) : List Cmd :=
  pa ++ (.drop 0 :: (pab ++ (.nip 0 :: .drop 0 :: .nip 0 :: .mp B :: .ax B 0 0 0 ::
    (nips 10 ++ [.drop 0, .nip 0, .nip 0]))))

theorem mp_contract {A B : Nat} {pa pab : List Cmd} (ha : Contract pa A)
    (hab : Contract pab (wim A B)) : Contract (mpBlock B pa pab) B := by
  intro T S
  rcases ha T S with hn | hs
  · left; rw [mpBlock, cexec_append, hn]
  · rw [mpBlock, cexec_append, hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 A S 0 0)]
    simp only [Nat.add_zero]
    rcases hab 0 (P A S) with hn2 | hs2
    · left; rw [cexec_append, hn2]
    · rw [cexec_append, hs2]
      simp only
      rw [cexec_cons_some (cstep_nip 0 (wim A B) (P A S) 0 0 (by omega))]
      simp only [unP_P', Nat.add_zero]
      rw [cexec_cons_some (cstep_drop 0 (wim A B) S 0 A)]
      simp only [Nat.add_zero]
      by_cases hA : A = 1
      · left
        rw [hA, cexec_cons_none (cstep_nip_one 0 1 (P (wim 1 B) S) 0)]
      · rw [cexec_cons_some (cstep_nip 0 A (P (wim A B) S) 0 A hA)]
        simp only [unP_P', Nat.add_zero]
        rw [cexec_cons_some (cstep_mp_ok B A S 0 (wim A B) (by simp))]
        simp only [Nat.zero_add]
        rw [cexec_cons_some (cstep_ax B 0 0 0 B (P 0 S) B 0)]
        simp only [Nat.add_zero]
        rw [show gate B 0 B = 0 from gate_self B 0, axStack_eq,
          show nips 10 = nips ((axList B 0 0 B 0).length + 1) from rfl, cexec_append,
          cexec_nips 0 (P 0 S) 0 (axList B 0 0 B 0) 0 B (by omega) (axList_ne_one _ _ _ _ _)]
        simp only
        rw [cexec_cons_some (cstep_drop 0 0 (P 0 S) 0 B)]
        simp only [Nat.add_zero]
        by_cases hB : B = 1
        · left
          rw [hB, cexec_cons_none (cstep_nip_one 0 1 (P 0 (P 0 S)) 0)]
        · right
          rw [cexec_cons_some (cstep_nip 0 B (P 0 (P 0 S)) 0 B hB)]
          simp only [unP_P', Nat.add_zero]
          rw [cexec_cons_some (cstep_nip 0 B (P 0 S) 0 0 (by omega))]
          simp [unP_P', cexec]

/-- Every derivable code has a block computing it. -/
theorem build : ∀ {n : Nat}, C254 n → ∃ p : List Cmd, Contract p n := by
  intro n h
  induction h with
  | truth => exact ⟨discard, fun T S => Or.inr (cexec_discard T S)⟩
  | mp _ _ ih1 ih2 =>
      obtain ⟨pa, ha⟩ := ih1
      obtain ⟨pab, hab⟩ := ih2
      exact ⟨_, mp_contract ha hab⟩
  | gen a _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨_, gen_contract a hp⟩
  | r1 a b => exact ⟨_, leaf1 a b⟩
  | r2 a b c => exact ⟨_, leaf2 a b c⟩
  | r3 a b c => exact ⟨_, leaf3 a b c⟩
  | r4 a b c => exact ⟨_, leaf4 a b c⟩
  | r5 a b c => exact ⟨_, leaf5 a b c⟩
  | r6 a b => exact ⟨_, leaf6 a b⟩
  | r7 a b c => exact ⟨_, leaf7 a b c⟩
  | r8 a b c u => exact ⟨_, leaf8 a b c u⟩
  | bundle a b c h1 h2 => exact ⟨_, bundle_contract a b c h1 h2⟩

/-- Completeness of the enumerator. -/
theorem complete (h : C254 F) : Halts := by
  obtain ⟨p, hp⟩ := build h
  apply halts_of_cexec (.ax 0 1 1 0) (p ++ [.drop 0, .nip 0, .nip 0])
  intro w
  obtain ⟨t, S, d, hh⟩ := w
  rw [cexec_cons_some (cstep_ax 0 1 1 0 t S d hh), cexec_append]
  rcases hp (gate (d + 1) (hh + 1) 0) (axStack (d + 1) hh (hh + 1) 0 0 t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop 0 F _ 0 0)]
    simp only [Nat.add_zero]
    rw [cexec_cons_some (cstep_nip 0 0 _ 0 0 (by omega))]
    simp only [unP_P', Nat.add_zero]
    exact cexec_cons_none (cstep_nip_one 0 0 _ 0)

/-- L1: the enumerator halts from the zero state iff code 1 is derivable. -/
theorem enum_halts_iff : Halts ↔ C254 F := ⟨sound, complete⟩

/-- If the enumerator halts, the decoded bundle theory has no irreflexive model. -/
theorem halts_no_model (h : Halts) {D : Type} (mem : D → D → Prop) (hirr : ∀ x, ¬ mem x x)
    (hB : ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → D, Tarski.Sat mem e (dec (bundle a b c)))
    (e : Nat → D) : False :=
  no_model_of_c254_one (sound h) mem hirr hB e

/-- If the encodable bundle theory has no irreflexive model with a valuation,
the enumerator halts. The valuation is necessary: the former premise without
it was refuted by Code254.empty_domain_counterexample. -/
theorem halts_of_no_model
    (hnone : ∀ (D : Type) (mem : D → D → Prop), (∀ x, ¬ mem x x) →
      (∀ f, EncBundle f → ∀ e : Nat → D, Tarski.Sat mem e f) →
      (Nat → D) → False) : Halts :=
  complete (c254_complete hnone)

end SetTheory.BusyBeaver.ZFC.Enum254
