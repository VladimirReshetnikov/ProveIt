import BusyBeaver.ZFC.KCode222
import BusyBeaver.ZFC.DomRho8

/-!
The abstract proof enumerator of the 217-state machine (Source 149's dominated AX), and L1.

The registers and the MP, DROP and NIP commands are `Enum222`'s. The AX command reads its three
fields `z, y, x` as

```text
3 + c  AX   z y x   U := d + z; A := U + x; B := h + y;
                    push tw, All(U,h), rho8(A,B,c,U), G(A,B,c), rho6 … rho1 at (A,B,c);
                    tw := (c = A or c = B ? 0 : bundle A B c); d := 0; h := 0
```

so every emitted rho8 instance has its fourth argument at most its first.

Main theorem `halts_iff`: from any state between candidates whose registers hold derivable
codes, the enumerator halts iff the falsity code 1 is derivable in `C222`. Soundness is
`Enum222`'s stack invariant. Completeness compiles `C222` directly into command blocks,
interpreting the dominated-implication theorem in `fun n => ∃ p, Contract p n` (a dominated rho8
leaf `rho8 a b c u`, `u ≤ a`, is `AX(c, u, b, a - u)`), behind `START_Y = AX(0, 1, Y, 0)`, whose
candidate number is at least `Y`.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumDom

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222

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

/-- The stack after AX: `tw` first, then GEN of the cache at `u`, then rho8 … rho1. -/
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w)))))))))

def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle222 a b c

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
      some ⟨gate (d + x + u) (h + y) c, axStack (d + x + u) h (h + y) c (d + x) t s, 0, 0⟩

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
            gate (s.d + (unP (unP pl1).2).1 + (unP (unP (unP (unP pl1).2).2).2).1)
              (s.h + (unP (unP (unP pl1).2).2).1) c,
            axStack (s.d + (unP (unP pl1).2).1 + (unP (unP (unP (unP pl1).2).2).2).1) s.h
              (s.h + (unP (unP (unP pl1).2).2).1) c (s.d + (unP (unP pl1).2).1) s.tw s.ws, 0, 0⟩

/-- One step of the enumerator. -/
def enumStep (s : St) : Option St := execAt (fetch s).1 (fetch s).2 s

def run : Nat → St → Option St
  | 0, s => some s
  | n + 1, s => match enumStep s with
    | some s' => run n s'
    | none => none

/-- The enumerator halts from `s`: some reachable state takes a halting step. -/
def HaltsFrom (s : St) : Prop := ∃ n s', run n s = some s' ∧ enumStep s' = none

/-! ## Soundness -/

/-- The stream after dropping `k` entries. -/
def tailN : Nat → Nat → Nat
  | 0, z => z
  | k + 1, z => tailN k (unP z).2

/-- Every entry of a stream is derivable. -/
def Good (z : Nat) : Prop := ∀ k, C222 (unP (tailN k z)).1

theorem tailN_zero : ∀ k, tailN k 0 = 0
  | 0 => rfl
  | k + 1 => by
      have h0 : (unP 0).2 = 0 := rfl
      simp only [tailN, h0, tailN_zero k]

theorem good_zero : Good 0 := by
  intro k
  rw [tailN_zero k]; exact C222.truth

theorem good_cons {x z : Nat} (hx : C222 x) (hz : Good z) : Good (P x z) := by
  intro k
  cases k with
  | zero => simpa [tailN, unP_P'] using hx
  | succ k => simpa [tailN, unP_P'] using hz k

theorem good_head {z : Nat} (hz : Good z) : C222 (unP z).1 := hz 0

theorem good_tail {z : Nat} (hz : Good z) : Good (unP z).2 := fun k => hz (k + 1)

def Inv (s : St) : Prop := C222 s.tw ∧ C222 s.h ∧ Good s.ws

theorem gate_good (a b c : Nat) : C222 (gate a b c) := by
  unfold gate
  split
  · exact C222.truth
  · rename_i h
    exact C222.bundle a b c (fun e => h (Or.inl e)) (fun e => h (Or.inr e))

theorem axStack_good (a h b c u t w : Nat) (hh : C222 h) (ht : C222 t) (hw : Good w) :
    Good (axStack a h b c u t w) := by
  unfold axStack
  exact good_cons (C222.r1 a b) <| good_cons (C222.r2 a b c) <| good_cons (C222.r3 a b c) <|
    good_cons (C222.r4 a b c) <| good_cons (C222.r5 a b c) <| good_cons (C222.r6 a c) <|
    good_cons (C222.rG a b c) <| good_cons (C222.r8 a b c u) <| good_cons (C222.gen u hh) <|
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
      refine ⟨?_, C222.truth, good_cons C222.truth hw⟩
      exact C222.mp ht (heq ▸ hh)
    · cases h
      exact ⟨C222.truth, C222.truth, hw⟩
  · cases h
    exact ⟨hh, hh, good_cons ht hw⟩
  · split at h
    · cases h
    · cases h
      exact ⟨ht, good_head hw, good_tail hw⟩
  · cases h
    exact ⟨gate_good _ _ _, C222.truth, axStack_good _ _ _ _ _ _ _ hh ht hw⟩

theorem halt_step {s : St} (hs : Inv s) (h : enumStep s = none) : C222 F := by
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

/-- Soundness of the enumerator: from derivable registers, halting yields a derivation of 1. -/
theorem sound {s : St} (hs : Inv s) : HaltsFrom s → C222 F := by
  rintro ⟨n, s', hrun, hstep⟩
  exact halt_step (run_inv n hs hrun) hstep

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

/-- From a state between candidates, every later candidate is reached unless the run halts. -/
theorem reach (sd : St) (hpl : sd.pl = 0) : ∀ k : Nat,
    (∃ n s, run n sd = some s ∧ s.pl = 0 ∧ s.np = sd.np + k) ∨ HaltsFrom sd
  | 0 => Or.inl ⟨0, sd, rfl, hpl, rfl⟩
  | k + 1 => by
      rcases reach sd hpl k with ⟨n, s, hr, hpl', hnp⟩ | hh
      · match hs : enumStep s with
        | none => exact Or.inr ⟨n, s, hr, hs⟩
        | some s1 =>
          have hnp1 : s1.np = sd.np + (k + 1) := by rw [step_start hpl' hs, hnp]; omega
          have hr1 : run (n + 1) sd = some s1 := by
            rw [run_add n 1 sd s hr]; simp only [run, hs]
          rcases drain s1.pl s1 (Nat.le_refl _) with ⟨j, s', hr', h1, h2⟩ | ⟨j, s', hr', h1⟩
          · left
            exact ⟨n + 1 + j, s', by rw [run_add (n + 1) j sd s1 hr1]; exact hr', h1, h2.trans hnp1⟩
          · right
            exact ⟨n + 1 + j, s', by rw [run_add (n + 1) j sd s1 hr1]; exact hr', h1⟩
      · exact Or.inr hh

/-! ### Block contracts, by symbolic execution -/

def nips : Nat → List Cmd
  | 0 => []
  | k + 1 => .nip 0 :: nips k

theorem cexec_cons_some {c : Cmd} {cs : List Cmd} {w w' : W} (h : cstep c w = some w') :
    cexec (c :: cs) w = cexec cs w' := by
  simp only [cexec, h]

theorem ex_nil (w : W) : cexec [] w = some w := rfl

theorem ex_nip {k t x S d h : Nat} {cs : List Cmd} (hh : h ≠ 1) :
    cexec (.nip k :: cs) ⟨t, P x S, d, h⟩ = cexec cs ⟨t, S, d + k, x⟩ := by
  simp [cexec, cstep, hh, unP_P']

theorem ex_nip1 {k t S d : Nat} {cs : List Cmd} : cexec (.nip k :: cs) ⟨t, S, d, 1⟩ = none := by
  simp [cexec, cstep]

/- `ex_drop` and `ex_ax` hold by `rfl`, but are stated through `cexec_cons_some`: as `rfl`
lemmas, simp would leave the kernel to check `cexec (c :: cs) w ≡ cexec cs w'` by unfolding
`cexec` on both sides, evaluating the pops of closed pairing numerals. -/
theorem ex_drop {k t S d h : Nat} {cs : List Cmd} :
    cexec (.drop k :: cs) ⟨t, S, d, h⟩ = cexec cs ⟨h, P t S, d + k, h⟩ := cexec_cons_some rfl

theorem ex_ax {c x y u t S d h : Nat} {cs : List Cmd} :
    cexec (.ax c x y u :: cs) ⟨t, S, d, h⟩ =
      cexec cs ⟨gate (d + x + u) (h + y) c, axStack (d + x + u) h (h + y) c (d + x) t S, 0, 0⟩ :=
  cexec_cons_some rfl

theorem ex_mp_ok {x T S d h : Nat} {cs : List Cmd} (hw : wim T (d + x) = h) :
    cexec (.mp x :: cs) ⟨T, S, d, h⟩ = cexec cs ⟨d + x, P 0 S, d + x, 0⟩ := by
  simp [cexec, cstep, hw]

theorem ex_mp_fail {x T S d h : Nat} {cs : List Cmd} (hw : wim T (d + x) ≠ h) :
    cexec (.mp x :: cs) ⟨T, S, d, h⟩ = cexec cs ⟨0, S, d + x, 0⟩ := by
  simp [cexec, cstep, hw]

theorem wim_ne_one (a b : Nat) : wim a b ≠ 1 := by simp only [wim]; omega
theorem wal_ne_one (a b : Nat) : wal a b ≠ 1 := by simp only [wal]; omega

theorem gate_ne_one (a b c : Nat) : gate a b c ≠ 1 := by
  unfold gate; split
  · omega
  · exact wim_ne_one _ _

theorem gate_self (a b : Nat) : gate a b a = 0 := by simp [gate]

/-- Every pushed row is a `wim` or a `wal`, so none is the falsity code. These are stated once
with variables: the symbolic runs below must never ask the kernel to unfold a row at numerals,
where nested pairings explode. -/
theorem rho1_ne (a b : Nat) : rho1 a b ≠ 1 := wim_ne_one _ _
theorem rho2_ne (a b c : Nat) : rho2 a b c ≠ 1 := wim_ne_one _ _
theorem rho3_ne (a b c : Nat) : rho3 a b c ≠ 1 := wim_ne_one _ _
theorem rho4_ne (a b c : Nat) : rho4 a b c ≠ 1 := wim_ne_one _ _
theorem rho5_ne (a b c : Nat) : rho5 a b c ≠ 1 := wim_ne_one _ _
theorem rho6_ne (a c : Nat) : rho6 a c ≠ 1 := wim_ne_one _ _
theorem growG_ne (a b c : Nat) : growG a b c ≠ 1 := wim_ne_one _ _
theorem rho8_ne (a b c u : Nat) : rho8 a b c u ≠ 1 := wim_ne_one _ _

/-- A popped entry is not the falsity code. -/
macro "ne1" : tactic => `(tactic| first | assumption | (simp only [ne_eq, Nat.zero_add,
  Nat.add_zero, Nat.zero_ne_one, rho1_ne, rho2_ne, rho3_ne, rho4_ne, rho5_ne, rho6_ne, growG_ne,
  rho8_ne, wim_ne_one, wal_ne_one, gate_ne_one, not_false_eq_true]; done))

/-- Symbolic execution of a block on an explicit register file. -/
macro "xrun" : tactic => `(tactic| simp (disch := ne1) only
  [ex_nil, ex_drop, ex_ax, ex_nip, ex_nip1, ex_mp_ok, axStack, gate_self, nips,
    List.cons_append, List.nil_append, Nat.add_zero, Nat.zero_add])

/-- A block maps `(T, S, 0, 0)` to `(X, S, 0, 0)` or halts. -/
def Contract (p : List Cmd) (X : Nat) : Prop :=
  ∀ T S : Nat, cexec p ⟨T, S, 0, 0⟩ = none ∨ cexec p ⟨T, S, 0, 0⟩ = some ⟨X, S, 0, 0⟩

def discard : List Cmd := [.mp 1, .ax 1 0 0 0] ++ nips 10

theorem cexec_discard (T S : Nat) : cexec discard ⟨T, S, 0, 0⟩ = some ⟨0, S, 0, 0⟩ := by
  have hw : wim T (0 + 1) ≠ 0 := by
    simp only [wim, Nat.zero_add]
    have := le_P_right T 1
    omega
  rw [discard, List.cons_append, ex_mp_fail hw]
  xrun

/-- After `discard`, `AX(c, u, b, a - u)` with `u ≤ a` pushes the rows at `(a, b, c, u)`. -/
theorem cexec_discard_ax (T S a b c u : Nat) (hu : u ≤ a) (rest : List Cmd) :
    cexec (discard ++ (.ax c u b (a - u) :: rest)) ⟨T, S, 0, 0⟩ =
      cexec rest ⟨gate a b c, axStack a 0 b c u 0 S, 0, 0⟩ := by
  rw [cexec_append, cexec_discard]
  simp only
  rw [ex_ax]
  simp only [Nat.zero_add, show u + (a - u) = a by omega]

/-- The leaf for the AX row at position `j`: pop to it, keep it, pop the rest. -/
def leaf (j a b c u : Nat) : List Cmd :=
  discard ++ (.ax c u b (a - u) :: (nips j ++ (.drop 0 :: nips (11 - j))))

/-- The bundle leaf. -/
def bundleLeaf (a b c : Nat) : List Cmd := discard ++ (.ax c a b (a - a) :: nips 10)

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
    xrun

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
    simp only [ex_drop, Nat.add_zero]
    rw [cexec_append]
    rcases hab 0 (P A S) with hn2 | hs2
    · left; rw [hn2]
    · rw [hs2]
      simp only
      by_cases hA : A = 1
      · left; subst hA; xrun
      · by_cases hB : B = 1
        · left; subst hB; xrun
        · right; xrun

/-- Compile directly in the algebra of block contracts: the restricted rho8 theorem,
interpreted in `fun n => ∃ p, Contract p n`, gives every unrestricted rho8 row. -/
theorem build : ∀ {n : Nat}, C222 n → ∃ p : List Cmd, Contract p n := by
  have hmp {A B : Nat} (hab : ∃ p : List Cmd, Contract p (wim A B))
      (ha : ∃ p : List Cmd, Contract p A) : ∃ p : List Cmd, Contract p B := by
    obtain ⟨pab, hab⟩ := hab
    obtain ⟨pa, ha⟩ := ha
    exact ⟨_, mp_contract ha hab⟩
  have hrow (a b c u : Nat) (hu : u ≤ a) : ∃ p : List Cmd, Contract p (rho8 a b c u) :=
    ⟨leaf 8 a b c u, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ hu]; xrun)⟩
  intro n h
  induction h with
  | truth => exact ⟨discard, fun T S => Or.inr (cexec_discard T S)⟩
  | mp _ _ ih1 ih2 => exact hmp ih2 ih1
  | gen a _ ih =>
      obtain ⟨p, hp⟩ := ih
      exact ⟨_, gen_contract a hp⟩
  | bundle a b c h1 h2 =>
      refine ⟨bundleLeaf a b c, fun T S => Or.inr ?_⟩
      rw [bundleLeaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a),
        show gate a b c = bundle222 a b c by simp [gate, h1, h2]]
      xrun
  | r1 a b => exact ⟨leaf 1 a b 0 a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | r2 a b c => exact ⟨leaf 2 a b c a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | r3 a b c => exact ⟨leaf 3 a b c a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | r4 a b c => exact ⟨leaf 4 a b c a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | r5 a b c => exact ⟨leaf 5 a b c a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | r6 a b => exact ⟨leaf 6 a 0 b a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | rG a b c => exact ⟨leaf 7 a b c a, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (Nat.le_refl a)]; xrun)⟩
  | r8 a b c u =>
      exact DomRho8.rho8_all_of_restricted (T := fun n => ∃ p : List Cmd, Contract p n)
        hmp hrow a b c u

/-- `START_Y = AX(0, 1, Y, 0)` clears the counter and the cache from every state; with a block
for 1 and `DROP; NIP; NIP`, the list halts from every state. -/
theorem program_none (Y : Nat) (p : List Cmd) (hp : Contract p F) :
    ∀ w, cexec (.ax 0 1 Y 0 :: (p ++ [.drop 0, .nip 0, .nip 0])) w = none := by
  rintro ⟨t, S, d, h⟩
  rw [ex_ax, cexec_append]
  rcases hp (gate (d + 1 + 0) (h + Y) 0) (axStack (d + 1 + 0) h (h + Y) 0 (d + 1) t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only [F]
    xrun

theorem encL_ge (Y : Nat) (cs : List Cmd) : Y ≤ encL (.ax 0 1 Y 0) cs := by
  have key : ∀ r, Y ≤ pack (.ax 0 1 Y 0) r := fun r =>
    Nat.le_trans (le_P_left Y (P 0 r)) (Nat.le_trans (le_P_right 1 (P Y (P 0 r)))
      (le_P_right (0 + 3) (P 1 (P Y (P 0 r)))))
  cases cs <;> exact key _

/-- Completeness: between candidates, a derivation of code 1 is eventually run. -/
theorem complete {sd : St} (hpl : sd.pl = 0) (h : C222 F) : HaltsFrom sd := by
  obtain ⟨p, hp⟩ := build h
  let cs := p ++ [.drop 0, .nip 0, .nip 0]
  have hN := encL_ge sd.np cs
  rcases reach sd hpl (encL (.ax 0 1 sd.np 0) cs - sd.np) with ⟨n, s, hr, hpl', hnp⟩ | hh
  · have hf : (fetch s).1 = encL (.ax 0 1 sd.np 0) cs := by simp only [fetch, hpl', if_true]; omega
    obtain ⟨k, s', hr', hs'⟩ := exec_list cs (.ax 0 1 sd.np 0) s hf (program_none sd.np p hp _)
    exact ⟨n + k, s', by rw [run_add n k sd s hr]; exact hr', hs'⟩
  · exact hh

/-- L1: between candidates, with derivable registers, the enumerator halts iff code 1 is
derivable. -/
theorem halts_iff {s : St} (hpl : s.pl = 0) (hs : Inv s) : HaltsFrom s ↔ C222 F :=
  ⟨sound hs, complete hpl⟩

end SetTheory.BusyBeaver.ZFC.EnumDom
