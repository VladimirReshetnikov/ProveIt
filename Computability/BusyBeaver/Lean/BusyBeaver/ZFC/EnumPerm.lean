import BusyBeaver.ZFC.KCode222
import BusyBeaver.ZFC.DomRho8

/-!
The abstract proof enumerator of the 215-state machine (Source 159's command-permuted
commands on Source 149's dominated AX), and L1.

The registers are `Enum222`'s. Commands are read from the proof list with the pairing inverse;
the counter field is read by the commands that use it, and the three small commands are
permuted:

```text
0      NIP          if h = 1 then HALT else h := pop
1      DROP         push tw; tw := h
2      MP   x       d += x; if Imp(tw, d) = h then tw := d, push 0 else tw := 0; h := 0
3 + c  AX   y x     U := d; A := d + x; B := h + y;
                    push tw, All(U,h), rho8(A,B,c,U), G(A,B,c), rho6 … rho1 at (A,B,c);
                    tw := (c = A or c = B ? 0 : bundle A B c); d := 0; h := 0
```

`AX` reads `y` first. Every emitted rho8 instance has its fourth argument at most its first.

Main theorem `halts_iff`: from any state between candidates whose registers hold derivable codes,
the enumerator halts iff the falsity code 1 is derivable in `C222`. Soundness is the stack
invariant. Completeness compiles `C222` directly into command blocks, interpreting the generic
dominated-implication theorem in the predicate `fun n => ∃ p, Contract p n`. Source 159's
compiler sets the counter by `J u = MP u` from a cleared state; a dominated rho8 leaf
`rho8 a b c u` is `J u; AX(c; a - u, b)`. The compiled block follows `START_Y = AX(0; 1, Y)`,
whose candidate number is at least `Y`. No intermediate `CDom` derivation is constructed.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222

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

/-- The stack after AX: `tw` first, then GEN of the cache at `u`, then rho8 … rho1. -/
def axStack (a h b c u t w : Nat) : Nat :=
  P (rho1 a b) (P (rho2 a b c) (P (rho3 a b c) (P (rho4 a b c) (P (rho5 a b c)
    (P (rho6 a c) (P (growG a b c) (P (rho8 a b c u) (P (wal u h) (P t w)))))))))

def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle222 a b c

/-- The register-level effect of one command, without the proof-list pointer. -/
inductive Cmd where
  | nip
  | drop
  | mp (x : Nat)
  | ax (c x y : Nat)

/-- Working registers `(tw, ws, d, h)`. -/
structure W where
  tw : Nat
  ws : Nat
  d : Nat
  h : Nat

/-- One command on the working registers; `none` is the halting NIP. -/
def cstep : Cmd → W → Option W
  | .nip, ⟨t, s, d, h⟩ => if h = 1 then none else some ⟨t, (unP s).2, d, (unP s).1⟩
  | .drop, ⟨t, s, d, h⟩ => some ⟨h, P t s, d, h⟩
  | .mp x, ⟨t, s, d, h⟩ =>
      if wim t (d + x) = h then some ⟨d + x, P 0 s, d + x, 0⟩ else some ⟨0, s, d + x, 0⟩
  | .ax c x y, ⟨t, s, d, h⟩ =>
      some ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c d t s, 0, 0⟩

/-- Packing of a command in front of the rest pointer `r`. -/
def pack : Cmd → Nat → Nat
  | .nip, r => P 0 r
  | .drop, r => P 1 r
  | .mp x, r => P 2 (P x r)
  | .ax c x y, r => P (c + 3) (P y (P x r))

/-- The command packed at `z`, and the rest pointer. -/
def decode (z : Nat) : Cmd × Nat :=
  match (unP z).1 with
  | 0 => (.nip, (unP z).2)
  | 1 => (.drop, (unP z).2)
  | 2 => (.mp (unP (unP z).2).1, (unP (unP z).2).2)
  | c + 3 => (.ax c (unP (unP (unP z).2).2).1 (unP (unP z).2).1, (unP (unP (unP z).2).2).2)

theorem decode_pack (c : Cmd) (r : Nat) : decode (pack c r) = (c, r) := by
  cases c <;> simp [decode, pack, unP_P']

theorem unP_le (z : Nat) : (unP z).1 ≤ z ∧ (unP z).2 ≤ z := ofNat_le z

theorem decode_le (z : Nat) : (decode z).2 ≤ z := by
  have h1 := unP_le z
  have h2 := unP_le (unP z).2
  have h3 := unP_le (unP (unP z).2).2
  unfold decode; split <;> simp only <;> omega

/-- Encoding of a nonempty command list as a candidate number. -/
def encL : Cmd → List Cmd → Nat
  | c, [] => pack c 0
  | c, c' :: cs => pack c (encL c' cs + 1)

def toW (s : St) : W := ⟨s.tw, s.ws, s.d, s.h⟩

/-- The proof-list fetch: a new candidate when the list is exhausted. -/
def fetch (s : St) : Nat × Nat := if s.pl = 0 then (s.np, s.np + 1) else (s.pl - 1, s.np)

/-- Execute the command packed at `pl1`, with the next candidate `np1`. -/
def execAt (pl1 np1 : Nat) (s : St) : Option St :=
  (cstep (decode pl1).1 (toW s)).map fun w => ⟨(decode pl1).2, np1, w.tw, w.ws, w.d, w.h⟩

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

theorem good_zero : Good 0 := fun k => by rw [tailN_zero k]; exact C222.truth

theorem good_cons {x z : Nat} (hx : C222 x) (hz : Good z) : Good (P x z) := by
  intro k
  cases k with
  | zero => simpa [tailN, unP_P'] using hx
  | succ k => simpa [tailN, unP_P'] using hz k

/-- The current formula, the cache and every stack entry are derivable. -/
def Inv (w : W) : Prop := C222 w.tw ∧ C222 w.h ∧ Good w.ws

theorem gate_good (a b c : Nat) : C222 (gate a b c) := by
  unfold gate
  split
  · exact C222.truth
  · rename_i h
    exact C222.bundle a b c (fun e => h (Or.inl e)) (fun e => h (Or.inr e))

theorem axStack_good (a h b c u t w : Nat) (hh : C222 h) (ht : C222 t) (hw : Good w) :
    Good (axStack a h b c u t w) :=
  good_cons (C222.r1 a b) <| good_cons (C222.r2 a b c) <| good_cons (C222.r3 a b c) <|
    good_cons (C222.r4 a b c) <| good_cons (C222.r5 a b c) <| good_cons (C222.r6 a c) <|
    good_cons (C222.rG a b c) <| good_cons (C222.r8 a b c u) <| good_cons (C222.gen u hh) <|
    good_cons ht hw

theorem cstep_inv : ∀ (c : Cmd) {w w' : W}, Inv w → cstep c w = some w' → Inv w'
  | .nip, ⟨_, _, _, h⟩, _, ⟨ht, _, hw⟩, e => by
      simp only [cstep] at e
      split at e
      · cases e
      · cases e; exact ⟨ht, hw 0, fun k => hw (k + 1)⟩
  | .drop, ⟨_, _, _, _⟩, _, ⟨ht, hh, hw⟩, e => by cases e; exact ⟨hh, hh, good_cons ht hw⟩
  | .mp _, ⟨_, _, _, _⟩, _, ⟨ht, hh, hw⟩, e => by
      simp only [cstep] at e
      split at e
      · rename_i heq
        cases e; exact ⟨C222.mp ht (heq ▸ hh), C222.truth, good_cons C222.truth hw⟩
      · cases e; exact ⟨C222.truth, C222.truth, hw⟩
  | .ax .., ⟨_, _, _, _⟩, _, ⟨ht, hh, hw⟩, e => by
      cases e; exact ⟨gate_good _ _ _, C222.truth, axStack_good _ _ _ _ _ _ _ hh ht hw⟩

/-- Only NIP halts, and only on the cached falsity code. -/
theorem cstep_none : ∀ (c : Cmd) {w : W}, cstep c w = none → w.h = 1
  | .nip, ⟨_, _, _, h⟩, e => by
      simp only [cstep] at e
      split at e
      · assumption
      · cases e
  | .drop, ⟨_, _, _, _⟩, e | .ax .., ⟨_, _, _, _⟩, e => by cases e
  | .mp _, ⟨_, _, _, _⟩, e => by simp only [cstep] at e; split at e <;> cases e

/-- One decoded command either preserves the invariant or halts with derivable falsity. -/
theorem step_sound {s : St} (hs : Inv (toW s)) :
    match enumStep s with
    | some s' => Inv (toW s')
    | none => C222 F := by
  cases h : enumStep s with
  | none =>
      simp only [enumStep, execAt, Option.map_eq_none_iff] at h
      have hh := hs.2.1
      rwa [cstep_none _ h] at hh
  | some s' =>
      simp only [enumStep, execAt, Option.map_eq_some_iff] at h
      obtain ⟨w, hw, rfl⟩ := h
      exact cstep_inv _ hs hw

theorem run_inv : ∀ (n : Nat) {s s' : St}, Inv (toW s) → run n s = some s' → Inv (toW s')
  | 0, s, s', hs, h => by cases h; exact hs
  | n + 1, s, s', hs, h => by
      unfold run at h
      split at h
      · rename_i s1 h1
        exact run_inv n (by simpa only [h1] using step_sound hs) h
      · cases h

/-- Soundness: halting yields a derivation of code 1. -/
theorem sound {s : St} (hs : Inv (toW s)) : HaltsFrom s → C222 F := by
  rintro ⟨n, s', hrun, hstep⟩
  simpa only [hstep] using step_sound (run_inv n hs hrun)

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

theorem cexec_cons_some {c : Cmd} {cs : List Cmd} {w w' : W} (h : cstep c w = some w') :
    cexec (c :: cs) w = cexec cs w' := by
  simp only [cexec, h]

theorem execAt_pack (c : Cmd) (r np1 : Nat) (s : St) :
    execAt (pack c r) np1 s = (cstep c (toW s)).map fun w => ⟨r, np1, w.tw, w.ws, w.d, w.h⟩ := by
  simp only [execAt, decode_pack]

theorem run_succ (n : Nat) (s s1 : St) (h : enumStep s = some s1) : run (n + 1) s = run n s1 := by
  simp only [run, h]

/-- If a candidate's command list halts, the enumerator halts from its start. -/
theorem exec_list (cs : List Cmd) : ∀ (c : Cmd) (s : St), (fetch s).1 = encL c cs →
    cexec (c :: cs) (toW s) = none → HaltsFrom s := by
  induction cs with
  | nil =>
      intro c s hf hx
      cases hw : cstep c (toW s) with
      | none => exact ⟨0, s, rfl, by simp [enumStep, hf, encL, execAt_pack, hw]⟩
      | some w => rw [cexec_cons_some hw] at hx; cases hx
  | cons c' cs' ih =>
      intro c s hf hx
      cases hw : cstep c (toW s) with
      | none => exact ⟨0, s, rfl, by simp [enumStep, hf, encL, execAt_pack, hw]⟩
      | some w =>
        let s1 : St := ⟨encL c' cs' + 1, (fetch s).2, w.tw, w.ws, w.d, w.h⟩
        have hstep : enumStep s = some s1 := by simp [enumStep, hf, encL, execAt_pack, hw, s1]
        obtain ⟨n, s', hr, hs'⟩ := ih c' s1 (by simp [fetch, s1]) (by rwa [cexec_cons_some hw] at hx)
        exact ⟨n + 1, s', by rwa [run_succ n s s1 hstep], hs'⟩

/-! ### Every later candidate is reached -/

theorem run_add : ∀ (n m : Nat) (s s1 : St), run n s = some s1 → run (n + m) s = run m s1
  | 0, m, s, s1, h => by
      simp only [run] at h; cases h; simp
  | n + 1, m, s, s1, h => by
      simp only [run] at h
      split at h
      · rename_i s2 h2
        rw [show n + 1 + m = (n + m) + 1 by omega]
        simp only [run, h2]
        exact run_add n m s2 s1 h
      · cases h

theorem step_eq {s s1 : St} (h : enumStep s = some s1) :
    s1.pl = (decode (fetch s).1).2 ∧ s1.np = (fetch s).2 := by
  simp only [enumStep, execAt, Option.map_eq_some_iff] at h
  obtain ⟨w, -, rfl⟩ := h
  exact ⟨rfl, rfl⟩

/-- A candidate in progress finishes or the enumerator halts. -/
theorem drain : ∀ (m : Nat) (s : St), s.pl ≤ m →
    (∃ n s', run n s = some s' ∧ s'.pl = 0 ∧ s'.np = s.np) ∨ HaltsFrom s
  | m, s, hm => by
      by_cases hpl : s.pl = 0
      · exact Or.inl ⟨0, s, rfl, hpl, rfl⟩
      · match hs : enumStep s with
        | none => exact Or.inr ⟨0, s, rfl, hs⟩
        | some s1 =>
          obtain ⟨h1, h2⟩ := step_eq hs
          have := decode_le (fetch s).1
          simp only [fetch, hpl, if_false] at h1 h2 this
          cases m with
          | zero => omega
          | succ m =>
            rcases drain m s1 (by omega) with ⟨n, s', hr, h3, h4⟩ | ⟨n, s', hr, h3⟩
            · exact Or.inl ⟨n + 1, s', by rwa [run_succ n s s1 hs], h3, h4.trans h2⟩
            · exact Or.inr ⟨n + 1, s', by rwa [run_succ n s s1 hs], h3⟩

theorem reach (sd : St) (hpl : sd.pl = 0) : ∀ k : Nat,
    (∃ n s, run n sd = some s ∧ s.pl = 0 ∧ s.np = sd.np + k) ∨ HaltsFrom sd
  | 0 => Or.inl ⟨0, sd, rfl, hpl, rfl⟩
  | k + 1 => by
      rcases reach sd hpl k with ⟨n, s, hr, hpl', hnp⟩ | hh
      · match hs : enumStep s with
        | none => exact Or.inr ⟨n, s, hr, hs⟩
        | some s1 =>
          have hnp1 : s1.np = sd.np + (k + 1) := by
            rw [(step_eq hs).2]; simp only [fetch, hpl', if_true]; omega
          have hr1 : run (n + 1) sd = some s1 := by
            rw [run_add n 1 sd s hr]; simp only [run, hs]
          rcases drain s1.pl s1 (Nat.le_refl _) with ⟨j, s', hr', h1, h2⟩ | ⟨j, s', hr', h1⟩
          · exact Or.inl ⟨n + 1 + j, s', by rwa [run_add (n + 1) j sd s1 hr1], h1, h2.trans hnp1⟩
          · exact Or.inr ⟨n + 1 + j, s', by rwa [run_add (n + 1) j sd s1 hr1], h1⟩
      · exact Or.inr hh

/-! ### Block contracts, by symbolic execution -/

def nips : Nat → List Cmd
  | 0 => []
  | k + 1 => .nip :: nips k

theorem ex_nil (w : W) : cexec [] w = some w := rfl

theorem ex_nip {t x S d h : Nat} {cs : List Cmd} (hh : h ≠ 1) :
    cexec (.nip :: cs) ⟨t, P x S, d, h⟩ = cexec cs ⟨t, S, d, x⟩ := by
  simp [cexec, cstep, hh, unP_P']

theorem ex_nip1 {t S d : Nat} {cs : List Cmd} : cexec (.nip :: cs) ⟨t, S, d, 1⟩ = none := by
  simp [cexec, cstep]

/- `ex_drop` and `ex_ax` hold by `rfl`, but are stated through `cexec_cons_some`: as `rfl`
lemmas, simp would leave the kernel to check `cexec (c :: cs) w ≡ cexec cs w'` by unfolding
`cexec` on both sides, evaluating the pops of closed pairing numerals. -/
theorem ex_drop {t S d h : Nat} {cs : List Cmd} :
    cexec (.drop :: cs) ⟨t, S, d, h⟩ = cexec cs ⟨h, P t S, d, h⟩ := cexec_cons_some rfl

theorem ex_ax {c x y t S d h : Nat} {cs : List Cmd} :
    cexec (.ax c x y :: cs) ⟨t, S, d, h⟩ =
      cexec cs ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c d t S, 0, 0⟩ :=
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

def discard : List Cmd := [.mp 1, .ax 1 0 0] ++ nips 10

theorem cexec_discard (T S : Nat) : cexec discard ⟨T, S, 0, 0⟩ = some ⟨0, S, 0, 0⟩ := by
  have hw : wim T (0 + 1) ≠ 0 := by
    simp only [wim, Nat.zero_add]
    have := le_P_right T 1
    omega
  rw [discard, List.cons_append, ex_mp_fail hw]
  xrun

/-- Setting the counter from a cleared state: `J u = MP u`, nothing for `u = 0`. -/
def J (u : Nat) : List Cmd := if u = 0 then [] else [.mp u]

theorem cexec_J (u S : Nat) (rest : List Cmd) :
    cexec (J u ++ rest) ⟨0, S, 0, 0⟩ = cexec rest ⟨0, S, u, 0⟩ := by
  unfold J
  split
  · rename_i hu; subst hu; rfl
  · rename_i hu
    have hw : wim 0 (0 + u) ≠ 0 := by
      intro h
      obtain ⟨_, h2⟩ := P_eq_zero (show P 0 u = 0 by simp only [wim, Nat.zero_add] at h; omega)
      exact hu h2
    rw [List.singleton_append, ex_mp_fail hw, Nat.zero_add]

/-- After `discard` and `J u`, `AX(c; a - u, b)` with `u ≤ a` pushes the rows at `(a, b, c, u)`. -/
theorem cexec_discard_ax (T S a b c u : Nat) (hu : u ≤ a) (rest : List Cmd) :
    cexec (discard ++ (J u ++ (.ax c (a - u) b :: rest))) ⟨T, S, 0, 0⟩ =
      cexec rest ⟨gate a b c, axStack a 0 b c u 0 S, 0, 0⟩ := by
  rw [cexec_append, cexec_discard]
  simp only
  rw [cexec_J, ex_ax]
  simp only [Nat.zero_add, show u + (a - u) = a by omega]

/-- The leaf for the AX row at position `j`: pop to it, keep it, pop the rest. -/
def leaf (j a b c u : Nat) : List Cmd :=
  discard ++ (J u ++ (.ax c (a - u) b :: (nips j ++ (.drop :: nips (11 - j)))))

/-- The bundle leaf. -/
def bundleLeaf (a b c : Nat) : List Cmd := discard ++ (J 0 ++ (.ax c (a - 0) b :: nips 10))

/-- Generalization of a block's result: `B_X; DROP; J i; NIP; AX(i; 0, 0); NIP^9; DROP; NIP; NIP`. -/
def genBlock (i : Nat) (p : List Cmd) : List Cmd :=
  p ++ (.drop :: (J i ++ (.nip :: .ax i 0 0 :: (nips 9 ++ [.drop, .nip, .nip]))))

theorem gen_contract (i : Nat) {p : List Cmd} {H : Nat} (hp : Contract p H) :
    Contract (genBlock i p) (wal i H) := by
  intro T S
  rcases hp T S with hn | hs
  · left; rw [genBlock, cexec_append, hn]
  · right
    rw [genBlock, cexec_append, hs]
    simp only [ex_drop]
    rw [cexec_J]
    xrun

/-- Modus ponens on two blocks. -/
def mpBlock (B : Nat) (pa pab : List Cmd) : List Cmd :=
  pa ++ (.drop :: (pab ++ (.nip :: .drop :: .nip :: .mp B :: .ax B 0 0 ::
    (nips 10 ++ [.drop, .nip, .nip]))))

theorem mp_contract {A B : Nat} {pa pab : List Cmd} (ha : Contract pa A)
    (hab : Contract pab (wim A B)) : Contract (mpBlock B pa pab) B := by
  intro T S
  rcases ha T S with hn | hs
  · left; rw [mpBlock, cexec_append, hn]
  · rw [mpBlock, cexec_append, hs]
    simp only [ex_drop]
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

/-- Compile directly in the algebra of block contracts. The restricted rho8 theorem is
interpreted here in `fun n => ∃ p, Contract p n`, eliminating the intermediate calculus. -/
theorem build_c222 : ∀ {n : Nat}, C222 n → ∃ p : List Cmd, Contract p n := by
  have hmp {A B : Nat} (hab : ∃ p : List Cmd, Contract p (wim A B))
      (ha : ∃ p : List Cmd, Contract p A) : ∃ p : List Cmd, Contract p B :=
    hab.elim fun _ hab => ha.elim fun _ ha => ⟨_, mp_contract ha hab⟩
  have hrow (a b c u : Nat) (hu : u ≤ a) : ∃ p : List Cmd, Contract p (rho8 a b c u) :=
    ⟨leaf 8 a b c u, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ hu]; xrun)⟩
  intro n h
  induction h with
  | truth => exact ⟨discard, fun T S => Or.inr (cexec_discard T S)⟩
  | mp _ _ ih1 ih2 => exact hmp ih2 ih1
  | gen a _ ih => exact ih.elim fun _ hp => ⟨_, gen_contract a hp⟩
  | bundle a b c h1 h2 =>
      refine ⟨bundleLeaf a b c, fun T S => Or.inr ?_⟩
      rw [bundleLeaf, cexec_discard_ax T S a b c 0 (Nat.zero_le a)]
      xrun
      simp [gate, h1, h2]
  | r1 a b => exact ⟨leaf 1 a b 0 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | r2 a b c => exact ⟨leaf 2 a b c 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | r3 a b c => exact ⟨leaf 3 a b c 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | r4 a b c => exact ⟨leaf 4 a b c 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | r5 a b c => exact ⟨leaf 5 a b c 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | r6 a b => exact ⟨leaf 6 a 0 b 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | rG a b c => exact ⟨leaf 7 a b c 0, fun T S => Or.inr (by rw [leaf, cexec_discard_ax _ _ _ _ _ _ (by omega)]; xrun)⟩
  | r8 a b c u =>
      exact DomRho8.rho8_all_of_restricted (T := fun n => ∃ p : List Cmd, Contract p n)
        hmp hrow a b c u

/-- `START_Y = AX(0; 1, Y)` resets the counter and cache from every state; with a block for 1
and `DROP; NIP; NIP`, the list halts from every state. -/
theorem program_none (Y : Nat) (p : List Cmd) (hp : Contract p F) :
    ∀ w, cexec (.ax 0 1 Y :: (p ++ [.drop, .nip, .nip])) w = none := by
  rintro ⟨t, S, d, h⟩
  rw [ex_ax, cexec_append]
  rcases hp (gate (d + 1) (h + Y) 0) (axStack (d + 1) h (h + Y) 0 d t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only [F]
    xrun

theorem encL_ge (Y : Nat) (cs : List Cmd) : Y ≤ encL (.ax 0 1 Y) cs := by
  have key : ∀ r, Y ≤ pack (.ax 0 1 Y) r := fun r =>
    Nat.le_trans (le_P_left Y (P 1 r)) (le_P_right (0 + 3) (P Y (P 1 r)))
  cases cs <;> exact key _

/-- Completeness: between candidates, a derivation of code 1 is eventually run. -/
theorem complete {sd : St} (hpl : sd.pl = 0) (h : C222 F) : HaltsFrom sd := by
  obtain ⟨p, hp⟩ := build_c222 h
  let cs := p ++ [.drop, .nip, .nip]
  have hN := encL_ge sd.np cs
  rcases reach sd hpl (encL (.ax 0 1 sd.np) cs - sd.np) with ⟨n, s, hr, hpl', hnp⟩ | hh
  · have hf : (fetch s).1 = encL (.ax 0 1 sd.np) cs := by simp only [fetch, hpl', if_true]; omega
    obtain ⟨k, s', hr', hs'⟩ := exec_list cs (.ax 0 1 sd.np) s hf (program_none sd.np p hp _)
    exact ⟨n + k, s', by rwa [run_add n k sd s hr], hs'⟩
  · exact hh

/-- L1: between candidates, with derivable registers, the enumerator halts iff code 1 is
derivable. -/
theorem halts_iff {s : St} (hpl : s.pl = 0) (hs : Inv (toW s)) : HaltsFrom s ↔ C222 F :=
  ⟨sound hs, complete hpl⟩

end SetTheory.BusyBeaver.ZFC.EnumPerm
