import BusyBeaver.ZFC.KCodeDom

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
invariant. Completeness compiles a derivation of the dominated calculus `KCodeDom.CDom` into
command blocks (Source 159's compiler: the counter is set by `J u = MP u` from a cleared state,
and a dominated rho8 leaf `rho8 a b c u` is `J u; AX(c; a - u, b)`) behind `START_Y = AX(0; 1, Y)`,
whose candidate number is at least `Y`; `CDom` derives every `C222` code.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumPerm

open SetTheory.BusyBeaver.ZFC.Code254 SetTheory.BusyBeaver.ZFC.KCode222
open SetTheory.BusyBeaver.ZFC.KCodeDom

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

theorem run_inv : ∀ (n : Nat) {s s' : St}, Inv (toW s) → run n s = some s' → Inv (toW s')
  | 0, s, s', hs, h => by cases h; exact hs
  | n + 1, s, s', hs, h => by
      unfold run at h
      split at h
      · rename_i s1 h1
        simp only [enumStep, execAt, Option.map_eq_some_iff] at h1
        obtain ⟨w, hw, rfl⟩ := h1
        exact run_inv n (cstep_inv _ hs hw) h
      · cases h

/-- Soundness: halting yields a derivation of code 1. -/
theorem sound {s : St} (hs : Inv (toW s)) : HaltsFrom s → C222 F := by
  rintro ⟨n, s', hrun, hstep⟩
  simp only [enumStep, execAt, Option.map_eq_none_iff] at hstep
  have := (run_inv n hs hrun).2.1
  rw [cstep_none _ hstep] at this
  exact this

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

theorem cexec_cons_none {c : Cmd} {cs : List Cmd} {w : W} (h : cstep c w = none) :
    cexec (c :: cs) w = none := by
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
        obtain ⟨n, s', hr, hs'⟩ := ih c' s1 (by simp [fetch, s1]) (by rw [cexec_cons_some hw] at hx; exact hx)
        exact ⟨n + 1, s', by rw [run_succ n s s1 hstep]; exact hr, hs'⟩

/-! ### Every later candidate is reached -/

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
            · exact Or.inl ⟨n + 1, s', by rw [run_succ n s s1 hs]; exact hr, h3, h4.trans h2⟩
            · exact Or.inr ⟨n + 1, s', by rw [run_succ n s s1 hs]; exact hr, h3⟩

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
          · left
            exact ⟨n + 1 + j, s', by rw [run_add (n + 1) j sd s1 hr1]; exact hr', h1, h2.trans hnp1⟩
          · right
            exact ⟨n + 1 + j, s', by rw [run_add (n + 1) j sd s1 hr1]; exact hr', h1⟩
      · exact Or.inr hh

/-! ### Block contracts -/

def pushL : List Nat → Nat → Nat
  | [], S => S
  | x :: L, S => P x (pushL L S)

def nips : Nat → List Cmd
  | 0 => []
  | k + 1 => .nip :: nips k

theorem cexec_nips_cons (k : Nat) (t x S d h : Nat) :
    cexec (nips (k + 1)) ⟨t, P x S, d, h⟩ =
      if h = 1 then none else cexec (nips k) ⟨t, S, d, x⟩ := by
  simp only [nips, cexec, cstep, unP_P']
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
  [rho1 a b, rho2 a b c, rho3 a b c, rho4 a b c, rho5 a b c, rho6 a c, growG a b c,
   rho8 a b c u, wal u h]

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

def discard : List Cmd := [.mp 1, .ax 1 0 0] ++ nips 10

theorem cstep_mp_fail (x T S d h : Nat) (hw : wim T (d + x) ≠ h) :
    cstep (.mp x) ⟨T, S, d, h⟩ = some ⟨0, S, d + x, 0⟩ := by
  simp [cstep, hw]

theorem cstep_ax (c x y t S d h : Nat) :
    cstep (.ax c x y) ⟨t, S, d, h⟩ =
      some ⟨gate (d + x) (h + y) c, axStack (d + x) h (h + y) c d t S, 0, 0⟩ := rfl

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
  rw [show gate (0 + 1 + 0) (0 + 0) 1 = 0 from gate_self _ _, axStack_eq]
  exact cexec_nips 0 S 0 (axList (0 + 1 + 0) 0 (0 + 0) 1 (0 + 1)) 0 0 (by omega)
    (axList_ne_one _ _ _ _ _)

theorem cstep_nip (t S d h : Nat) (hh : h ≠ 1) :
    cstep .nip ⟨t, S, d, h⟩ = some ⟨t, (unP S).2, d, (unP S).1⟩ := by
  simp [cstep, hh]

theorem cstep_nip_one (t S d : Nat) : cstep .nip ⟨t, S, d, 1⟩ = none := by
  simp [cstep]

theorem cstep_drop (t S d h : Nat) : cstep .drop ⟨t, S, d, h⟩ = some ⟨h, P t S, d, h⟩ :=
  rfl

theorem cstep_mp_ok (x T S d h : Nat) (hw : wim T (d + x) = h) :
    cstep (.mp x) ⟨T, S, d, h⟩ = some ⟨d + x, P 0 S, d + x, 0⟩ := by
  simp [cstep, hw]

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
    simp only [List.cons_append, List.nil_append]
    rw [cexec_cons_some (cstep_mp_fail u 0 S 0 0 hw), Nat.zero_add]

theorem pushL_append (L1 L2 : List Nat) (S : Nat) : pushL (L1 ++ L2) S = pushL L1 (pushL L2 S) := by
  induction L1 with
  | nil => rfl
  | cons x L ih => simp only [List.cons_append, pushL, ih]

/-- Pop down to a selected entry, make it current, and pop the rest. -/
theorem select_entry (L1 : List Nat) (x : Nat) (L2 : List Nat) (last g h0 S : Nat)
    (hh : h0 ≠ 1) (hg : g ≠ 1) (hx : x ≠ 1) (h1 : ∀ y, y ∈ L1 → y ≠ 1)
    (h2 : ∀ y, y ∈ L2 → y ≠ 1) :
    cexec (nips (L1.length + 1) ++ (.drop :: nips (L2.length + 2)))
      ⟨g, pushL (L1 ++ x :: (L2 ++ [last])) S, 0, h0⟩ = some ⟨x, S, 0, last⟩ := by
  have hs : pushL (L1 ++ x :: (L2 ++ [last])) S = pushL (L1 ++ [x]) (pushL (L2 ++ [last]) S) := by
    rw [← pushL_append]; simp
  rw [hs, cexec_append, cexec_nips g _ 0 L1 h0 x hh h1]
  simp only
  rw [cexec_cons_some (cstep_drop g _ 0 x)]
  have := cexec_nips x S 0 (g :: L2) x last hx (fun y hy => by
    cases List.mem_cons.mp hy with
    | inl e => rw [e]; exact hg
    | inr hy => exact h2 y hy)
  rw [show L2.length + 2 = (g :: L2).length + 1 by simp]
  simpa [pushL] using this

/-- After `discard` and `J u`, `AX(c; a - u, b)` with `u ≤ a` pushes the rows at `(a, b, c, u)`. -/
theorem cexec_discard_ax (T S a b c u : Nat) (hu : u ≤ a) (rest : List Cmd) :
    cexec (discard ++ (J u ++ (.ax c (a - u) b :: rest))) ⟨T, S, 0, 0⟩ =
      cexec rest ⟨gate a b c, pushL (axList a 0 b c u ++ [0]) S, 0, 0⟩ := by
  rw [cexec_append, cexec_discard]
  simp only
  rw [cexec_J, cexec_cons_some (cstep_ax c (a - u) b 0 S u 0)]
  simp only [Nat.zero_add, show u + (a - u) = a by omega]
  rfl

/-- The leaf block for the AX row at position `j`. -/
def leaf (j a b c u : Nat) : List Cmd :=
  discard ++ (J u ++ (.ax c (a - u) b :: (nips j ++ (.drop :: nips (11 - j)))))

theorem leaf_contract (j a b c u x : Nat) (L1 L2 : List Nat) (hu : u ≤ a)
    (hsplit : axList a 0 b c u = L1 ++ x :: L2)
    (hj : L1.length + 1 = j) (hk : L2.length + 2 = 11 - j) : Contract (leaf j a b c u) x := by
  intro T S
  right
  have hx : x ≠ 1 := axList_ne_one a 0 b c u x (by rw [hsplit]; simp)
  have h1 : ∀ y, y ∈ L1 → y ≠ 1 := fun y hy => axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  have h2 : ∀ y, y ∈ L2 → y ≠ 1 := fun y hy => axList_ne_one a 0 b c u y (by rw [hsplit]; simp [hy])
  rw [leaf, cexec_discard_ax T S a b c u hu, hsplit, ← hk, ← hj]
  have := select_entry L1 x L2 0 (gate a b c) 0 S (by omega) (gate_ne_one a b c) hx h1 h2
  simpa [List.append_assoc] using this

/-- The bundle leaf. -/
def bundleLeaf (a b c : Nat) : List Cmd := discard ++ (J 0 ++ (.ax c (a - 0) b :: nips 10))

theorem bundle_contract (a b c : Nat) (h1 : c ≠ a) (h2 : c ≠ b) :
    Contract (bundleLeaf a b c) (bundle222 a b c) := by
  intro T S
  right
  rw [bundleLeaf, cexec_discard_ax T S a b c 0 (Nat.zero_le a)]
  have hg : gate a b c = bundle222 a b c := by
    simp [gate, h1, h2]
  rw [hg, show nips 10 = nips ((axList a 0 b c 0).length + 1) from rfl]
  exact cexec_nips (bundle222 a b c) S 0 (axList a 0 b c 0) 0 0 (by omega) (axList_ne_one _ _ _ _ _)

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
    simp only
    rw [cexec_cons_some (cstep_drop H S 0 0), cexec_J,
      cexec_cons_some (cstep_nip 0 (P H S) i 0 (by omega))]
    simp only [unP_P']
    rw [cexec_cons_some (cstep_ax i 0 0 0 S i H)]
    simp only [Nat.add_zero]
    rw [show gate i H i = 0 from gate_self i H, axStack_eq]
    exact select_entry
      [rho1 i H, rho2 i H i, rho3 i H i, rho4 i H i, rho5 i H i, rho6 i i,
        growG i H i, rho8 i H i i] (wal i H) [] 0 0 0 S
      (by omega) (by omega) (wal_ne_one i H)
      (fun y hy => axList_ne_one i H H i i y (by simp [axList] at hy ⊢; omega))
      (by simp)

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
    simp only
    rw [cexec_cons_some (cstep_drop A S 0 0)]
    rcases hab 0 (P A S) with hn2 | hs2
    · left; rw [cexec_append, hn2]
    · rw [cexec_append, hs2]
      simp only
      rw [cexec_cons_some (cstep_nip (wim A B) (P A S) 0 0 (by omega))]
      simp only [unP_P']
      rw [cexec_cons_some (cstep_drop (wim A B) S 0 A)]
      by_cases hA : A = 1
      · left
        rw [hA, cexec_cons_none (cstep_nip_one 1 (P (wim 1 B) S) 0)]
      · rw [cexec_cons_some (cstep_nip A (P (wim A B) S) 0 A hA)]
        simp only [unP_P']
        rw [cexec_cons_some (cstep_mp_ok B A S 0 (wim A B) (by simp))]
        simp only [Nat.zero_add]
        rw [cexec_cons_some (cstep_ax B 0 0 B (P 0 S) B 0)]
        simp only [Nat.add_zero]
        rw [show gate B 0 B = 0 from gate_self B 0, axStack_eq,
          show nips 10 = nips ((axList B 0 0 B B).length + 1) from rfl, cexec_append,
          cexec_nips 0 (P 0 S) 0 (axList B 0 0 B B) 0 B (by omega) (axList_ne_one _ _ _ _ _)]
        simp only
        rw [cexec_cons_some (cstep_drop 0 (P 0 S) 0 B)]
        by_cases hB : B = 1
        · left
          rw [hB, cexec_cons_none (cstep_nip_one 1 (P 0 (P 0 S)) 0)]
        · right
          rw [cexec_cons_some (cstep_nip B (P 0 (P 0 S)) 0 B hB)]
          simp only [unP_P']
          rw [cexec_cons_some (cstep_nip B (P 0 S) 0 0 (by omega))]
          simp [unP_P', cexec]

/-- Every code of the dominated calculus has a block computing it. -/
theorem build : ∀ {n : Nat}, CDom n → ∃ p : List Cmd, Contract p n := by
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
  | r1 a b => exact ⟨_, leaf_contract 1 a b 0 0 _ [] _ (Nat.zero_le a) rfl rfl rfl⟩
  | r2 a b c => exact ⟨_, leaf_contract 2 a b c 0 _ [_] _ (Nat.zero_le a) rfl rfl rfl⟩
  | r3 a b c => exact ⟨_, leaf_contract 3 a b c 0 _ [_, _] _ (Nat.zero_le a) rfl rfl rfl⟩
  | r4 a b c => exact ⟨_, leaf_contract 4 a b c 0 _ [_, _, _] _ (Nat.zero_le a) rfl rfl rfl⟩
  | r5 a b c => exact ⟨_, leaf_contract 5 a b c 0 _ [_, _, _, _] _ (Nat.zero_le a) rfl rfl rfl⟩
  | r6 a b => exact ⟨_, leaf_contract 6 a 0 b 0 _ [_, _, _, _, _] _ (Nat.zero_le a) rfl rfl rfl⟩
  | rG a b c => exact ⟨_, leaf_contract 7 a b c 0 _ [_, _, _, _, _, _] _ (Nat.zero_le a) rfl rfl rfl⟩
  | r8 a b c u hu => exact ⟨_, leaf_contract 8 a b c u _ [_, _, _, _, _, _, _] _ hu rfl rfl rfl⟩
  | bundle a b c h1 h2 => exact ⟨_, bundle_contract a b c h1 h2⟩

/-- `START_Y = AX(0; 1, Y)` resets the counter and cache from every state; with a block for 1
and `DROP; NIP; NIP`, the list halts from every state. -/
theorem program_none (Y : Nat) (p : List Cmd) (hp : Contract p F) :
    ∀ w, cexec (.ax 0 1 Y :: (p ++ [.drop, .nip, .nip])) w = none := by
  intro w
  obtain ⟨t, S, d, hh⟩ := w
  rw [cexec_cons_some (cstep_ax 0 1 Y t S d hh), cexec_append]
  rcases hp (gate (d + 1) (hh + Y) 0) (axStack (d + 1) hh (hh + Y) 0 d t S) with hn | hs
  · rw [hn]
  · rw [hs]
    simp only
    rw [cexec_cons_some (cstep_drop F _ 0 0)]
    rw [cexec_cons_some (cstep_nip 0 _ 0 0 (by omega))]
    simp only [unP_P']
    exact cexec_cons_none (cstep_nip_one 0 _ 0)

theorem encL_ge (Y : Nat) (cs : List Cmd) : Y ≤ encL (.ax 0 1 Y) cs := by
  have key : ∀ r, Y ≤ pack (.ax 0 1 Y) r := fun r =>
    Nat.le_trans (le_P_left Y (P 1 r)) (le_P_right (0 + 3) (P Y (P 1 r)))
  cases cs <;> exact key _

/-- Completeness: between candidates, a derivation of code 1 is eventually run. -/
theorem complete {sd : St} (hpl : sd.pl = 0) (h : C222 F) : HaltsFrom sd := by
  obtain ⟨p, hp⟩ := build (cdom_of_c222 h)
  let cs := p ++ [.drop, .nip, .nip]
  have hN := encL_ge sd.np cs
  rcases reach sd hpl (encL (.ax 0 1 sd.np) cs - sd.np) with ⟨n, s, hr, hpl', hnp⟩ | hh
  · have hf : (fetch s).1 = encL (.ax 0 1 sd.np) cs := by simp only [fetch, hpl', if_true]; omega
    obtain ⟨k, s', hr', hs'⟩ := exec_list cs (.ax 0 1 sd.np) s hf (program_none sd.np p hp _)
    exact ⟨n + k, s', by rw [run_add n k sd s hr]; exact hr', hs'⟩
  · exact hh

/-- L1: between candidates, with derivable registers, the enumerator halts iff code 1 is
derivable. -/
theorem halts_iff {s : St} (hpl : s.pl = 0) (hs : Inv (toW s)) : HaltsFrom s ↔ C222 F :=
  ⟨sound hs, complete hpl⟩

end SetTheory.BusyBeaver.ZFC.EnumPerm
