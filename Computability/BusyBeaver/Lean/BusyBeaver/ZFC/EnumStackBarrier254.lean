import BusyBeaver.ZFC.EnumSafeStart254

/-!
Actual command-code foundations for the dirty-stack barrier of intake155,
source42, “A252-state ZFC consistency machine and a smaller finite kernel”.
Arrival fab89c5d26b81cd2ccab2ee5d213ff23725c7726; report input
61e77836565f63582561f54745f633d50efd9c7d. The marked-occurrence argument is
attributed to that report and its standalone CantorOccurrenceOrder module.
The original calculus/enumerator is attributed to Mira-Cult, Jeff Ketchersid
and Andrew James Wade through Enum254's pinned source lineage.

All encodings and command effects below use Enum254 itself. This module
does not yet prove that the earlier marked occurrences supply a counting
invariant along every actual run. In particular it does not assert soundness
of an arbitrary dirty stack, a new binary endpoint, or internal PA provability.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumStackBarrier254

open Code254 Enum254

attribute [local irreducible] Code254.P

theorem P_eq_iff (a b c d : Nat) : P a b = P c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    have hh := congrArg unP h
    simpa only [unP_P', Prod.mk.injEq] using hh
  · rintro ⟨rfl, rfl⟩; rfl

private theorem tri_strict {m n : Nat} (h : m < n) : Cantor.tri m < Cantor.tri n := by
  have hm := Cantor.tri_mono (Nat.succ_le_of_lt h)
  simp only [Cantor.tri] at hm
  omega

theorem P_left_strict (y : Nat) {a b : Nat} (h : a < b) : P a y < P b y := by
  have ht := tri_strict (show a + y < b + y by omega)
  simp only [P, Cantor.toNat]
  omega

theorem P_right_strict (x : Nat) {a b : Nat} (h : a < b) : P x a < P x b := by
  have ht := tri_strict (show x + a < x + b by omega)
  simp only [P, Cantor.toNat]
  omega

theorem pack_strict (c : Cmd) {r s : Nat} (h : r < s) : pack c r < pack c s := by
  cases c with
  | mp x => exact P_right_strict 0 (P_right_strict x h)
  | drop x => exact P_right_strict 1 (P_right_strict x h)
  | nip x => exact P_right_strict 2 (P_right_strict x h)
  | ax c x y u =>
      exact P_right_strict (c + 3)
        (P_right_strict x (P_right_strict y (P_right_strict u h)))

theorem pack_injective {c d : Cmd} {r s : Nat} (h : pack c r = pack d s) :
    c = d ∧ r = s := by
  cases c <;> cases d <;> simp_all [pack, P_eq_iff]

/-- Decode exactly one actual command and its raw rest pointer. -/
def unpack (z : Nat) : Cmd × Nat :=
  let op := (unP z).1
  let p := (unP z).2
  let x := (unP p).1
  let r := (unP p).2
  match op with
  | 0 => (.mp x, r)
  | 1 => (.drop x, r)
  | 2 => (.nip x, r)
  | c + 3 => (.ax c x (unP r).1 (unP (unP r).2).1, (unP (unP r).2).2)

theorem unpack_pack (c : Cmd) (r : Nat) : unpack (pack c r) = (c, r) := by
  cases c <;> simp [unpack, pack, unP_P']

private theorem P_unP (z : Nat) : P (unP z).1 (unP z).2 = z := by
  simpa only [P, unP] using Cantor.toNat_ofNat z

theorem pack_unpack (z : Nat) : pack (unpack z).1 (unpack z).2 = z := by
  have h0 := P_unP z
  have h1 := P_unP (unP z).2
  have h2 := P_unP (unP (unP z).2).2
  have h3 := P_unP (unP (unP (unP z).2).2).2
  unfold unpack
  dsimp only
  split <;> simp only [pack]
  all_goals simp_all only

theorem unpack_rest_le (z : Nat) : (unpack z).2 ≤ z := by
  have h0 := unP_le z
  have h1 := unP_le (unP z).2
  have h2 := unP_le (unP (unP z).2).2
  have h3 := unP_le (unP (unP (unP z).2).2).2
  unfold unpack
  dsimp only
  split <;> simp only <;> omega

/-- Every candidate number is a finite nonempty actual command list.
The returned pair is its first command and remaining list. -/
def decode (z : Nat) : Cmd × List Cmd :=
  if (unpack z).2 = 0 then ((unpack z).1, [])
  else
    let p := decode ((unpack z).2 - 1)
    ((unpack z).1, p.1 :: p.2)
termination_by z
decreasing_by
  have := unpack_rest_le z
  omega

theorem encL_decode (z : Nat) : encL (decode z).1 (decode z).2 = z := by
  induction z using Nat.strongRecOn with
  | ind z ih =>
      rw [decode]
      split
      · rename_i hz
        simpa only [encL, ← hz] using pack_unpack z
      · rename_i hz
        simp only [encL]
        have hl : (unpack z).2 - 1 < z := by have := unpack_rest_le z; omega
        rw [ih _ hl]
        have hr : (unpack z).2 - 1 + 1 = (unpack z).2 := by omega
        rw [hr]
        exact pack_unpack z

theorem encL_injective (c : Cmd) (cs : List Cmd) (d : Cmd) (ds : List Cmd)
    (h : encL c cs = encL d ds) : c = d ∧ cs = ds := by
  induction cs generalizing c d ds with
  | nil =>
      cases ds with
      | nil => exact ⟨(pack_injective h).1, rfl⟩
      | cons d' ds => have := (pack_injective h).2; omega
  | cons c' cs ih =>
      cases ds with
      | nil => have := (pack_injective h).2; omega
      | cons d' ds =>
          obtain ⟨hcd, htail⟩ := pack_injective h
          have ht : encL c' cs = encL d' ds := by omega
          obtain ⟨hhead, hrest⟩ := ih c' d' ds ht
          exact ⟨hcd, by rw [hhead, hrest]⟩

theorem decode_encL (c : Cmd) (cs : List Cmd) : decode (encL c cs) = (c, cs) := by
  have h := encL_injective _ _ c cs (encL_decode (encL c cs))
  exact Prod.ext h.1 h.2

/-- This genuine candidate is intentionally not an empty-list code. -/
theorem decode_zero : decode 0 = (.mp 0, []) := by
  have h : encL (.mp 0) [] = 0 := by simp [encL, pack, P, Cantor.toNat, Cantor.tri]
  simpa only [h] using decode_encL (.mp 0) []

/-- One actual execAt step is exactly execution of its decoded command. -/
theorem execAt_unpack (z np : Nat) (s : St) :
    execAt z np s =
      match cstep (unpack z).1 (toW s) with
      | none => none
      | some w => some ⟨(unpack z).2, np, w.tw, w.ws, w.d, w.h⟩ := by
  have h := execAt_pack (unpack z).1 (unpack z).2 np s
  rw [pack_unpack] at h
  cases he : cstep (unpack z).1 (toW s) <;> simpa only [he] using h

/-- An exact suffix context, using the existing encL convention. -/
def context : List Cmd → Nat → Nat
  | [], r => r
  | c :: cs, r => pack c (context cs r + 1)

theorem context_strict (cs : List Cmd) {r s : Nat} (h : r < s) :
    context cs r < context cs s := by
  induction cs with
  | nil => exact h
  | cons c cs ih => exact pack_strict c (by omega)

theorem marked_drop_earlier (pre suf : List Cmd) (x : Nat) :
    context pre (encL (.drop x) suf) < context pre (encL (.nip x) suf) := by
  apply context_strict
  cases suf <;> exact P_left_strict _ (by omega)

def swap : Cmd → Cmd
  | .drop x => .nip x
  | .nip x => .drop x
  | c => c

theorem swap_involutive (c : Cmd) : swap (swap c) = c := by cases c <;> rfl

def swapAt : Nat → List Cmd → List Cmd
  | _, [] => []
  | 0, c :: cs => swap c :: cs
  | n + 1, c :: cs => c :: swapAt n cs

theorem swapAt_involutive (n : Nat) (cs : List Cmd) : swapAt n (swapAt n cs) = cs := by
  induction n generalizing cs with
  | zero => cases cs <;> simp [swapAt, swap_involutive]
  | succ n ih => cases cs <;> simp [swapAt, ih]

theorem swapAt_injective (n : Nat) {cs ds : List Cmd}
    (h : swapAt n cs = swapAt n ds) : cs = ds := by
  have hh := congrArg (swapAt n) h
  simpa only [swapAt_involutive] using hh

def listCode : List Cmd → Option Nat
  | [] => none
  | c :: cs => some (encL c cs)

theorem encL_append (c : Cmd) (cs : List Cmd) (d : Cmd) (ds : List Cmd) :
    encL c (cs ++ d :: ds) = context (c :: cs) (encL d ds) := by
  induction cs generalizing c with
  | nil => rfl
  | cons c' cs ih =>
      simp only [List.cons_append, encL, context]
      rw [ih c']
      rfl

theorem listCode_context (pre : List Cmd) (c : Cmd) (cs : List Cmd) :
    listCode (pre ++ c :: cs) = some (context pre (encL c cs)) := by
  cases pre with
  | nil => rfl
  | cons p ps =>
      simp only [List.cons_append, listCode]
      rw [encL_append]

theorem swapAt_marked (pre : List Cmd) (c : Cmd) (cs : List Cmd) :
    swapAt pre.length (pre ++ c :: cs) = pre ++ swap c :: cs := by
  induction pre with
  | nil => rfl
  | cons p ps ih => simp only [List.length_cons, List.cons_append, swapAt, ih]

theorem listCode_injective {cs ds : List Cmd} (h : listCode cs = listCode ds) : cs = ds := by
  cases cs with
  | nil => cases ds <;> simp_all [listCode]
  | cons c cs =>
      cases ds with
      | nil => simp [listCode] at h
      | cons d ds =>
          have hh : encL c cs = encL d ds := by simpa only [listCode, Option.some.injEq] using h
          obtain ⟨hc, hs⟩ := encL_injective c cs d ds hh
          rw [hc, hs]

/-- Changing one marked actual NIP to DROP gives a strictly earlier genuine
candidate; the marked position is retained in the occurrence encoding. -/
theorem marked_occurrence_lower (pre suf : List Cmd) (x : Nat) :
    ∃ lower upper,
      listCode (pre ++ .nip x :: suf) = some upper ∧
      listCode (swapAt pre.length (pre ++ .nip x :: suf)) = some lower ∧
      lower < upper := by
  refine ⟨context pre (encL (.drop x) suf), context pre (encL (.nip x) suf),
    listCode_context _ _ _, ?_, marked_drop_earlier _ _ _⟩
  rw [swapAt_marked]
  exact listCode_context pre (.drop x) suf

theorem occurrence_image_injective (cs ds : List Cmd) (i j : Nat)
    (h : (listCode (swapAt i cs), i) = (listCode (swapAt j ds), j)) :
    cs = ds ∧ i = j := by
  have hij : i = j := congrArg Prod.snd h
  subst j
  have hc := listCode_injective (congrArg Prod.fst h)
  exact ⟨swapAt_injective i hc, rfl⟩

/-! A witnessed finite prefix, without any premise about the original tail.
The credit is a lower bound on its length, not a decoding of that length. -/

def SafeStack (bottom credit stack : Nat) : Prop :=
  ∃ xs : List Nat, stack = pushL xs bottom ∧ credit ≤ xs.length ∧
    ∀ x ∈ xs, C254 x

theorem safeStack_nil (bottom : Nat) : SafeStack bottom 0 bottom :=
  ⟨[], rfl, Nat.le_refl _, fun _ h => by cases h⟩

theorem safeStack_weaken {bottom small big stack : Nat} (h : small ≤ big)
    (hs : SafeStack bottom big stack) : SafeStack bottom small stack := by
  obtain ⟨xs, he, hl, hg⟩ := hs
  exact ⟨xs, he, Nat.le_trans h hl, hg⟩

theorem safeStack_cons {bottom credit stack x : Nat} (hx : C254 x)
    (hs : SafeStack bottom credit stack) : SafeStack bottom (credit + 1) (P x stack) := by
  obtain ⟨xs, he, hl, hg⟩ := hs
  refine ⟨x :: xs, by rw [pushL, ← he], by simp; omega, ?_⟩
  intro y hy
  rcases List.mem_cons.mp hy with h | h
  · exact h ▸ hx
  · exact hg y h

theorem safeStack_pop {bottom credit stack : Nat} (hp : 0 < credit)
    (hs : SafeStack bottom credit stack) :
    C254 (unP stack).1 ∧ SafeStack bottom (credit - 1) (unP stack).2 := by
  obtain ⟨xs, he, hl, hg⟩ := hs
  cases xs with
  | nil => simp at hl; omega
  | cons x xs =>
      rw [he, pushL, unP_P']
      exact ⟨hg x (by simp), xs, rfl, by simp at hl; omega,
        fun y hy => hg y (by simp [hy])⟩

def PrefixInv (bottom credit : Nat) (w : W) : Prop :=
  C254 w.tw ∧ C254 w.h ∧ SafeStack bottom credit w.ws

def nextCredit : Cmd → Nat → Nat
  | .drop _, n => n + 1
  | .nip _, n => n - 1
  | _, n => n

/-- Only NIP needs a positive prefix credit. The global enumeration theorem
must eventually establish this premise at every reached NIP. -/
def PopAdmissible : Cmd → Nat → Prop
  | .nip _, n => 0 < n
  | _, _ => True

/-- Exact local soundness for the existing command semantics. Successful MP
and AX contribute additional prefix entries, whose extra credit is unused. -/
theorem cstep_prefix {bottom credit : Nat} {c : Cmd} {w w' : W}
    (hs : PrefixInv bottom credit w) (hp : PopAdmissible c credit)
    (he : cstep c w = some w') : PrefixInv bottom (nextCredit c credit) w' := by
  obtain ⟨t, stack, d, h⟩ := w
  obtain ⟨ht, hh, hstack⟩ := hs
  cases c with
  | mp x =>
      simp only [cstep] at he
      split at he
      · rename_i hmp
        cases he
        exact ⟨C254.mp ht (hmp ▸ hh), C254.truth,
          safeStack_weaken (by simp only [nextCredit]; omega) (safeStack_cons C254.truth hstack)⟩
      · cases he
        exact ⟨C254.truth, C254.truth, hstack⟩
  | drop x =>
      cases he
      exact ⟨hh, hh, safeStack_cons ht hstack⟩
  | nip x =>
      simp only [cstep] at he
      split at he
      · cases he
      · cases he
        obtain ⟨hhead, htail⟩ := safeStack_pop hp hstack
        exact ⟨ht, hhead, htail⟩
  | ax c x y u =>
      cases he
      refine ⟨gate_good _ _ _, C254.truth, ?_⟩
      have hs' := safeStack_cons (C254.r1 (d + x) (h + y)) <|
        safeStack_cons (C254.r2 (d + x) (h + y) c) <|
        safeStack_cons (C254.r3 (d + x) (h + y) c) <|
        safeStack_cons (C254.r4 (d + x) (h + y) c) <|
        safeStack_cons (C254.r5 (d + x) (h + y) c) <|
        safeStack_cons (C254.r6 (d + x) (h + y)) <|
        safeStack_cons (C254.r7 (d + x) (h + y) c) <|
        safeStack_cons (C254.r8 (d + x) (h + y) c u) <|
        safeStack_cons (C254.gen (d + x) hh) <| safeStack_cons ht hstack
      exact safeStack_weaken (by simp only [nextCredit]; omega) hs'

/-- Halting checks the already protected cache before attempting a pop. -/
theorem cstep_halt {bottom credit : Nat} {c : Cmd} {w : W}
    (hs : PrefixInv bottom credit w) (he : cstep c w = none) : C254 F := by
  obtain ⟨_, hh, _⟩ := hs
  obtain ⟨t, stack, d, h⟩ := w
  cases c with
  | mp x => simp only [cstep] at he; split at he <;> cases he
  | drop x => cases he
  | nip x =>
      simp only [cstep] at he
      split at he
      · rename_i h1
        rw [h1] at hh
        exact hh
      · cases he
  | ax c x y u => cases he

/-- The local prefix invariant applies to actual fetched commands, with no
change to the scheduler or its register effects. -/
theorem enumStep_prefix {bottom credit : Nat} {s s' : St}
    (hs : PrefixInv bottom credit (toW s))
    (hp : PopAdmissible (unpack (fetch s).1).1 credit)
    (he : enumStep s = some s') :
    PrefixInv bottom (nextCredit (unpack (fetch s).1).1 credit) (toW s') := by
  unfold enumStep at he
  rw [execAt_unpack] at he
  cases hc : cstep (unpack (fetch s).1).1 (toW s) with
  | none => simp only [hc] at he; cases he
  | some w =>
      simp only [hc, Option.some.injEq] at he
      subst s'
      exact cstep_prefix hs hp hc

theorem enumStep_halt {bottom credit : Nat} {s : St}
    (hs : PrefixInv bottom credit (toW s)) (he : enumStep s = none) : C254 F := by
  unfold enumStep at he
  rw [execAt_unpack] at he
  cases hc : cstep (unpack (fetch s).1).1 (toW s) with
  | none => exact cstep_halt hs hc
  | some w => simp only [hc] at he; cases he

/-- Candidate zero clears the active formulas without reading the original
stack or pushing the original current formula, even when its MP succeeds. -/
theorem candidate_zero_reset (t stack h : Nat) :
    ∃ out, enumStep ⟨0, 0, t, stack, 0, h⟩ = some out ∧
      out.pl = 0 ∧ out.np = 1 ∧ out.tw = 0 ∧ out.d = 0 ∧ out.h = 0 ∧
      PrefixInv stack 0 (toW out) := by
  have hp0 : pack (.mp 0) 0 = 0 := by simp [pack, P, Cantor.toNat, Cantor.tri]
  have he := execAt_pack (.mp 0) 0 1 (⟨0, 0, t, stack, 0, h⟩ : St)
  rw [hp0] at he
  change (execAt 0 1 ⟨0, 0, t, stack, 0, h⟩) = _ at he
  by_cases hm : wim t 0 = h
  · refine ⟨⟨0, 1, 0, P 0 stack, 0, 0⟩, ?_, rfl, rfl, rfl, rfl, rfl,
      C254.truth, C254.truth,
      safeStack_weaken (by omega) (safeStack_cons C254.truth (safeStack_nil stack))⟩
    simpa only [enumStep, fetch, if_pos rfl, toW, cstep, Nat.add_zero, hm, if_true] using he
  · refine ⟨⟨0, 1, 0, stack, 0, 0⟩, ?_, rfl, rfl, rfl, rfl, rfl,
      C254.truth, C254.truth, safeStack_nil stack⟩
    simpa only [enumStep, fetch, if_pos rfl, toW, cstep, Nat.add_zero, hm, if_false, if_true] using he

end SetTheory.BusyBeaver.ZFC.EnumStackBarrier254
