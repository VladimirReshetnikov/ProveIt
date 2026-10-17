import BusyBeaver.ZFC.EnumStackBarrier254

/-!
The actual increasing candidate scan supplies the dirty-stack barrier.
The marked NIP-to-DROP injection is from intake155/source42 (arrival
fab89c5d26b81cd2ccab2ee5d213ff23725c7726, input
61e77836565f63582561f54745f633d50efd9c7d). We use Enum254's actual
command coding, candidate ordering and six-register execution throughout.
The original enumerator is attributed to Mira-Cult, Jeff Ketchersid and
Andrew James Wade through the source lineage recorded in Enum254.

A useful stronger counting statement puts every NIP in candidates through k
in injection with DROPs in candidates strictly before k. Thus the credit
at candidate k suffices for all its NIPs, even before crediting its DROPs.
No count or safety assumption is added to the final dirty-start theorem.
These are external Lean theorems; no PA representation result is asserted.
-/

namespace SetTheory.BusyBeaver.ZFC.EnumStackCount254

open Code254 Enum254 EnumStackBarrier254

attribute [local irreducible] Code254.P

/-- The exact nonempty command list decoded from candidate k. -/
def commands (k : Nat) : List Cmd :=
  (EnumStackBarrier254.decode k).1 :: (EnumStackBarrier254.decode k).2

theorem commands_code (k : Nat) : listCode (commands k) = some k := by
  simp only [commands, listCode, encL_decode]

theorem commands_nonempty (k : Nat) : commands k ≠ [] := by
  simp only [commands, List.cons_ne_nil, ne_eq, not_false_eq_true]

def isNip : Cmd → Bool
  | .nip _ => true
  | _ => false

def isDrop : Cmd → Bool
  | .drop _ => true
  | _ => false

/-- Positions, rather than just command values, distinguish repeated commands. -/
def positions (p : Cmd → Bool) : List Cmd → List Nat
  | [] => []
  | c :: cs => if p c then 0 :: (positions p cs).map Nat.succ
      else (positions p cs).map Nat.succ

theorem positions_spec (p : Cmd → Bool) (cs : List Cmd) (i : Nat) :
    i ∈ positions p cs ↔ ∃ c, cs[i]? = some c ∧ p c = true := by
  induction cs generalizing i with
  | nil => simp [positions]
  | cons c cs ih =>
      cases i with
      | zero => cases hp : p c <;> simp [positions, hp]
      | succ i =>
          cases hp : p c <;> simp [positions, hp, ih, List.mem_map]

theorem positions_nodup (p : Cmd → Bool) (cs : List Cmd) :
    (positions p cs).Nodup := by
  induction cs with
  | nil => exact List.nodup_nil
  | cons c cs ih =>
      have hm : ((positions p cs).map Nat.succ).Nodup :=
        ih.map Nat.succ (fun _ _ h he => h (Nat.succ.inj he))
      cases hp : p c
      · simpa only [positions, hp, Bool.false_eq_true, if_false] using hm
      · simp only [positions, hp, if_true, List.nodup_cons]
        exact ⟨by simp, hm⟩

def count (p : Cmd → Bool) (cs : List Cmd) : Nat := (positions p cs).length

@[simp] theorem count_nil (p : Cmd → Bool) : count p [] = 0 := rfl

theorem count_cons (p : Cmd → Bool) (c : Cmd) (cs : List Cmd) :
    count p (c :: cs) = (if p c then 1 else 0) + count p cs := by
  cases hp : p c <;> simp [count, positions, hp, Nat.add_comm]

/-- All occurrences in candidates strictly below k, in source order. -/
def occurrences (p : Cmd → Bool) : Nat → List (Nat × Nat)
  | 0 => []
  | k + 1 => occurrences p k ++
      (positions p (commands k)).map (fun i => (k, i))

theorem occurrences_spec (p : Cmd → Bool) (k m i : Nat) :
    (m, i) ∈ occurrences p k ↔ m < k ∧ i ∈ positions p (commands m) := by
  induction k with
  | zero => simp [occurrences]
  | succ k ih =>
      simp only [occurrences, List.mem_append, ih, List.mem_map, Prod.mk.injEq]
      constructor
      · intro h
        rcases h with ⟨hm, hi⟩ | ⟨j, hj, he⟩
        · exact ⟨by omega, hi⟩
        · obtain ⟨hkm, hji⟩ := he
          subst m; subst j
          exact ⟨by omega, hj⟩
      · rintro ⟨hm, hi⟩
        by_cases hmk : m < k
        · exact Or.inl ⟨hmk, hi⟩
        · have hmk : m = k := by omega
          subst m
          exact Or.inr ⟨i, hi, rfl, rfl⟩

theorem occurrences_nodup (p : Cmd → Bool) (k : Nat) :
    (occurrences p k).Nodup := by
  induction k with
  | zero => exact List.nodup_nil
  | succ k ih =>
      rw [occurrences, List.nodup_append]
      refine ⟨ih, ?_, ?_⟩
      · exact (positions_nodup p (commands k)).map (fun i => (k, i))
          (fun _ _ hn he => hn (congrArg Prod.snd he))
      · intro a ha b hb he
        obtain ⟨m, i⟩ := a
        obtain ⟨hm, _⟩ := (occurrences_spec p k m i).mp ha
        obtain ⟨j, _, hj⟩ := List.mem_map.mp hb
        have hmk : m = k := congrArg Prod.fst (he.trans hj.symm)
        omega

def total (p : Cmd → Bool) (k : Nat) : Nat := (occurrences p k).length

@[simp] theorem total_zero (p : Cmd → Bool) : total p 0 = 0 := rfl

theorem total_succ (p : Cmd → Bool) (k : Nat) :
    total p (k + 1) = total p k + count p (commands k) := by
  simp only [total, occurrences, List.length_append, List.length_map, count]

private theorem get_decomposition {cs : List Cmd} {i : Nat} {c : Cmd}
    (h : cs[i]? = some c) :
    ∃ pre suf, cs = pre ++ c :: suf ∧ pre.length = i := by
  induction cs generalizing i with
  | nil => simp at h
  | cons d ds ih =>
      cases i with
      | zero =>
          have hdc : d = c := by simpa using h
          subst d
          exact ⟨[], ds, rfl, rfl⟩
      | succ i =>
          obtain ⟨pre, suf, he, hl⟩ := ih h
          exact ⟨d :: pre, suf, by simp only [List.cons_append, he], by simp [hl]⟩

private theorem get_marked (pre suf : List Cmd) (c : Cmd) :
    (pre ++ c :: suf)[pre.length]? = some c := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simpa only [List.cons_append, List.length_cons,
      List.getElem?_cons_succ] using ih

/-- Retain the marked position while replacing this command with its mate. -/
def image (o : Nat × Nat) : Nat × Nat :=
  ((listCode (swapAt o.2 (commands o.1))).getD 0, o.2)

private theorem image_code (m i : Nat) :
    listCode (swapAt i (commands m)) = some (image (m, i)).1 := by
  have hn : swapAt i (commands m) ≠ [] := by
    intro h
    have hh := congrArg (swapAt i) h
    simp only [swapAt_involutive, swapAt] at hh
    exact commands_nonempty m hh
  cases hc : swapAt i (commands m) with
  | nil => exact False.elim (hn hc)
  | cons c cs => simp only [image, hc, listCode, Option.getD_some]

theorem image_injective (a b : Nat × Nat) (h : image a = image b) : a = b := by
  obtain ⟨m, i⟩ := a
  obtain ⟨n, j⟩ := b
  have hi : i = j := congrArg Prod.snd h
  have hc : listCode (swapAt i (commands m)) = listCode (swapAt j (commands n)) := by
    rw [image_code, image_code, congrArg Prod.fst h]
  obtain ⟨hcmd, hij⟩ := occurrence_image_injective (commands m) (commands n) i j
    (Prod.ext hc hi)
  have hmn : m = n := by
    have hh := congrArg listCode hcmd
    simpa only [commands_code, Option.some.injEq] using hh
  exact Prod.ext hmn hij

theorem image_earlier_drop (m i : Nat) (h : i ∈ positions isNip (commands m)) :
    (image (m, i)).1 < m ∧
      (image (m, i)).2 ∈ positions isDrop (commands (image (m, i)).1) := by
  obtain ⟨c, hc, hp⟩ := (positions_spec _ _ _).mp h
  cases c with
  | mp x => cases hp
  | drop x => cases hp
  | ax c x y u => cases hp
  | nip x =>
      obtain ⟨pre, suf, he, hl⟩ := get_decomposition hc
      obtain ⟨lo, hi, hhi, hlo, hlt⟩ := marked_occurrence_lower pre suf x
      have hhim : hi = m := by
        rw [← he, commands_code] at hhi
        exact Option.some.inj hhi.symm
      subst hi
      have himg : (image (m, i)).1 = lo := by
        have hcode := image_code m i
        rw [he, ← hl] at hcode
        rw [hlo] at hcode
        simpa only [hl] using Option.some.inj hcode.symm
      refine ⟨by rw [himg]; exact hlt, ?_⟩
      have hcmd : commands lo = pre ++ .drop x :: suf := by
        apply listCode_injective
        rw [commands_code]
        rw [swapAt_marked] at hlo
        exact hlo.symm
      change i ∈ positions isDrop (commands (image (m, i)).1)
      rw [himg, hcmd, ← hl]
      exact (positions_spec _ _ _).mpr ⟨.drop x, get_marked _ _ _, rfl⟩

private theorem injection_length_le (xs ys : List (Nat × Nat)) (f : (Nat × Nat) → Nat × Nat)
    (nd : xs.Nodup) (into : ∀ x ∈ xs, f x ∈ ys)
    (inj : ∀ x ∈ xs, ∀ y ∈ xs, f x = f y → x = y) : xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
      have hx : f x ∈ ys := into x (by simp)
      have nds : xs.Nodup := (List.nodup_cons.mp nd).2
      have into' : ∀ a ∈ xs, f a ∈ ys.erase (f x) := by
        intro a ha
        have ne : f a ≠ f x := by
          intro he
          have ax := inj a (by simp [ha]) x (by simp) he
          exact (List.nodup_cons.mp nd).1 (ax ▸ ha)
        exact (List.mem_erase_of_ne ne).mpr (into a (by simp [ha]))
      have inj' : ∀ a ∈ xs, ∀ b ∈ xs, f a = f b → a = b := by
        intro a ha b hb he
        exact inj a (by simp [ha]) b (by simp [hb]) he
      have hi := ih (ys.erase (f x)) nds into' inj'
      have he := List.length_erase_of_mem hx
      have hp : 0 < ys.length := List.length_pos_iff_exists_mem.mpr ⟨f x, hx⟩
      simp only [List.length_cons]
      omega

/-- All NIPs through candidate k are covered by DROPs strictly before k.
This is stronger than merely nonnegative credit at candidate boundaries. -/
theorem all_pops_covered (k : Nat) : total isNip (k + 1) ≤ total isDrop k := by
  apply injection_length_le (occurrences isNip (k + 1)) (occurrences isDrop k)
    image (occurrences_nodup _ _)
  · intro a ha
    obtain ⟨m, i⟩ := a
    obtain ⟨hm, hi⟩ := (occurrences_spec _ _ _ _).mp ha
    obtain ⟨hl, hd⟩ := image_earlier_drop m i hi
    apply (occurrences_spec _ _ _ _).mpr
    constructor
    · change (image (m, i)).1 < k
      omega
    · exact hd
  · intro a _ b _ h
    exact image_injective a b h

/-- Distinguished safe pushes minus pops before candidate k. -/
def credit (k : Nat) : Nat := total isDrop k - total isNip k

theorem total_pops_le (k : Nat) : total isNip k ≤ total isDrop k := by
  have h := all_pops_covered k
  rw [total_succ] at h
  omega

theorem candidate_reserve (k : Nat) : count isNip (commands k) ≤ credit k := by
  have h := all_pops_covered k
  rw [total_succ] at h
  unfold credit
  omega

theorem credit_succ (k : Nat) :
    credit (k + 1) = credit k + count isDrop (commands k) - count isNip (commands k) := by
  have h := total_pops_le k
  have hr := candidate_reserve k
  unfold credit at *
  rw [total_succ, total_succ]
  omega

@[simp] theorem credit_zero : credit 0 = 0 := rfl

@[simp] theorem credit_one : credit 1 = 0 := by
  rw [credit_succ]
  simp only [credit_zero, commands, decode_zero, count_cons, count_nil, isDrop, isNip]
  rfl

private theorem command_reserve (c : Cmd) (cs : List Cmd) (n : Nat)
    (hr : count isNip (c :: cs) ≤ n) :
    PopAdmissible c n ∧ count isNip cs ≤ nextCredit c n := by
  cases c <;> simp only [count_cons, isNip, nextCredit, PopAdmissible,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add] at * <;>
    constructor <;> first | trivial | omega

private theorem command_credit (c : Cmd) (cs : List Cmd) (n : Nat)
    (hr : count isNip (c :: cs) ≤ n) :
    nextCredit c n + count isDrop cs - count isNip cs =
      n + count isDrop (c :: cs) - count isNip (c :: cs) := by
  cases c <;> simp only [count_cons, isNip, isDrop, nextCredit,
    Bool.false_eq_true, if_false, if_true, Nat.zero_add] at * <;> omega

/-- If no contradiction is derivable, enough credit executes an entire actual
command list safely. Extra safe pushes from MP and AX are deliberately unused. -/
theorem cexec_safe (hn : ¬ C254 F) (cs : List Cmd) {bottom n : Nat} {w : W}
    (hs : PrefixInv bottom n w) (hr : count isNip cs ≤ n) :
    ∃ out, cexec cs w = some out ∧
      PrefixInv bottom (n + count isDrop cs - count isNip cs) out := by
  induction cs generalizing n w with
  | nil => exact ⟨w, rfl, by simpa only [count_nil, Nat.add_zero, Nat.sub_zero] using hs⟩
  | cons c cs ih =>
      obtain ⟨hp, hrest⟩ := command_reserve c cs n hr
      cases he : cstep c w with
      | none => exact False.elim (hn (cstep_halt hs he))
      | some w1 =>
          obtain ⟨out, hout, hsout⟩ := ih (cstep_prefix hs hp he) hrest
          refine ⟨out, ?_, ?_⟩
          · simpa only [cexec, he] using hout
          · rw [command_credit c cs n hr] at hsout
            exact hsout

/-- Successful execution of a nonempty candidate has the exact pointer,
register output and number of actual scheduler steps. -/
theorem exec_list_some : ∀ (cs : List Cmd) (c : Cmd) (s : St) (out : W),
    (fetch s).1 = encL c cs → cexec (c :: cs) (toW s) = some out →
    run (cs.length + 1) s =
      some ⟨0, (fetch s).2, out.tw, out.ws, out.d, out.h⟩
  | [], c, s, out, hf, hx => by
      cases hc : cstep c (toW s) with
      | none => simp only [cexec, hc] at hx; cases hx
      | some w =>
          have hwo : w = out := by simpa only [cexec, hc, Option.some.injEq] using hx
          subst w
          simp only [List.length_nil, run]
          unfold enumStep
          rw [hf, encL, execAt_pack, hc]
  | c' :: cs, c, s, out, hf, hx => by
      cases hc : cstep c (toW s) with
      | none => simp only [cexec, hc] at hx; cases hx
      | some w =>
          have htail : cexec (c' :: cs) w = some out := by
            simpa only [cexec, hc] using hx
          let s1 : St := ⟨encL c' cs + 1, (fetch s).2, w.tw, w.ws, w.d, w.h⟩
          have hstep : enumStep s = some s1 := by
            unfold enumStep
            rw [hf, encL, execAt_pack, hc]
          have hf1 : (fetch s1).1 = encL c' cs := by simp [fetch, s1]
          have hr := exec_list_some cs c' s1 out hf1 htail
          have hnp : (fetch s1).2 = (fetch s).2 := by simp [fetch, s1]
          rw [hnp] at hr
          rw [List.length_cons, run_succ _ s s1 hstep]
          exact hr

/-- A completed candidate advances np exactly once and retains the full
four-register cexec result, including the arbitrary original stack bottom. -/
theorem candidate_some (k : Nat) (s : St) (out : W)
    (hpl : s.pl = 0) (hnp : s.np = k)
    (hx : cexec (commands k) (toW s) = some out) :
    run (commands k).length s = some ⟨0, k + 1, out.tw, out.ws, out.d, out.h⟩ := by
  have hf : (fetch s).1 = k := by simp only [fetch, hpl, if_pos, hnp]
  have hf2 : (fetch s).2 = k + 1 := by simp only [fetch, hpl, if_pos, hnp]
  have he := exec_list_some (EnumStackBarrier254.decode k).2
    (EnumStackBarrier254.decode k).1 s out (hf.trans (encL_decode k).symm) hx
  rw [hf2] at he
  exact he

/-- Starting with exactly the reserve for candidate k, the actual enumerator
has arbitrarily late safe candidate boundaries unless a contradiction exists. -/
theorem safe_boundaries (hn : ¬ C254 F) (k bottom : Nat) (s : St)
    (hpl : s.pl = 0) (hnp : s.np = k) (hs : PrefixInv bottom (credit k) (toW s)) :
    ∀ j, ∃ t out, j ≤ t ∧ run t s = some out ∧ out.pl = 0 ∧ out.np = k + j ∧
      PrefixInv bottom (credit (k + j)) (toW out) := by
  intro j
  induction j with
  | zero => exact ⟨0, s, Nat.le_refl _, rfl, hpl, by omega, by simpa using hs⟩
  | succ j ih =>
      obtain ⟨t, st, hjt, hrun, hstpl, hstnp, hst⟩ := ih
      obtain ⟨w, hw, hsw⟩ := cexec_safe hn (commands (k + j)) hst (candidate_reserve _)
      let out : St := ⟨0, k + j + 1, w.tw, w.ws, w.d, w.h⟩
      refine ⟨t + (commands (k + j)).length, out, ?_, ?_, rfl, ?_, ?_⟩
      · have hp : 0 < (commands (k + j)).length := by
          simp only [commands, List.length_cons]; omega
        omega
      · rw [run_add _ _ s st hrun]
        exact candidate_some (k + j) st w hstpl hstnp hw
      · dsimp only [out]; omega
      · change PrefixInv bottom (credit (k + (j + 1))) w
        rw [show k + (j + 1) = (k + j) + 1 by omega, credit_succ]
        exact hsw

/-- Once an actual run is none it remains none. This uses the existing
partial-run definition, rather than treating a missing command as a halt. -/
theorem run_none_add (n m : Nat) (s : St) (h : run n s = none) :
    run (n + m) s = none := by
  induction n generalizing s with
  | zero => cases h
  | succ n ih =>
      cases he : enumStep s with
      | none =>
          rw [show n + 1 + m = (n + m) + 1 by omega]
          simp only [run, he]
      | some s1 =>
          have hh : run n s1 = none := by simpa only [run, he] using h
          rw [show n + 1 + m = (n + m) + 1 by omega, run_succ _ s s1 he]
          exact ih s1 hh

/-- No extra count hypothesis: the credit here is the defined exact balance
of the actual earlier candidates. -/
theorem sound_from_credit (k bottom : Nat) (s : St)
    (hpl : s.pl = 0) (hnp : s.np = k) (hs : PrefixInv bottom (credit k) (toW s)) :
    EnumSafeStart254.HaltsFrom s → C254 F := by
  intro hh
  by_cases hc : C254 F
  · exact hc
  · obtain ⟨n, st, hrun, hhalt⟩ := hh
    have hn : run (n + 1) s = none := by
      rw [run_add n 1 s st hrun]
      simp only [run, hhalt]
    obtain ⟨t, out, ht, hr, _, _, _⟩ := safe_boundaries hc k bottom s hpl hnp hs (n + 1)
    have hnone : run t s = none := by
      have h := run_none_add (n + 1) (t - (n + 1)) s hn
      have he : n + 1 + (t - (n + 1)) = t := by omega
      rwa [he] at h
    rw [hnone] at hr
    cases hr

/-- Generic candidate-boundary adapter for a witnessed good prefix. The required
credit is computed from the actual syntax of all earlier candidates. -/
theorem credit_start_iff (k bottom : Nat) (s : St)
    (hpl : s.pl = 0) (hnp : s.np = k) (hs : PrefixInv bottom (credit k) (toW s)) :
    EnumSafeStart254.HaltsFrom s ↔ C254 F :=
  ⟨sound_from_credit k bottom s hpl hnp hs, EnumSafeStart254.complete_from s⟩

private theorem halts_after_some {s out : St} (he : enumStep s = some out) :
    EnumSafeStart254.HaltsFrom s → EnumSafeStart254.HaltsFrom out := by
  rintro ⟨n, st, hrun, hhalt⟩
  cases n with
  | zero =>
      have hst : s = st := Option.some.inj hrun
      subst st
      rw [he] at hhalt
      cases hhalt
  | succ n => exact ⟨n, st, by simpa only [run, he] using hrun, hhalt⟩

/-- Exact arbitrary dirty bottom theorem for the actual enumerator.
Candidate zero protects the active formulas; every later pop is covered
by a strictly earlier distinguished push. -/
theorem dirty_start_iff (t stack h : Nat) :
    EnumSafeStart254.HaltsFrom ⟨0, 0, t, stack, 0, h⟩ ↔ C254 F := by
  constructor
  · intro hh
    obtain ⟨out, he, hpl, hnp, _, _, _, hs⟩ := candidate_zero_reset t stack h
    apply sound_from_credit 1 stack out hpl hnp
    · simpa only [credit_one] using hs
    · exact halts_after_some he hh
  · exact EnumSafeStart254.complete_from _

/-- Candidate one also admits an arbitrary dirty tail, provided the active
formula and cache are already theorems; numerical d is unrestricted. -/
theorem candidate_one_iff (t stack d h : Nat) (ht : C254 t) (hh : C254 h) :
    EnumSafeStart254.HaltsFrom ⟨0, 1, t, stack, d, h⟩ ↔ C254 F := by
  constructor
  · exact sound_from_credit 1 stack _ rfl rfl
      (by rw [credit_one]; exact ⟨ht, hh, safeStack_nil stack⟩)
  · exact EnumSafeStart254.complete_from _

end SetTheory.BusyBeaver.ZFC.EnumStackCount254
