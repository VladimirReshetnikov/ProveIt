import BusyBeaver.ZFC.KRuntimeCore
import BusyBeaver.ZFC.KTable230

/-!
The four register lemmas of the K-family engine (port of K230's `Tape230Blocks.v` and
`Tape230Carry.v`; the initial list, scan and marker proofs there are adapted from Jeff Ketchersid's
m254 `Box.v`).

They are proved once, for every table that agrees with K230 on the 23 engine states the register
operations read (`boxStates`, found by tracing; the proofs below confirm the list suffices). The
result is `boxLemmas : Agree M tm230 boxStates → BoxLemmas M`, the hypothesis of
`KRuntimeCore.exec_sound`.
-/

namespace SetTheory.BusyBeaver.ZFC.KTape

open KZip KRuntimeCore KTableCore

/-- The engine states read by the mark, increment and decrement routines. -/
def boxStates : List Nat :=
  [0, 1, 2, 3, 16, 22, 25, 32, 33, 36, 40, 48, 51, 54, 55, 60, 64, 66, 74, 94, 97, 113, 198]

/-! ## List facts -/

def sepsL (vs : List Nat) : List Bool := vs.flatMap fun v => List.replicate (v + 1) true ++ [false]

theorem rep_comm {α : Type} (x : α) (n : Nat) (l : List α) :
    List.replicate n x ++ x :: l = x :: (List.replicate n x ++ l) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

@[simp] theorem sepsR_nil : sepsR [] = [] := rfl

theorem sepsR_cons (v : Nat) (vs : List Nat) :
    sepsR (v :: vs) = false :: true :: (List.replicate v true ++ sepsR vs) := by
  simp [sepsR, List.replicate_succ]

theorem sepsR_app (a b : List Nat) : sepsR (a ++ b) = sepsR a ++ sepsR b := by
  simp [sepsR, List.flatMap_append]

theorem sepsL_cons (v : Nat) (vs : List Nat) :
    sepsL (v :: vs) = true :: (List.replicate v true ++ false :: sepsL vs) := by
  simp [sepsL, List.replicate_succ]

theorem sepsL_app (a b : List Nat) : sepsL (a ++ b) = sepsL a ++ sepsL b := by
  simp [sepsL, List.flatMap_append]

theorem rev_sepsR (vs : List Nat) : (sepsR vs).reverse = sepsL vs.reverse := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [sepsR_cons, ih, sepsL, List.replicate_succ']

theorem split_at : ∀ (vs : List Nat) (r : Nat), r < vs.length →
    ∃ pre v rest, vs = pre ++ v :: rest ∧ pre.length = r
  | [], r, h => absurd h (by simp)
  | x :: vs, 0, _ => ⟨[], x, vs, rfl, rfl⟩
  | x :: vs, r + 1, h => by
      obtain ⟨pre, v, rest, e, hl⟩ := split_at vs r (by simp at h; omega)
      exact ⟨x :: pre, v, rest, by rw [e]; rfl, by simp [hl]⟩

theorem nth_split (pre rest : List Nat) (v : Nat) : (pre ++ v :: rest).getD pre.length 0 = v := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simp

theorem incr_split (pre rest : List Nat) (v : Nat) :
    incr pre.length (pre ++ v :: rest) = pre ++ (v + 1) :: rest := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simp [incr, ih]

theorem decr_split (pre rest : List Nat) (v : Nat) :
    decr pre.length (pre ++ v :: rest) = pre ++ (v - 1) :: rest := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simp [decr, ih]

theorem sepsM_split (pre rest : List Nat) (v : Nat) :
    sepsM pre.length (pre ++ v :: rest) =
      sepsR pre ++ false :: false :: (List.replicate v true ++ sepsR rest) := by
  induction pre with
  | nil => rfl
  | cons p pre ih => simp [sepsM, ih, sepsR_cons, List.replicate_succ]

theorem rev_sepsR_snoc (pre : List Nat) (w : Nat) :
    (sepsR (pre ++ [w])).reverse = List.replicate w true ++ true :: false :: sepsL pre.reverse := by
  rw [rev_sepsR, List.reverse_append, List.reverse_singleton, List.singleton_append, sepsL_cons,
    rep_comm]

theorem rev_sepsR_cons (p : Nat) (pre : List Nat) (l : List Bool) :
    (sepsR (p :: pre)).reverse ++ l =
      (sepsR pre).reverse ++ (List.replicate p true ++ true :: false :: l) := by
  simp [sepsR_cons]

theorem sepsR_one (w : Nat) (Y : List Bool) :
    sepsR [w] ++ Y = false :: true :: (List.replicate w true ++ Y) := by
  simp [sepsR_cons]

theorem exists_snoc : ∀ (vs : List Nat), vs ≠ [] → ∃ pre w, vs = pre ++ [w]
  | [], h => absurd rfl h
  | [w], _ => ⟨[], w, rfl⟩
  | x :: y :: vs, _ => by
      obtain ⟨pre, w, e⟩ := exists_snoc (y :: vs) (List.cons_ne_nil _ _)
      exact ⟨x :: pre, w, by rw [e]; rfl⟩

/-! ## Single steps -/

theorem stR {M : TMN} {q q' : Nat} {b w : Bool} {l r : List Bool} {X : Conf}
    (T : M q b = some (w, true, q')) (h : Reach M (zc q' (w :: l) r) X) :
    Reach M (zc q l (b :: r)) X :=
  (Reach.of_step (zR T)).trans h

theorem stL {M : TMN} {q q' : Nat} {b w : Bool} {l r : List Bool} {X : Conf}
    (T : M q b = some (w, false, q')) (h : Reach M (zl q' l (w :: r)) X) :
    Reach M (zc q l (b :: r)) X :=
  (Reach.of_step (zL T)).trans h

/-- One concrete step, its row read from K230 through the agreement hypothesis. -/
macro "go" h:term : tactic => `(tactic| first
  | refine stR (Agree.row $h (by decide) rfl) ?_
  | refine stL (Agree.row $h (by decide) rfl) ?_)

theorem zc_blank (q : Nat) (l : List Bool) : zc q l [] = zc q l [false] := by
  simp [zc, trim_cons]

/-! ## Generic scans across register blocks -/

section Scans

variable {M : TMN} {qa qb : Nat}

/-- Rightwards: `qa` crosses ones; a `0` sends it to `qb`, which returns to `qa` on a `1`. -/
theorem fwd (F1 : M qa true = some (true, true, qa)) (F2 : M qa false = some (false, true, qb))
    (F3 : M qb true = some (true, true, qa)) :
    ∀ (pre : List Nat) (l X : List Bool),
      Reach M (zc qa l (sepsR pre ++ X)) (zc qa ((sepsR pre).reverse ++ l) X)
  | [], _, _ => Reach.refl M _
  | p :: pre, l, X => by
      rw [show sepsR (p :: pre) ++ X = false :: true :: (List.replicate p true ++ (sepsR pre ++ X)) by
        simp [sepsR_cons]]
      refine stR F2 (stR F3 ((scanR F1 p _ _).trans ((fwd F1 F2 F3 pre _ X).trans (Reach.of_eq ?_))))
      rw [rev_sepsR_cons]

/-- Leftwards: the same pattern, ending one cell left of the file in state `qb`. -/
theorem ret (R1 : M qa true = some (true, false, qa)) (R2 : M qa false = some (false, false, qb))
    (R3 : M qb true = some (true, false, qa)) :
    ∀ (rp : List Nat) (w : Nat) (l Y : List Bool) (q : Nat), M q true = some (true, false, qa) →
      Reach M (zc q (List.replicate w true ++ false :: (sepsL rp ++ l)) (true :: Y))
        (zl qb l (sepsR (rp.reverse ++ [w]) ++ Y))
  | [], w, l, Y, q, T => by
      refine stL T ((scanL R1 w (false :: l) (true :: Y)).trans ?_)
      rw [zl_cons]
      refine stL R2 (Reach.of_eq ?_)
      simp [sepsR_cons, rep_comm]
  | w' :: rp, w, l, Y, q, T => by
      refine stL T ((scanL R1 w (false :: (sepsL (w' :: rp) ++ l)) (true :: Y)).trans ?_)
      rw [zl_cons]
      refine stL R2 ?_
      rw [sepsL_cons, List.cons_append, zl_cons, List.append_assoc, List.cons_append]
      refine (ret R1 R2 R3 rp w' l _ qb R3).trans (Reach.of_eq ?_)
      simp [sepsR_app, sepsR_cons, rep_comm]

/-- The same from a `zl` configuration on the last `1` of a nonempty file. -/
theorem ret_file (R1 : M qa true = some (true, false, qa)) (R2 : M qa false = some (false, false, qb))
    (R3 : M qb true = some (true, false, qa)) {vs : List Nat} (l Y : List Bool) {q : Nat}
    (hne : vs ≠ []) (T : M q true = some (true, false, qa)) :
    Reach M (zl q ((sepsR vs).reverse ++ l) Y) (zl qb l (sepsR vs ++ Y)) := by
  obtain ⟨pre, w, rfl⟩ := exists_snoc vs hne
  rw [rev_sepsR_snoc, List.append_assoc, List.cons_append, List.cons_append, rep_comm, zl_cons]
  simpa using ret R1 R2 R3 pre.reverse w l Y q T

end Scans

/-! ### Prefix carries -/

def carryR (vs : List Nat) : List Bool := vs.flatMap fun v => true :: false :: List.replicate v true

theorem carryR_cons (v : Nat) (vs : List Nat) :
    carryR (v :: vs) = true :: false :: (List.replicate v true ++ carryR vs) := by
  simp [carryR]

theorem carryR_final (vs : List Nat) : carryR vs ++ [true] = true :: sepsR vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [carryR_cons, sepsR_cons, ih, rep_comm]

theorem carryR_rev (vs : List Nat) (l : List Bool) :
    true :: ((carryR vs).reverse ++ l) = (sepsR vs).reverse ++ true :: l := by
  have E := congrArg List.reverse (carryR_final vs)
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.singleton_append] at E
  calc true :: ((carryR vs).reverse ++ l) = (true :: (carryR vs).reverse) ++ l := rfl
    _ = ((sepsR vs).reverse ++ [true]) ++ l := by rw [E]
    _ = _ := by simp

/-! ## The register routines of the engine -/

section Box

variable {M : TMN} (hA : Agree M tm230 boxStates)
include hA

theorem sk_self (j : Nat) (hj : j < 9) : M (sk j) true = some (true, true, sk j) := by
  have : ∀ j, j < 9 → sk j ∈ boxStates ∧ tm230 (sk j) true = some (true, true, sk j) := by decide
  exact hA.row (this j hj).1 (this j hj).2

theorem sk_next (j : Nat) (hj : j < 8) : M (sk (j + 1)) false = some (false, true, sk j) := by
  have : ∀ j, j < 8 → sk (j + 1) ∈ boxStates ∧ tm230 (sk (j + 1)) false = some (false, true, sk j) := by
    decide
  exact hA.row (this j hj).1 (this j hj).2

theorem skip : ∀ (pre : List Nat) (m : Nat) (l X : List Bool), pre.length + m < 9 →
    Reach M (zc (sk (pre.length + m)) l (sepsR pre ++ X)) (zc (sk m) ((sepsR pre).reverse ++ l) X)
  | [], m, l, X, _ => by
      simp only [List.length_nil, Nat.zero_add, sepsR_nil, List.nil_append, List.reverse_nil]
      exact Reach.refl M _
  | p :: pre, m, l, X, h => by
      simp only [List.length_cons] at h ⊢
      rw [show pre.length + 1 + m = (pre.length + m) + 1 by omega,
        show sepsR (p :: pre) ++ X = false :: (List.replicate (p + 1) true ++ (sepsR pre ++ X)) by
          simp [sepsR_cons, List.replicate_succ]]
      refine stR (sk_next hA _ (by omega)) ((scanR (sk_self hA _ (by omega)) (p + 1) _ _).trans
        ((skip pre m _ X (by omega)).trans (Reach.of_eq ?_)))
      rw [rev_sepsR_cons, List.replicate_succ, List.cons_append, rep_comm]

theorem box_mark (q r : Nat) (l : List Bool) (vs : List Nat) (hq : skipTarget q = some r)
    (hl : 10 ≤ vs.length) : Reach M (zc q l (sepsR vs)) (zl (markExit r) l (sepsM r vs)) := by
  obtain ⟨rfl, hr⟩ := skipTarget_sk hq
  obtain ⟨pre, v, rest, rfl, rfl⟩ := split_at vs r (by omega)
  rw [sepsR_app, sepsM_split]
  refine (skip hA pre 0 l _ (by omega)).trans ?_
  rw [sepsR_cons]
  go hA
  go hA
  rw [zl_cons]
  go hA
  cases pre with
  | nil => exact Reach.refl M _
  | cons p pre' =>
      have h3 : markExit (p :: pre').length = 3 := by simp [markExit]
      rw [h3]
      exact ret_file (qa := 2) (qb := 3) (hA.row (by decide) rfl) (hA.row (by decide) rfl)
        (hA.row (by decide) rfl) l _ (List.cons_ne_nil _ _) (hA.row (by decide) rfl)

theorem carry_fwd : ∀ (pre : List Nat) (l X : List Bool),
    Reach M (zc 0 l (sepsR pre ++ X)) (zc 0 ((carryR pre).reverse ++ l) X)
  | [], _, _ => Reach.refl M _
  | p :: pre, l, X => by
      rw [show sepsR (p :: pre) ++ X = false :: true :: (List.replicate p true ++ (sepsR pre ++ X)) by
        simp [sepsR_cons]]
      go hA
      go hA
      refine (scanR (hA.row (q := 0) (b := true) (by decide) rfl) p _ _).trans
        ((carry_fwd pre _ X).trans (Reach.of_eq ?_))
      simp [carryR_cons]

theorem rollback_block (v : Nat) (l Y : List Bool) :
    Reach M (zl 97 ((true :: false :: List.replicate v true).reverse ++ l) Y)
      (zl 97 l (sepsR [v] ++ Y)) := by
  rw [show (true :: false :: List.replicate v true).reverse ++ l =
      List.replicate v true ++ false :: true :: l by simp]
  refine (scanL (hA.row (q := 97) (b := true) (by decide) rfl) v _ _).trans ?_
  rw [zl_cons]
  go hA
  rw [zl_cons]
  go hA
  exact Reach.of_eq (by simp [sepsR_one])

theorem rollback : ∀ (pre : List Nat) (l Y : List Bool),
    Reach M (zl 97 ((carryR pre).reverse ++ l) Y) (zl 97 l (sepsR pre ++ Y))
  | [], _, _ => Reach.refl M _
  | v :: pre, l, Y => by
      rw [show (carryR (v :: pre)).reverse ++ l =
          (carryR pre).reverse ++ ((true :: false :: List.replicate v true).reverse ++ l) by
        simp [carryR_cons]]
      refine (rollback pre _ Y).trans ((rollback_block hA v l _).trans (Reach.of_eq ?_))
      rw [← List.append_assoc, ← sepsR_app]
      rfl

theorem ret_file_any (vs : List Nat) (l Y : List Bool) :
    Reach M (zl 40 ((sepsR vs).reverse ++ l) Y) (zl 40 l (sepsR vs ++ Y)) := by
  cases vs with
  | nil => exact Reach.refl M _
  | cons v vs =>
      exact ret_file (qa := 54) (qb := 40) (hA.row (by decide) rfl) (hA.row (by decide) rfl)
        (hA.row (by decide) rfl) l Y (List.cons_ne_nil _ _) (hA.row (by decide) rfl)

theorem box_decp (r : Nat) (l : List Bool) (vs : List Nat) (hr : r < 9) (hl : 10 ≤ vs.length)
    (hz : vs.getD r 0 ≠ 0) :
    Reach M (zc 0 l (sepsM r vs)) (zl 40 (true :: l) (sepsR (decr r vs))) := by
  obtain ⟨pre, v, rest, rfl, rfl⟩ := split_at vs r (by omega)
  rw [nth_split] at hz
  obtain ⟨v, rfl⟩ : ∃ u, v = u + 1 := ⟨v - 1, by omega⟩
  rw [sepsM_split, decr_split, Nat.add_sub_cancel]
  refine (carry_fwd hA pre l _).trans ?_
  simp only [List.replicate_succ, List.cons_append]
  go hA
  go hA
  go hA
  rw [zl_cons]
  go hA
  rw [carryR_rev]
  refine (ret_file_any hA pre (true :: l) _).trans (Reach.of_eq ?_)
  simp [sepsR_app, sepsR_cons]

theorem box_dec0 (r : Nat) (l : List Bool) (vs : List Nat) (hr : r < 9) (hl : 10 ≤ vs.length)
    (hz : vs.getD r 0 = 0) : Reach M (zc 0 l (sepsM r vs)) (zl 97 l (sepsR vs)) := by
  obtain ⟨pre, v, rest, rfl, rfl⟩ := split_at vs r (by omega)
  rw [nth_split] at hz
  subst hz
  cases rest with
  | nil => simp at hl; omega
  | cons w rest =>
      rw [sepsM_split, sepsR_cons]
      refine (carry_fwd hA pre l _).trans ?_
      simp only [List.replicate_zero, List.nil_append]
      go hA
      go hA
      go hA
      go hA
      rw [zl_cons]
      go hA
      rw [zl_cons]
      go hA
      rw [zl_cons]
      go hA
      refine (rollback hA pre l _).trans (Reach.of_eq ?_)
      simp [sepsR_app, sepsR_cons]

theorem box_inc (r : Nat) (l : List Bool) (vs : List Nat) (hr : r < 9) (hl : 10 ≤ vs.length) :
    Reach M (zc 64 l (sepsM r vs)) (zl 40 l (sepsR (incr r vs ++ [1]))) := by
  obtain ⟨pre, v, rest, rfl, rfl⟩ := split_at vs r (by omega)
  rw [sepsM_split, incr_split]
  refine (fwd (hA.row (q := 64) (b := true) (by decide) rfl)
    (hA.row (q := 64) (b := false) (by decide) rfl) (hA.row (q := 74) (b := true) (by decide) rfl)
    pre l _).trans ?_
  go hA
  go hA
  refine (scanR (hA.row (q := 0) (b := true) (by decide) rfl) v _ _).trans ?_
  have hc := carry_fwd hA rest (List.replicate v true ++ true :: false :: ((sepsR pre).reverse ++ l)) []
  rw [List.append_nil] at hc
  refine hc.trans ?_
  rw [zc_blank]
  go hA
  rw [zc_blank]
  go hA
  rw [zc_blank]
  go hA
  rw [zc_blank]
  go hA
  rw [zl_cons]
  go hA
  rw [zl_cons]
  go hA
  rw [carryR_rev, show (sepsR rest).reverse ++ true :: (List.replicate v true ++ true :: false ::
      ((sepsR pre).reverse ++ l)) = (sepsR (pre ++ (v + 1) :: rest)).reverse ++ l by
    simp [sepsR_app, sepsR_cons, List.replicate_succ, rep_comm]]
  refine (ret_file_any hA _ l _).trans (Reach.of_eq ?_)
  simp [sepsR_app, sepsR_cons]

/-- The register lemmas hold for every table that agrees with K230 on `boxStates`. -/
theorem boxLemmas : BoxLemmas M where
  mark q r l vs hq hl := box_mark hA q r l vs hq hl
  inc r l vs hr hl := box_inc hA r l vs hr hl
  dec0 r l vs hr hl hz := box_dec0 hA r l vs hr hl hz
  decp r l vs hr hl hz := box_decp hA r l vs hr hl hz

end Box

end SetTheory.BusyBeaver.ZFC.KTape
