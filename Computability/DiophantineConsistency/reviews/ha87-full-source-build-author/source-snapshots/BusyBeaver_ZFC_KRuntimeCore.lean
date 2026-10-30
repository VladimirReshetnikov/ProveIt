import BusyBeaver.ZFC.KZip

/-!
A certified symbolic run-length executor for the K-family engine (port of K230's
`Runtime230Core.v`, itself adapted from Jeff Ketchersid's m254 `SymExec.v`).

A symbolic configuration `(q, onl, L, R)` describes, for every gap parameter `n` and every register
file `vs`, the zipper configuration `conc n vs s`: state `q`, head on the first cell of `R`
(`onl = false`) or of `L` (`onl = true`). Both sides are lists of segments: one cell `b`, a run
`run b a c` of `a * n + c` cells `b`, or the register file `box x` (only as the last segment of `R`).
`sstep` does one abstract step: a concrete transition, a whole self-loop over a run, peeling a cell
off a run, or a register-file excursion justified by the four register lemmas, which are hypotheses
here (`BoxLemmas`). `exec_sound`: whatever `exec` reaches, the machine reaches, for every `n` and
every valid `vs`. The box oracle uses K230's state labels; K-family tables keep K230's engine
labels (deleted states are disabled), so this module serves all of them.
-/

namespace SetTheory.BusyBeaver.ZFC.KRuntimeCore

open KZip

/-! ## Register files: a register of value `v` is `0 1^(v+1)`. -/

def sepsR (vs : List Nat) : List Bool := vs.flatMap fun v => false :: List.replicate (v + 1) true

/-- The same file with the first `1` of register `r` erased (the "mark"). -/
def sepsM : Nat → List Nat → List Bool
  | _, [] => []
  | 0, v :: vs => false :: false :: List.replicate v true ++ sepsR vs
  | r + 1, v :: vs => false :: List.replicate (v + 1) true ++ sepsM r vs

def incr : Nat → List Nat → List Nat
  | _, [] => []
  | 0, v :: vs => (v + 1) :: vs
  | r + 1, v :: vs => v :: incr r vs

def decr : Nat → List Nat → List Nat
  | _, [] => []
  | 0, v :: vs => (v - 1) :: vs
  | r + 1, v :: vs => v :: decr r vs

inductive Eff where
  | none
  | inc (r : Nat)
  | dec (r : Nat)
  deriving DecidableEq, Repr

inductive BoxSt where
  | plain (e : Eff)
  | mark (r : Nat)
  deriving DecidableEq, Repr

def boxList : BoxSt → List Nat → List Bool
  | .plain .none, vs => sepsR vs
  | .plain (.inc r), vs => sepsR (incr r vs ++ [1])
  | .plain (.dec r), vs => sepsR (decr r vs)
  | .mark r, vs => sepsM r vs

/-- A decnz branch assumption: `some (r, true)` means register `r` is zero. -/
abbrev Branch := Option (Nat × Bool)

def Valid (br : Branch) (vs : List Nat) : Prop :=
  10 ≤ vs.length ∧
    match br with
    | none => True
    | some (r, z) => if z then vs.getD r 0 = 0 else vs.getD r 0 ≠ 0

/-! ## The box oracle, numbered as in the frozen K230 table. -/

/-- The skip chain: state `sk j` crosses register `j`'s block on its way to the start of the file. -/
def skList : List Nat := [51, 36, 25, 48, 32, 33, 22, 55, 60]

def sk (j : Nat) : Nat := skList.getD j 0

/-- Which register a skip-chain state is about to mark (51 → 0, 36 → 1, …, 60 → 8). -/
def skipTarget (q : Nat) : Option Nat := (List.range 9).find? fun j => sk j == q

theorem skipTarget_sk {q r : Nat} (h : skipTarget q = some r) : q = sk r ∧ r < 9 := by
  have h' : (List.range 9).find? (fun j => sk j == q) = some r := h
  have e : (sk r == q) = true := List.find?_some (p := fun j => sk j == q) h'
  exact ⟨(beq_iff_eq.mp e).symm, List.mem_range.mp (List.mem_of_find?_eq_some h')⟩

def markExit (r : Nat) : Nat := if r = 0 then 1 else 3

/-- A positive decrement moves the file boundary one cell right (`extra = true`). -/
def oracle (q : Nat) (br : Branch) : BoxSt → Option (Nat × BoxSt × Bool)
  | .plain .none => (skipTarget q).map fun r => (markExit r, .mark r, false)
  | .mark r =>
      if r < 9 then
        if q = 64 then some (40, .plain (.inc r), false)
        else if q = 0 then
          match br with
          | some (r', z) =>
              if r = r' then (if z then some (97, .plain .none, false) else some (40, .plain (.dec r), true))
              else none
          | none => none
        else none
      else none
  | _ => none

/-! ## Segments and symbolic configurations -/

inductive Seg where
  | bit (b : Bool)
  | run (b : Bool) (a c : Nat)
  | box (x : BoxSt)
  deriving DecidableEq, Repr

def segList (n : Nat) (vs : List Nat) : Seg → List Bool
  | .bit b => [b]
  | .run b a c => List.replicate (a * n + c) b
  | .box x => boxList x vs

def flat (n : Nat) (vs : List Nat) (s : List Seg) : List Bool := s.flatMap (segList n vs)

/-- `(state, head on the left list?, left, right)`. -/
abbrev SConf := Nat × Bool × List Seg × List Seg

def conc (n : Nat) (vs : List Nat) : SConf → Conf
  | (q, true, l, r) => zl q (flat n vs l) (flat n vs r)
  | (q, false, l, r) => zc q (flat n vs l) (flat n vs r)

def peelLeft (q : Nat) (b : Bool) (a c : Nat) (l r : List Seg) : Option (SConf × Bool) :=
  match c, a with
  | c + 1, _ => some ((q, true, .bit b :: .run b a c :: l, r), false)
  | 0, 0 => some ((q, true, l, r), false)
  | 0, _ + 1 => none

def peelRight (q : Nat) (b : Bool) (a c : Nat) (l r : List Seg) : Option (SConf × Bool) :=
  match c, a with
  | c + 1, _ => some ((q, false, l, .bit b :: .run b a c :: r), false)
  | 0, 0 => some ((q, false, l, r), false)
  | 0, _ + 1 => none

/-- One abstract step; the boolean says that at least one machine step was taken. -/
def sstep (M : TMN) (br : Branch) : SConf → Option (SConf × Bool)
  | (q, true, [], r) => some ((q, false, [], .bit false :: r), false)
  | (q, true, .bit x :: l, r) => some ((q, false, l, .bit x :: r), false)
  | (q, true, .run b a c :: l, r) =>
      match M q b with
      | some (w, false, q2) => if q2 = q then some ((q, true, l, .run w a c :: r), false)
                               else peelLeft q b a c l r
      | _ => peelLeft q b a c l r
  | (_, true, .box _ :: _, _) => none
  | (_, false, _, []) => none
  | (q, false, l, .bit x :: r) =>
      match M q x with
      | some (w, true, q2) => some ((q2, false, .bit w :: l, r), true)
      | some (w, false, q2) => some ((q2, true, l, .bit w :: r), true)
      | none => none
  | (q, false, l, .run b a c :: r) =>
      match M q b with
      | some (w, true, q2) => if q2 = q then some ((q, false, .run w a c :: l, r), false)
                              else peelRight q b a c l r
      | _ => peelRight q b a c l r
  | (q, false, l, [.box x]) =>
      match oracle q br x with
      | some (q2, x2, extra) => some ((q2, true, (if extra then .bit true :: l else l), [.box x2]), false)
      | none =>
          match M q false with
          | some (false, false, q2) => some ((q2, true, l, [.box x]), true)
          | _ => none
  | (_, false, _, .box _ :: _ :: _) => none

def execWith (next : SConf → Option (SConf × Bool)) (tgt : SConf → Bool) : Nat → SConf → Bool → Option SConf
  | 0, _, _ => none
  | f + 1, s, moved =>
      if moved && tgt s then some s
      else match next s with
        | none => none
        | some (s', m) => execWith next tgt f s' (moved || m)

/-- The original symbolic executor, with exactly its original step function. -/
def exec (M : TMN) (br : Branch) (tgt : SConf → Bool) :
    Nat → SConf → Bool → Option SConf := execWith (sstep M br) tgt

/-! ## Basic facts -/

theorem flat_cons (n : Nat) (vs : List Nat) (x : Seg) (s : List Seg) :
    flat n vs (x :: s) = segList n vs x ++ flat n vs s := by simp [flat]

theorem flat_nil (n : Nat) (vs : List Nat) : flat n vs [] = [] := rfl

theorem rep_succ (x : Bool) (a n c : Nat) :
    List.replicate (a * n + (c + 1)) x = x :: List.replicate (a * n + c) x := by
  rw [← Nat.add_assoc, List.replicate_succ]

theorem sepsR_head {vs : List Nat} (h : vs ≠ []) : ∃ t, sepsR vs = false :: t := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs => exact ⟨_, by rw [sepsR, List.flatMap_cons, List.cons_append]⟩

theorem incr_ne_nil {r : Nat} {vs : List Nat} (h : vs ≠ []) : incr r vs ≠ [] := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs => cases r <;> simp [incr]

theorem decr_ne_nil {r : Nat} {vs : List Nat} (h : vs ≠ []) : decr r vs ≠ [] := by
  cases vs with
  | nil => exact absurd rfl h
  | cons v vs => cases r <;> simp [decr]

theorem box_head (x : BoxSt) {vs : List Nat} (h : vs ≠ []) : ∃ t, boxList x vs = false :: t := by
  cases x with
  | plain e =>
      cases e with
      | none => exact sepsR_head h
      | inc r => exact sepsR_head (by simp)
      | dec r => exact sepsR_head (decr_ne_nil h)
  | mark r =>
      cases vs with
      | nil => exact absurd rfl h
      | cons v vs => cases r <;> exact ⟨_, rfl⟩

/-! ## Soundness, relative to the four register lemmas -/

/-- The generic register-file lemmas of the engine (proved separately, by induction on the file). -/
structure BoxLemmas (M : TMN) : Prop where
  mark : ∀ q r l vs, skipTarget q = some r → 10 ≤ vs.length →
    Reach M (zc q l (sepsR vs)) (zl (markExit r) l (sepsM r vs))
  inc : ∀ r l vs, r < 9 → 10 ≤ vs.length →
    Reach M (zc 64 l (sepsM r vs)) (zl 40 l (sepsR (incr r vs ++ [1])))
  dec0 : ∀ r l vs, r < 9 → 10 ≤ vs.length → vs.getD r 0 = 0 →
    Reach M (zc 0 l (sepsM r vs)) (zl 97 l (sepsR vs))
  decp : ∀ r l vs, r < 9 → 10 ≤ vs.length → vs.getD r 0 ≠ 0 →
    Reach M (zc 0 l (sepsM r vs)) (zl 40 (true :: l) (sepsR (decr r vs)))

section Sound

variable {M : TMN} (B : BoxLemmas M)
include B

theorem oracle_sound {q : Nat} {br : Branch} {x x' : BoxSt} {q' : Nat} {extra : Bool}
    {vs : List Nat} (l : List Bool) (ho : oracle q br x = some (q', x', extra)) (hv : Valid br vs) :
    Reach M (zc q l (boxList x vs)) (zl q' (if extra then true :: l else l) (boxList x' vs)) := by
  obtain ⟨hlen, hbr⟩ := hv
  cases x with
  | plain e =>
      cases e with
      | none =>
          simp only [oracle, Option.map_eq_some_iff, Prod.mk.injEq] at ho
          obtain ⟨r, hr, rfl, rfl, rfl⟩ := ho
          exact B.mark q r l vs hr hlen
      | inc _ | dec _ => simp [oracle] at ho
  | mark r =>
      simp only [oracle] at ho
      by_cases h9 : r < 9
      · simp only [h9, if_true] at ho
        by_cases h64 : q = 64
        · subst h64
          simp only [if_true, Option.some.injEq, Prod.mk.injEq] at ho
          obtain ⟨rfl, rfl, rfl⟩ := ho
          exact B.inc r l vs h9 hlen
        · simp only [h64, if_false] at ho
          by_cases h0 : q = 0
          · subst h0
            simp only [if_true] at ho
            rcases br with _ | ⟨r', z⟩
            · simp at ho
            · by_cases hrr : r = r'
              · subst hrr
                simp only [if_true] at ho
                cases z with
                | true =>
                    simp only [if_true, Option.some.injEq, Prod.mk.injEq] at ho
                    obtain ⟨rfl, rfl, rfl⟩ := ho
                    exact B.dec0 r l vs h9 hlen (by simpa using hbr)
                | false =>
                    simp only [Bool.false_eq_true, if_false, Option.some.injEq, Prod.mk.injEq] at ho
                    obtain ⟨rfl, rfl, rfl⟩ := ho
                    exact B.decp r l vs h9 hlen (by simpa using hbr)
              · simp [hrr] at ho
          · simp [h0] at ho
      · simp [h9] at ho

omit B in
theorem peelLeft_sound {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {s' : SConf} {m : Bool}
    (n : Nat) (vs : List Nat) (h : peelLeft q b a c l r = some (s', m)) :
    m = false ∧ conc n vs (q, true, .run b a c :: l, r) = conc n vs s' := by
  unfold peelLeft at h
  split at h
  · cases h
    refine ⟨rfl, ?_⟩
    simp only [conc, flat_cons, segList, rep_succ, List.cons_append, List.nil_append]
  · cases h
    refine ⟨rfl, ?_⟩
    simp [conc, flat_cons, segList]
  · simp at h

omit B in
theorem peelRight_sound {q : Nat} {b : Bool} {a c : Nat} {l r : List Seg} {s' : SConf} {m : Bool}
    (n : Nat) (vs : List Nat) (h : peelRight q b a c l r = some (s', m)) :
    m = false ∧ conc n vs (q, false, l, .run b a c :: r) = conc n vs s' := by
  unfold peelRight at h
  split at h
  · cases h
    refine ⟨rfl, ?_⟩
    simp only [conc, flat_cons, segList, rep_succ, List.cons_append, List.nil_append]
  · cases h
    refine ⟨rfl, ?_⟩
    simp [conc, flat_cons, segList]
  · simp at h

/-- What one abstract step guarantees. -/
def StepOk (M : TMN) (n : Nat) (vs : List Nat) (s s' : SConf) (m : Bool) : Prop :=
  Reach M (conc n vs s) (conc n vs s') ∧ (m = true → Reach1 M (conc n vs s) (conc n vs s'))

omit B in
theorem stepOk_eq {n : Nat} {vs : List Nat} {s s' : SConf} (h : conc n vs s = conc n vs s') :
    StepOk M n vs s s' false :=
  ⟨Reach.of_eq h, fun h => by cases h⟩

omit B in
theorem stepOk_one {n : Nat} {vs : List Nat} {s s' : SConf}
    (h : step M (conc n vs s) = some (conc n vs s')) : StepOk M n vs s s' true :=
  ⟨Reach.of_step h, fun _ => Reach1.of_step h⟩

theorem sstep_sound {br : Branch} {s s' : SConf} {m : Bool} (n : Nat) {vs : List Nat}
    (h : sstep M br s = some (s', m)) (hv : Valid br vs) : StepOk M n vs s s' m := by
  obtain ⟨q, onl, l, r⟩ := s
  cases onl with
  | true =>
      cases l with
      | nil =>
          simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact stepOk_eq (by simp [conc, flat_cons, flat_nil, segList, zl])
      | cons x l =>
          cases x with
          | bit x =>
              simp only [sstep, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact stepOk_eq (by simp [conc, flat_cons, segList, zl])
          | box x => simp [sstep] at h
          | run b a c =>
              have hp : ∀ {s'' : SConf} {m' : Bool}, peelLeft q b a c l r = some (s'', m') →
                  StepOk M n vs (q, true, .run b a c :: l, r) s'' m' := fun hp => by
                obtain ⟨rfl, e⟩ := peelLeft_sound n vs hp
                exact stepOk_eq e
              simp only [sstep] at h
              split at h
              · rename_i w q2 hm
                split at h
                · rename_i hq
                  subst hq
                  cases h
                  refine ⟨?_, fun h => by cases h⟩
                  simp only [conc, flat_cons, segList]
                  exact scanL hm _ _ _
                · exact hp h
              · exact hp h
  | false =>
      cases r with
      | nil => simp [sstep] at h
      | cons x r =>
          cases x with
          | bit x =>
              simp only [sstep] at h
              split at h
              · rename_i w q2 hm
                cases h
                apply stepOk_one
                simp only [conc, flat_cons, segList, List.singleton_append]
                exact zR hm
              · rename_i w q2 hm
                cases h
                apply stepOk_one
                simp only [conc, flat_cons, segList, List.singleton_append]
                exact zL hm
              · simp at h
          | run b a c =>
              have hp : ∀ {s'' : SConf} {m' : Bool}, peelRight q b a c l r = some (s'', m') →
                  StepOk M n vs (q, false, l, .run b a c :: r) s'' m' := fun hp => by
                obtain ⟨rfl, e⟩ := peelRight_sound n vs hp
                exact stepOk_eq e
              simp only [sstep] at h
              split at h
              · rename_i w q2 hm
                split at h
                · rename_i hq
                  subst hq
                  cases h
                  refine ⟨?_, fun h => by cases h⟩
                  simp only [conc, flat_cons, segList]
                  exact scanR hm _ _ _
                · exact hp h
              · exact hp h
          | box x =>
              cases r with
              | cons y r => simp [sstep] at h
              | nil =>
                  simp only [sstep] at h
                  split at h
                  · rename_i q2 x2 extra ho
                    cases h
                    refine ⟨?_, fun h => by cases h⟩
                    have := oracle_sound B (flat n vs l) ho hv
                    cases extra <;>
                      simpa [conc, flat_cons, flat_nil, segList] using this
                  · split at h
                    · rename_i q2 hm
                      cases h
                      apply stepOk_one
                      obtain ⟨t, ht⟩ := box_head x (vs := vs) (fun e => by simpa [e] using hv.1)
                      simp only [conc, flat_cons, flat_nil, segList, List.append_nil, ht]
                      exact zL hm
                    · simp at h

omit B in
theorem execWith_sound {next : SConf → Option (SConf × Bool)} {tgt : SConf → Bool}
    (n : Nat) (vs : List Nat)
    (hnext : ∀ s t m, next s = some (t, m) → StepOk M n vs s t m) :
    ∀ (f : Nat) (s : SConf) (m0 : Bool) (s' : SConf), execWith next tgt f s m0 = some s' →
      tgt s' = true ∧ Reach M (conc n vs s) (conc n vs s') ∧
        (m0 = false → Reach1 M (conc n vs s) (conc n vs s'))
  | 0, _, _, _, h => by simp [execWith] at h
  | f + 1, s, m0, s', h => by
      simp only [execWith] at h
      split at h
      · rename_i ht
        cases h
        simp only [Bool.and_eq_true] at ht
        refine ⟨ht.2, Reach.refl M _, fun hm => by simp [hm] at ht⟩
      · split at h
        · simp at h
        · rename_i s1 m hs
          obtain ⟨hg, e1, p1⟩ := execWith_sound n vs hnext f s1 (m0 || m) s' h
          obtain ⟨e0, p0⟩ := hnext s s1 m hs
          refine ⟨hg, e0.trans e1, fun hm0 => ?_⟩
          subst hm0
          cases m with
          | true => exact (p0 rfl).trans_reach e1
          | false => exact e0.trans_reach1 (p1 rfl)

/-- The old theorem is an instance of the single generic executor induction. -/
theorem exec_sound {br : Branch} {tgt : SConf → Bool} (n : Nat) {vs : List Nat} (hv : Valid br vs) :
    ∀ (f : Nat) (s : SConf) (m0 : Bool) (s' : SConf), exec M br tgt f s m0 = some s' →
      tgt s' = true ∧ Reach M (conc n vs s) (conc n vs s') ∧
        (m0 = false → Reach1 M (conc n vs s) (conc n vs s')) :=
  execWith_sound n vs (fun _ _ _ h => sstep_sound B n h hv)

end Sound

/-! ## Normal forms of segment lists, for comparing final configurations -/

inductive Tok where
  | run (b : Bool) (a c : Nat)
  | box (x : BoxSt)
  deriving DecidableEq, Repr

def tokList (n : Nat) (vs : List Nat) : Tok → List Bool
  | .run b a c => List.replicate (a * n + c) b
  | .box x => boxList x vs

def flatT (n : Nat) (vs : List Nat) (ts : List Tok) : List Bool := ts.flatMap (tokList n vs)

def tokOf : Seg → Tok
  | .bit b => .run b 0 1
  | .run b a c => .run b a c
  | .box x => .box x

def push (t : Tok) (ts : List Tok) : List Tok :=
  match t with
  | .run _ 0 0 => ts
  | .run b a c =>
      match ts with
      | .run b' a' c' :: ts' => if b = b' then .run b (a + a') (c + c') :: ts' else t :: ts
      | _ => t :: ts
  | .box _ => t :: ts

def norm (s : List Seg) : List Tok := s.foldr (fun x ts => push (tokOf x) ts) []

/-- The left side may end in blanks, which `trim` discards. -/
def normL (s : List Seg) : List Tok :=
  match (norm s).reverse with
  | .run false _ _ :: t => t.reverse
  | t => t.reverse

def sMatches (s e : SConf) : Bool :=
  let (q, onl, l, r) := s
  let (q', onl', l', r') := e
  q == q' && onl == onl' && norm r == norm r' && normL l == normL l'

theorem flatT_push (n : Nat) (vs : List Nat) (t : Tok) (ts : List Tok) :
    flatT n vs (push t ts) = tokList n vs t ++ flatT n vs ts := by
  cases t with
  | box x => simp [push, flatT]
  | run b a c =>
      have g : flatT n vs (match ts with
          | .run b' a' c' :: ts' => if b = b' then .run b (a + a') (c + c') :: ts' else .run b a c :: ts
          | _ => .run b a c :: ts) = tokList n vs (.run b a c) ++ flatT n vs ts := by
        match ts with
        | [] | .box _ :: _ => simp [flatT]
        | .run b' a' c' :: ts' =>
            by_cases hb : b = b'
            · subst hb
              simp only [if_true, flatT, List.flatMap_cons, tokList, ← List.append_assoc,
                List.replicate_append_replicate]
              congr 2; simp only [Nat.add_mul]
              generalize a * n = x; generalize a' * n = y; omega
            · simp [hb, flatT]
      match a, c with
      | 0, 0 => simp [push, tokList]
      | 0, _ + 1 | _ + 1, _ => exact g

theorem flatT_norm (n : Nat) (vs : List Nat) (s : List Seg) : flatT n vs (norm s) = flat n vs s := by
  induction s with
  | nil => rfl
  | cons x s ih =>
      simp only [norm, List.foldr_cons] at ih ⊢
      rw [flatT_push, ih, flat_cons]
      cases x <;> simp [tokOf, tokList, segList]

theorem flatT_append (n : Nat) (vs : List Nat) (a b : List Tok) :
    flatT n vs (a ++ b) = flatT n vs a ++ flatT n vs b := by simp [flatT]

theorem normL_spec (n : Nat) (vs : List Nat) (s : List Seg) :
    ∃ m, flat n vs s = flatT n vs (normL s) ++ List.replicate m false := by
  rw [← flatT_norm]
  unfold normL
  generalize hR : (norm s).reverse = R
  rw [show norm s = R.reverse by rw [← hR, List.reverse_reverse]]
  match R with
  | [] | .run true _ _ :: _ | .box _ :: _ => exact ⟨0, by simp⟩
  | .run false a c :: t => exact ⟨a * n + c, by simp [flatT, tokList]⟩

theorem sMatches_conc {s e : SConf} (n : Nat) (vs : List Nat) (h : sMatches s e = true) :
    conc n vs s = conc n vs e := by
  obtain ⟨q, onl, l, r⟩ := s
  obtain ⟨q', onl', l', r'⟩ := e
  simp only [sMatches, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨rfl, rfl⟩, hr⟩, hl⟩ := h
  have er : flat n vs r = flat n vs r' := by rw [← flatT_norm, hr, flatT_norm]
  obtain ⟨m1, h1⟩ := normL_spec n vs l
  obtain ⟨m2, h2⟩ := normL_spec n vs l'
  cases onl <;> simp only [conc, er, h1, h2, hl, zc_padl, zl_padl]

end SetTheory.BusyBeaver.ZFC.KRuntimeCore
