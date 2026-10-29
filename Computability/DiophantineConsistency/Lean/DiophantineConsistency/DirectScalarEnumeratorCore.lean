import DiophantineConsistency.DirectScalarArithmetic
import DiophantineConsistency.EnumeratorSemantics

/-!
# A supplied scalar program for the literal proof enumerator

This file builds the arithmetic program directly from the source semantics.
States are represented by six nested natural-pair coordinates; option states
use zero for `none` and a successor for `some`. No primitive-recursiveness
proof is reified and no existential witness is selected.
-/

namespace DiophantineConsistency.DirectEnumerator

open SetTheory SetTheory.BusyBeaver.ZFC EnumPerm Code254 KCode222
open ScalarPRCode DirectScalar

attribute [local irreducible] Nat.unpair

def triangular : R Cantor.tri := by
  let p := recursion (g := fun _ i acc => acc + i + 1) Realizes.zero
    (successor (add (Realizes.right.comp Realizes.right) (Realizes.left.comp Realizes.right)))
  refine (p.comp (Realizes.zero.pair identity)).ofEq ?_
  intro n
  simp only [Nat.unpair_pair]
  induction n <;> simp_all [Cantor.tri]

def cantorPairCore : R (fun n => P n.unpair.1 n.unpair.2) :=
  add Realizes.right (triangular.comp (add Realizes.left Realizes.right))

def cantorPair {a b : ℕ → ℕ} (ha : R a) (hb : R b) : R (fun n => P (a n) (b n)) :=
  (cantorPairCore.comp (ha.pair hb)).ofEq (fun _ => by simp)

def cantorStep (n : ℕ) : ℕ :=
    if n.unpair.1 = 0 then Nat.pair (n.unpair.2 + 1) 0
    else Nat.pair (n.unpair.1 - 1) (n.unpair.2 + 1)

def cantorWalkStep : R cantorStep :=
  ifZero Realizes.left ((successor Realizes.right).pair Realizes.zero)
    ((sub Realizes.left (constant 1)).pair (successor Realizes.right))

def cantorUnpair : R (fun n => Nat.pair (unP n).1 (unP n).2) := by
  refine (iterate cantorWalkStep 0).ofEq ?_
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    change cantorStep (Nat.rec (motive := fun _ => ℕ) 0 (fun _ acc => cantorStep acc) n) = _
    rw [ih]
    simp only [cantorStep, Nat.unpair_pair]
    cases he : unP n with
    | mk a b =>
      cases a <;> simp [unP, Cantor.ofNat, he]

def unpairLeft {a : ℕ → ℕ} (ha : R a) : R (fun n => (unP (a n)).1) :=
  ((Realizes.left.comp cantorUnpair).comp ha).ofEq (fun _ => by simp)

def unpairRight {a : ℕ → ℕ} (ha : R a) : R (fun n => (unP (a n)).2) :=
  ((Realizes.right.comp cantorUnpair).comp ha).ofEq (fun _ => by simp)

def implication {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => wim (a n) (b n)) := mul (constant 4) (cantorPair ha hb)
def membership {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => wel (a n) (b n)) := successor (implication ha hb)
def universal {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => wal (a n) (b n)) := add (implication ha hb) (constant 2)
def equality {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => weq (a n) (b n)) := add (implication ha hb) (constant 3)
def negation {a : ℕ → ℕ} (ha : R a) : R (fun n => wn (a n)) :=
  implication ha (constant 1)
def existential {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => wex (a n) (b n)) := negation (universal ha (negation hb))

def row1 {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => rho1 (a n) (b n)) := existential ha (equality ha hb)
def row2 {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => rho2 (a n) (b n) (c n)) :=
  implication (universal ha (implication hb hc)) (implication (universal ha hb) (universal ha hc))
def row3 {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => rho3 (a n) (b n) (c n)) :=
  implication (equality ha hb) (implication (membership hc ha) (membership hc hb))
def row4 {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => rho4 (a n) (b n) (c n)) :=
  implication (universal ha (universal hb hc)) (universal hb (universal ha hc))
def row5 {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => rho5 (a n) (b n) (c n)) :=
  implication (equality hc ha) (implication (membership hc hb) (membership ha hb))
def row6 {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => rho6 (a n) (b n)) := implication (existential ha (universal ha hb)) hb
def growth {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => growG (a n) (b n) (c n)) :=
  implication (equality hc ha) (implication (equality hc hb)
    (universal (membership ha hb) (equality ha hb)))
def request {b k m : ℕ → ℕ} (hb : R b) (hk : R k) (hm : R m) :
    R (fun n => req (b n) (k n) (m n)) :=
  universal hb (implication hm (negation (universal hb
    (implication hm (negation (membership hb hk))))))
def closure {a b k m : ℕ → ℕ} (ha : R a) (hb : R b) (hk : R k) (hm : R m) :
    R (fun n => clos (a n) (b n) (k n) (m n)) :=
  universal hb (implication (membership hb hk) (negation (universal ha
    (implication hm (negation (universal ha (implication
      (universal hk (implication (membership hk ha) (membership hk hb)))
      (request hb hk hm))))))))
def row8 {a b c u : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) (hu : R u) :
    R (fun n => rho8 (a n) (b n) (c n) (u n)) :=
  implication (implication (implication hc hu) ha)
    (implication (implication ha hc) (implication hb hc))

def gatedBody {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => gate (a n) (b n) (c n)) := by
  let body := negation (implication
    (implication (membership ha hb) (universal hc (membership ha hb)))
    (universal hc (implication (closure ha hb hc hc) (negation (request hb hc hc)))))
  refine (ifEq hc ha Realizes.zero (ifEq hc hb Realizes.zero body)).ofEq ?_
  intro n
  by_cases hca : c n = a n <;> by_cases hcb : c n = b n <;>
    simp [gate, bundle222, vrel, nks, hca, hcb]

def gated {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => gate (a n) (b n) (c n)) :=
  ((gatedBody Realizes.left (Realizes.left.comp Realizes.right)
    (Realizes.right.comp Realizes.right)).comp (ha.pair (hb.pair hc))).ofEq
      (fun _ => by simp)

def stackBody {a h b c u t w : ℕ → ℕ} (ha : R a) (hh : R h) (hb : R b) (hc : R c)
    (hu : R u) (ht : R t) (hw : R w) :
    R (fun n => axStack (a n) (h n) (b n) (c n) (u n) (t n) (w n)) :=
  cantorPair (row1 ha hb) (cantorPair (row2 ha hb hc) (cantorPair (row3 ha hb hc)
    (cantorPair (row4 ha hb hc) (cantorPair (row5 ha hb hc) (cantorPair (row6 ha hc)
    (cantorPair (growth ha hb hc) (cantorPair (row8 ha hb hc hu)
    (cantorPair (universal hu hh) (cantorPair ht hw)))))))))

def stack {a h b c u t w : ℕ → ℕ} (ha : R a) (hh : R h) (hb : R b) (hc : R c)
    (hu : R u) (ht : R t) (hw : R w) :
    R (fun n => axStack (a n) (h n) (b n) (c n) (u n) (t n) (w n)) := by
  let r1 := Realizes.right
  let r2 := Realizes.right.comp r1
  let r3 := Realizes.right.comp r2
  let r4 := Realizes.right.comp r3
  let r5 := Realizes.right.comp r4
  let r6 := Realizes.right.comp r5
  let core := stackBody Realizes.left (Realizes.left.comp r1) (Realizes.left.comp r2)
    (Realizes.left.comp r3) (Realizes.left.comp r4) (Realizes.left.comp r5) r6
  exact (core.comp (ha.pair (hh.pair (hb.pair (hc.pair (hu.pair (ht.pair hw))))))).ofEq
    (fun _ => by simp)

def encodeState (s : St) : ℕ :=
  Nat.pair s.pl (Nat.pair s.np (Nat.pair s.tw (Nat.pair s.ws (Nat.pair s.d s.h))))
def decodeState (n : ℕ) : St :=
  ⟨n.unpair.1, n.unpair.2.unpair.1, n.unpair.2.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.2.unpair.2.unpair.1,
    n.unpair.2.unpair.2.unpair.2.unpair.2.unpair.2⟩

@[simp] theorem decode_encode (s : St) : decodeState (encodeState s) = s := by
  cases s; simp [encodeState, decodeState]

def encodeOption : Option St → ℕ
  | none => 0
  | some s => encodeState s + 1

def pl : R (fun n => (decodeState n).pl) := Realizes.left
def np : R (fun n => (decodeState n).np) := Realizes.left.comp Realizes.right
def tw : R (fun n => (decodeState n).tw) := Realizes.left.comp (Realizes.right.comp Realizes.right)
def ws : R (fun n => (decodeState n).ws) :=
  Realizes.left.comp (Realizes.right.comp (Realizes.right.comp Realizes.right))
def depth : R (fun n => (decodeState n).d) :=
  ⟨.comp .left (.comp .right (.comp .right (.comp .right .right))), fun _ => rfl⟩
def cache : R (fun n => (decodeState n).h) :=
  ⟨.comp .right (.comp .right (.comp .right (.comp .right .right))), fun _ => rfl⟩

def state {a b c d e f : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) (hd : R d)
    (he : R e) (hf : R f) : R (fun n => encodeState ⟨a n, b n, c n, d n, e n, f n⟩) :=
  ha.pair (hb.pair (hc.pair (hd.pair (he.pair hf))))

/-- Literal source step, preserving the arithmetic branch structure. -/
def rawStep (pl np : ℕ) (s : St) : Option St :=
  let tag := (unP pl).1
  let rest := (unP pl).2
  if tag = 0 then
    if s.h = 1 then none else
      some ⟨rest, np, s.tw, (unP s.ws).2, s.d, (unP s.ws).1⟩
  else if tag = 1 then some ⟨rest, np, s.h, P s.tw s.ws, s.d, s.h⟩
  else if tag = 2 then
    let d := s.d + (unP rest).1
    if wim s.tw d = s.h then some ⟨(unP rest).2, np, d, P 0 s.ws, d, 0⟩
    else some ⟨(unP rest).2, np, 0, s.ws, d, 0⟩
  else
    let c := tag - 3
    let a := s.d + (unP (unP rest).2).1
    let b := s.h + (unP rest).1
    some ⟨(unP (unP rest).2).2, np, gate a b c,
      axStack a s.h b c s.d s.tw s.ws, 0, 0⟩

theorem rawStep_eq (pl np : ℕ) (s : St) : rawStep pl np s = execAt pl np s := by
  unfold rawStep execAt EnumPerm.decode
  generalize unP pl = p
  rcases p with ⟨tag, rest⟩
  rcases s with ⟨pl0, np0, t, w, d, h⟩
  cases tag with
  | zero => simp [cstep, toW]; split <;> rfl
  | succ tag =>
      cases tag with
      | zero => rfl
      | succ tag =>
          cases tag with
          | zero => simp [cstep, toW]; split <;> rfl
          | succ tag => simp [cstep, toW]

def rawStepProgram {a b : ℕ → ℕ} (ha : R a) (hb : R b) :
    R (fun n => encodeOption (rawStep (a n) (b n) (decodeState n))) := by
  let tag := unpairLeft ha
  let rest := unpairRight ha
  let x := unpairLeft rest
  let y := unpairRight rest
  let av := add depth (unpairLeft y)
  let bv := add cache x
  let cv := sub tag (constant 3)
  let dv := add depth x
  let p := ifEq tag (constant 0)
    (ifEq cache (constant 1) Realizes.zero
      (successor (state rest hb tw (unpairRight ws) depth (unpairLeft ws))))
    (ifEq tag (constant 1)
      (successor (state rest hb cache (cantorPair tw ws) depth cache))
      (ifEq tag (constant 2)
        (ifEq (implication tw dv) cache
          (successor (state y hb dv (cantorPair Realizes.zero ws) dv Realizes.zero))
          (successor (state y hb Realizes.zero ws dv Realizes.zero)))
        (successor (state (unpairRight y) hb (gated av bv cv)
          (stack av cache bv cv depth tw ws) Realizes.zero Realizes.zero))))
  refine p.ofEq ?_
  intro n
  dsimp only [rawStep]
  split_ifs <;> rfl

def enumStepProgram : R (fun n => encodeOption (enumStep (decodeState n))) := by
  let newPl := ifEq pl (constant 0) np (sub pl (constant 1))
  let newNp := ifEq pl (constant 0) (successor np) np
  refine (rawStepProgram newPl newNp).ofEq ?_
  intro n
  simp only [enumStep, fetch]
  split <;> simp_all only [rawStep_eq]

def optionStep (n : ℕ) : ℕ :=
  if n = 0 then 0 else encodeOption (enumStep (decodeState (n - 1)))

def optionStepProgram : R optionStep :=
  ifZero identity Realizes.zero (enumStepProgram.comp (sub identity (constant 1)))

@[simp] theorem optionStep_encode (o : Option St) :
    optionStep (encodeOption o) = encodeOption (o.bind enumStep) := by
  cases o <;> simp [optionStep, encodeOption]

/-- The scalar iterator follows the literal bounded enumerator on every input. -/
theorem boundedRun_rec (n : ℕ) :
    Nat.rec (encodeOption (some initialState)) (fun _ acc => optionStep acc) n =
      encodeOption (boundedRun n initialState) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change optionStep (Nat.rec _ _ n) = _
    rw [ih, optionStep_encode]
    change _ = encodeOption ((fun o : Option St => o.bind enumStep)^[n + 1] (some initialState))
    rw [Function.iterate_succ_apply']
    rfl

def boundedRunProgram : R (fun n => encodeOption (boundedRun n initialState)) := by
  refine (iterate optionStepProgram (encodeOption (some initialState))).ofEq ?_
  exact boundedRun_rec

/-- Closed code data for the exact bounded halting test used by the ZFC bridge. -/
def program : ScalarPRCode.Realizes haltingTest := by
  refine (ifZero boundedRunProgram (constant 1) Realizes.zero).ofEq ?_
  intro n
  cases he : boundedRun n initialState <;> simp [encodeOption, haltingTest, he]

#print axioms program

end DiophantineConsistency.DirectEnumerator
