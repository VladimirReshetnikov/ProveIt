import DiophantineConsistency.CantorRepresentation
import DiophantineConsistency.DirectScalarEnumerator
import DiophantineConsistency.GraphBranching
import DiophantineConsistency.ScalarPRRepresentation

/-!
# A direct arithmetic graph for the literal refutation test

Source arithmetic is represented directly, including quadratic Cantor
pairing and inverse projections. Only the outer bounded iteration uses a
beta-function trace; elementary arithmetic is not expanded into recursive
program traces.
-/

namespace DiophantineConsistency.DirectGraphEnumerator

open SetTheory SetTheory.BusyBeaver.ZFC EnumPerm Code254 KCode222
open DirectEnumerator

attribute [local irreducible] Nat.unpair

abbrev R (f : ℕ → ℕ) := GraphRep (fun v : Fin 1 → ℕ => f (v 0))

def ofEq {f g : ℕ → ℕ} (r : R f) (h : ∀ n, f n = g n) : R g :=
  r.ofIff (fun v => by change v none = f (v (some 0)) ↔ v none = g (v (some 0)); rw [h])

def identity : R id := GraphRep.coordinate 0
def constant (n : ℕ) : R (fun _ => n) := GraphRep.constant n

def comp {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => f (g n)) :=
  GraphRep.compose r (fun _ => s)

def successor {f : ℕ → ℕ} (r : R f) : R (fun n => f n + 1) :=
  r.add (GraphRep.constant 1)

def add {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => f n + g n) := r.add s
def mul {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => f n * g n) := r.mul s
def sub {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => f n - g n) := r.sub s
def pair {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => Nat.pair (f n) (g n)) := r.pair s

def naturalLeft : R (fun n => n.unpair.1) := (GraphRep.coordinate 0).unpairLeft
def naturalRight : R (fun n => n.unpair.2) := (GraphRep.coordinate 0).unpairRight

def ifEq {f g h k : ℕ → ℕ} (r : R f) (s : R g) (t : R h) (u : R k) :
    R (fun n => if f n = g n then h n else k n) := r.ifEq s t u

def ifZero {f g h : ℕ → ℕ} (r : R f) (s : R g) (t : R h) :
    R (fun n => if f n = 0 then g n else h n) := r.ifZero s t

def cantorPair {f g : ℕ → ℕ} (r : R f) (s : R g) : R (fun n => P (f n) (g n)) :=
  CantorRepresentation.pair r s

def unpairLeft {f : ℕ → ℕ} (r : R f) : R (fun n => (unP (f n)).1) :=
  CantorRepresentation.left r

def unpairRight {f : ℕ → ℕ} (r : R f) : R (fun n => (unP (f n)).2) :=
  CantorRepresentation.right r

private def equalityGraphs {σ : Type*} {f g : (σ → ℕ) → ℕ}
    (r : GraphRep f) (s : GraphRep g) : Rep σ (fun v => f v = g v) := by
  let arguments : ∀ i : Fin 2, GraphRep (![f, g] i) :=
    Fin.cases r (Fin.cases s (fun i => Fin.elim0 i))
  exact (Rep.compose
    (PellRepresentation.NaturalRelation.equality
      (.var (0 : Fin 2)) (.var 1)) arguments).ofIff (fun _ => Iff.rfl)

/-- A trace specialized to unary iteration, with no unused scalar parameter
or pairing/unpairing of a primitive-recursion step argument. -/
def iterate {f : ℕ → ℕ} (p : R f) (initial : ℕ) :
    R (fun n => n.rec initial (fun _ acc => f acc)) := by
  let V := Option (Fin 1) ⊕ Fin 2
  let a : GraphRep (fun v : V → ℕ => v (Sum.inr 0)) := GraphRep.coordinate (Sum.inr 0)
  let b : GraphRep (fun v : V → ℕ => v (Sum.inr 1)) := GraphRep.coordinate (Sum.inr 1)
  let k : GraphRep (fun v : V → ℕ => v (Sum.inl (some 0))) := GraphRep.coordinate (Sum.inl (some 0))
  let out : GraphRep (fun v : V → ℕ => v (Sum.inl none)) := GraphRep.coordinate (Sum.inl none)
  let first := equalityGraphs (ScalarPRRepresentation.entryGraph a b (GraphRep.constant 0))
    (GraphRep.constant initial)
  let last := equalityGraphs (ScalarPRRepresentation.entryGraph a b k) out
  let i : GraphRep (fun v : Option V → ℕ => v none) := GraphRep.coordinate none
  let aa := a.reindex some
  let bb := b.reindex some
  let before := ScalarPRRepresentation.entryGraph aa bb i
  let after := ScalarPRRepresentation.entryGraph aa bb (i.add (GraphRep.constant 1))
  let next := GraphRep.compose p (fun _ : Fin 1 => before)
  let transitions := (equalityGraphs after next).boundedForall (Sum.inl (some 0))
  refine ((first.conjunction (last.conjunction transitions)).existsBlock).ofIff ?_
  intro v
  change (∃ t : Fin 2 → ℕ,
    ScalarPRRepresentation.entry (t 0) (t 1) 0 = initial ∧
    ScalarPRRepresentation.entry (t 0) (t 1) (v (some 0)) = v none ∧
    ∀ i < v (some 0), ScalarPRRepresentation.entry (t 0) (t 1) (i + 1) =
      f (ScalarPRRepresentation.entry (t 0) (t 1) i)) ↔ _
  simpa only [Nat.unpair_pair, Function.comp_apply] using
    (ScalarPRRepresentation.trace_iff (fun _ => initial)
      (fun n => f n.unpair.2.unpair.2) 0 (v (some 0)) (v none)).symm

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

def gated {a b c : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) :
    R (fun n => gate (a n) (b n) (c n)) := by
  let body := negation (implication
    (implication (membership ha hb) (universal hc (membership ha hb)))
    (universal hc (implication (closure ha hb hc hc) (negation (request hb hc hc)))))
  refine ofEq (ifEq hc ha (constant 0) (ifEq hc hb (constant 0) body)) ?_
  intro n
  by_cases hca : c n = a n <;> by_cases hcb : c n = b n <;>
    simp [gate, bundle222, vrel, nks, hca, hcb]

def stack {a h b c u t w : ℕ → ℕ} (ha : R a) (hh : R h) (hb : R b) (hc : R c)
    (hu : R u) (ht : R t) (hw : R w) :
    R (fun n => axStack (a n) (h n) (b n) (c n) (u n) (t n) (w n)) :=
  cantorPair (row1 ha hb) (cantorPair (row2 ha hb hc) (cantorPair (row3 ha hb hc)
    (cantorPair (row4 ha hb hc) (cantorPair (row5 ha hb hc) (cantorPair (row6 ha hc)
    (cantorPair (growth ha hb hc) (cantorPair (row8 ha hb hc hu)
    (cantorPair (universal hu hh) (cantorPair ht hw)))))))))

def pl : R (fun n => (decodeState n).pl) := naturalLeft
def np : R (fun n => (decodeState n).np) := comp naturalLeft naturalRight
def tw : R (fun n => (decodeState n).tw) := comp naturalLeft (comp naturalRight naturalRight)
def ws : R (fun n => (decodeState n).ws) :=
  comp naturalLeft (comp naturalRight (comp naturalRight naturalRight))
def depth : R (fun n => (decodeState n).d) :=
  comp naturalLeft (comp naturalRight (comp naturalRight (comp naturalRight naturalRight)))
def cache : R (fun n => (decodeState n).h) :=
  comp naturalRight (comp naturalRight (comp naturalRight (comp naturalRight naturalRight)))

def state {a b c d e f : ℕ → ℕ} (ha : R a) (hb : R b) (hc : R c) (hd : R d)
    (he : R e) (hf : R f) : R (fun n => encodeState ⟨a n, b n, c n, d n, e n, f n⟩) :=
  ha.pair (hb.pair (hc.pair (hd.pair (he.pair hf))))

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
    (ifEq cache (constant 1) (constant 0)
      (successor (state rest hb tw (unpairRight ws) depth (unpairLeft ws))))
    (ifEq tag (constant 1)
      (successor (state rest hb cache (cantorPair tw ws) depth cache))
      (ifEq tag (constant 2)
        (ifEq (implication tw dv) cache
          (successor (state y hb dv (cantorPair (constant 0) ws) dv (constant 0)))
          (successor (state y hb (constant 0) ws dv (constant 0))))
        (successor (state (unpairRight y) hb (gated av bv cv)
          (stack av cache bv cv depth tw ws) (constant 0) (constant 0)))))
  refine ofEq p ?_
  intro n
  dsimp only [rawStep]
  split_ifs <;> rfl

def enumStepProgram : R (fun n => encodeOption (enumStep (decodeState n))) := by
  let newPl := ifEq pl (constant 0) np (sub pl (constant 1))
  let newNp := ifEq pl (constant 0) (successor np) np
  refine ofEq (rawStepProgram newPl newNp) ?_
  intro n
  simp only [enumStep, fetch]
  split <;> simp_all only [rawStep_eq]

def optionStepProgram : R optionStep :=
  ifZero identity (constant 0) (comp enumStepProgram (sub identity (constant 1)))

@[simp] theorem optionStep_encode (o : Option St) :
    optionStep (encodeOption o) = encodeOption (o.bind enumStep) := by
  cases o <;> simp [optionStep, encodeOption]

def boundedRunProgram : R (fun n => encodeOption (boundedRun n initialState)) := by
  refine ofEq (iterate optionStepProgram (encodeOption (some initialState))) ?_
  exact DirectEnumerator.boundedRun_rec

/-- Closed code data for the exact bounded halting test used by the ZFC bridge. -/
def program : R haltingTest := by
  refine ofEq (ifZero boundedRunProgram (constant 1) (constant 0)) ?_
  intro n
  cases he : boundedRun n initialState <;> simp [encodeOption, haltingTest, he]

#print axioms program

end DiophantineConsistency.DirectGraphEnumerator
