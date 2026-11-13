import Std.Tactic

/-!
A bounded proof-carrying stack invariant for the exact PA196 Cantor stack.
This is a standard-natural-number prerequisite, not a derivation in iPRA.
It handles the alias `pair 0 0 = 0` by ignoring certificate entries after
numeric underflow. No PA196 checker or machine theorem is assumed here.
-/
namespace PA196CertificateStack

variable (pair : Nat → Nat → Nat) (decode : Nat → Nat × Nat)
variable (decodePair : ∀ a b, decode (pair a b) = (a,b))
variable (decodeZero : decode 0 = (0,0))
variable (tailSmaller : ∀ w, w ≠ 0 → (decode w).2 < w)

def tail (decode : Nat → Nat × Nat) (w : Nat) := (decode w).2

def walk (decode : Nat → Nat × Nat) (w : Nat) : Nat → Nat
  | 0 => w
  | n+1 => tail decode (walk decode w n)

@[simp] theorem walk_zero (w : Nat) : walk decode w 0 = w := rfl
@[simp] theorem walk_succ (w n : Nat) : walk decode w (n+1) = walk decode (tail decode w) n := by
  induction n generalizing w with
  | zero => rfl
  | succ n ih =>
    change tail decode (walk decode w (n+1)) = tail decode (walk decode (tail decode w) n)
    rw [ih]

include decodeZero in
theorem walk_zero_stays (n : Nat) : walk decode 0 n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [walk, ih, tail, decodeZero]

include decodeZero tailSmaller in
theorem walk_vanishes (w n : Nat) (h : w ≤ n) : walk decode w n = 0 := by
  induction n generalizing w with
  | zero => simp only [walk]; omega
  | succ n ih =>
    by_cases hz : w = 0
    · subst w; exact walk_zero_stays decode decodeZero _
    · have ht : tail decode w < w := tailSmaller w hz
      rw [walk_succ]
      exact ih _ (by omega)

variable (cert : Nat → Nat → Prop) (truthProof : Nat)
variable (truthValid : cert truthProof 0)

/-- Only certificate entries at nonzero numeric-stack positions matter. -/
def Good (w p : Nat) : Prop :=
  ∀ i, walk decode w i ≠ 0 →
    cert (decode (walk decode p i)).1 (decode (walk decode w i)).1

/-- This bound makes the invariant suitable for a bounded representation. -/
def BoundedGood (w p : Nat) : Prop :=
  ∀ i < w, walk decode w i ≠ 0 →
    cert (decode (walk decode p i)).1 (decode (walk decode w i)).1

include decodeZero tailSmaller in
theorem good_iff_bounded (w p : Nat) :
    Good decode cert w p ↔ BoundedGood decode cert w p := by
  constructor
  · intro h i _ hi; exact h i hi
  · intro h i hi
    by_cases hlt : i < w
    · exact h i hlt hi
    · exact False.elim (hi (walk_vanishes decode decodeZero tailSmaller w i (by omega)))

include decodeZero in
theorem good_empty (p : Nat) : Good decode cert 0 p := by
  intro i hi
  exact False.elim (hi (walk_zero_stays decode decodeZero i))

include decodePair in
theorem good_push (w p a proof : Nat) (hw : Good decode cert w p) (hp : cert proof a) :
    Good decode cert (pair a w) (pair proof p) := by
  intro i hi
  cases i with
  | zero => simpa [decodePair] using hp
  | succ i =>
    rw [walk_succ, walk_succ]
    simp only [tail, decodePair]
    apply hw i
    simpa [walk_succ, tail, decodePair] using hi

/-- At numeric underflow, ignore ghost certificates and return truth. -/
def popProof (w p : Nat) : Nat × Nat :=
  if w = 0 then (truthProof,p) else ((decode p).1,(decode p).2)

include decodeZero truthValid in
theorem good_pop (w p : Nat) (hw : Good decode cert w p) :
    cert (popProof decode truthProof w p).1 (decode w).1 ∧
      Good decode cert (decode w).2 (popProof decode truthProof w p).2 := by
  by_cases hz : w = 0
  · subst w
    simpa [popProof, decodeZero] using And.intro truthValid (good_empty decode decodeZero cert p)
  · constructor
    · simpa [popProof, hz] using hw 0 hz
    · intro i hi
      have h := hw (i+1) (by simpa [walk_succ, tail] using hi)
      simpa [popProof, hz, walk_succ, tail] using h

include decodePair decodeZero tailSmaller in
theorem bounded_push (w p a proof : Nat)
    (hw : BoundedGood decode cert w p) (hp : cert proof a) :
    BoundedGood decode cert (pair a w) (pair proof p) := by
  apply (good_iff_bounded decode decodeZero tailSmaller cert _ _).mp
  exact good_push pair decode decodePair cert w p a proof
    ((good_iff_bounded decode decodeZero tailSmaller cert w p).mpr hw) hp

include decodeZero tailSmaller truthValid in
theorem bounded_pop (w p : Nat) (hw : BoundedGood decode cert w p) :
    cert (popProof decode truthProof w p).1 (decode w).1 ∧
      BoundedGood decode cert (decode w).2 (popProof decode truthProof w p).2 := by
  have h := good_pop decode decodeZero cert truthProof truthValid w p
    ((good_iff_bounded decode decodeZero tailSmaller cert w p).mpr hw)
  exact ⟨h.1, (good_iff_bounded decode decodeZero tailSmaller cert _ _).mp h.2⟩

end PA196CertificateStack

/- Exact definitions copied from PA196's M6/Source/Cantor.lean. -/
namespace PA196CertificateStack.Cantor

def triangle : Nat → Nat
  | 0 => 0
  | n+1 => triangle n + n + 1

def pair (a b : Nat) : Nat := triangle (a+b) + b

def advance (p : Nat × Nat) : Nat × Nat :=
  match p.1 with
  | 0 => (p.2 + 1, 0)
  | a+1 => (a, p.2 + 1)

def decode : Nat → Nat × Nat
  | 0 => (0,0)
  | n+1 => advance (decode n)

theorem triangle_strict_mono {s t : Nat} (h : s < t) : triangle s < triangle t := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases he : s = t
    · subst s; simp only [triangle]; omega
    · have hs : s < t := by omega
      have hm := ih hs
      simp only [triangle]
      omega

theorem pair_diagonal_lower (a b : Nat) : triangle (a+b) ≤ pair a b := by simp [pair]
theorem pair_diagonal_upper (a b : Nat) : pair a b < triangle (a+b+1) := by
  simp only [pair, triangle]
  omega

theorem pair_injective {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  have lo₁ := pair_diagonal_lower a b
  have hi₁ := pair_diagonal_upper a b
  have lo₂ := pair_diagonal_lower c d
  have hi₂ := pair_diagonal_upper c d
  have hs : a+b = c+d := by
    by_cases hab : a+b < c+d
    · have hle : triangle (a+b+1) ≤ triangle (c+d) := by
        by_cases he : a+b+1 = c+d
        · simp [he]
        · have hh := triangle_strict_mono (s := a+b+1) (t := c+d) (by omega)
          omega
      omega
    · by_cases hcd : c+d < a+b
      · have hle : triangle (c+d+1) ≤ triangle (a+b) := by
          by_cases he : c+d+1 = a+b
          · simp [he]
          · have hh := triangle_strict_mono (s := c+d+1) (t := a+b) (by omega)
            omega
        omega
      · omega
  simp only [pair, hs] at h
  constructor <;> omega

theorem pair_advance (p : Nat × Nat) : pair (advance p).1 (advance p).2 = pair p.1 p.2 + 1 := by
  rcases p with ⟨a,b⟩
  cases a with
  | zero => simp [advance, pair, triangle, Nat.add_assoc]
  | succ a => simp [advance, pair, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem pair_decode (n : Nat) : pair (decode n).1 (decode n).2 = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [decode, pair_advance, ih]

theorem decode_pair (a b : Nat) : decode (pair a b) = (a,b) := by
  have h := pair_injective (a := (decode (pair a b)).1) (b := (decode (pair a b)).2)
    (c := a) (d := b) (pair_decode (pair a b))
  exact Prod.ext h.1 h.2

theorem pair_tail_lt (a b : Nat) (h : pair a b ≠ 0) : b < pair a b := by
  have hsum : a + b ≠ 0 := by
    intro hzero
    have ha : a = 0 := by omega
    have hb : b = 0 := by omega
    simp [pair, ha, hb, triangle] at h
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hsum
  simp only [pair]
  rw [hn, triangle]
  omega

theorem pair_tail_smaller (w : Nat) (h : w ≠ 0) : (decode w).2 < w := by
  have hn : pair (decode w).1 (decode w).2 ≠ 0 := by simpa [pair_decode] using h
  have lt := pair_tail_lt (decode w).1 (decode w).2 hn
  simpa [pair_decode] using lt

theorem bounded_push (cert : Nat → Nat → Prop) (w p a proof : Nat)
    (hgood : PA196CertificateStack.BoundedGood decode cert w p) (hproof : cert proof a) :
    PA196CertificateStack.BoundedGood decode cert (pair a w) (pair proof p) :=
  PA196CertificateStack.bounded_push pair decode decode_pair rfl pair_tail_smaller cert w p a proof hgood hproof

theorem bounded_pop (cert : Nat → Nat → Prop) (truthProof w p : Nat)
    (htruth : cert truthProof 0) (hgood : PA196CertificateStack.BoundedGood decode cert w p) :
    cert (PA196CertificateStack.popProof decode truthProof w p).1 (decode w).1 ∧
      PA196CertificateStack.BoundedGood decode cert (decode w).2
        (PA196CertificateStack.popProof decode truthProof w p).2 :=
  PA196CertificateStack.bounded_pop decode rfl pair_tail_smaller cert truthProof htruth w p hgood

/-- A nonzero ghost certificate is ignored when the numeric stack is empty. -/
example : pair 0 0 = 0 ∧ pair 42 0 = 903 ∧
    PA196CertificateStack.popProof decode 1 (pair 0 0) (pair 42 0) = (1,903) := by
  decide

end PA196CertificateStack.Cantor

#print axioms PA196CertificateStack.Cantor.bounded_push
#print axioms PA196CertificateStack.Cantor.bounded_pop

/-!
The next result makes the exact numeric command cases proof-producing,
conditional on concrete certificate constructors. This models the native
checker interface but does not yet represent the construction in iPRA.
-/
namespace PA196CertificateStack.Commands

structure Store where
  t : Nat
  w : Nat
  d : Nat
  h : Nat
  deriving DecidableEq, Repr

structure Proofs where
  t : Nat
  w : Nat
  h : Nat
  deriving DecidableEq, Repr

inductive Command where
  | shift
  | mp (x : Nat)
  | ax (c x y : Nat)
  deriving DecidableEq, Repr

variable (pair : Nat → Nat → Nat) (decode : Nat → Nat × Nat)
variable (cert : Nat → Nat → Prop)
variable (heads : Nat → Nat → Nat → Nat → Nat → List Nat)
variable (gate : Nat → Nat → Nat → Nat)

def implication (a b : Nat) : Nat := 4 * pair a b

def stackOf (xs : List Nat) (w : Nat) : Nat := xs.foldr pair w

def step (c : Command) (s : Store) : Option Store :=
  match c with
  | .shift =>
      if s.t + s.h = 1 then none
      else some ⟨s.h, (decode s.w).2, s.d, (decode s.w).1⟩
  | .mp x =>
      let y := s.d + x
      if implication pair s.t y = s.h then some ⟨y, pair 0 s.w, y, 0⟩
      else some ⟨0, s.w, y, 0⟩
  | .ax c x y =>
      some ⟨gate (s.h+y) (s.d+x) c,
        stackOf pair (heads (s.d+x) (s.h+y) c s.d s.h ++ [s.t]) s.w, 0, 0⟩

def Sound (s : Store) (p : Proofs) : Prop :=
  cert p.t s.t ∧ BoundedGood decode cert s.w p.w ∧ cert p.h s.h

/-- Formula and proof lists of the same length, checked entry by entry. -/
inductive Aligned (cert : Nat → Nat → Prop) : List Nat → List Nat → Prop where
  | nil : Aligned cert [] []
  | cons {f p fs ps} : cert p f → Aligned cert fs ps → Aligned cert (f :: fs) (p :: ps)

/-- Certificate constructors have the same interfaces as the imported checker
lemmas, with AX's eight head proofs supplied in actual stack order. -/
structure Constructors where
  truth : Nat
  truthValid : cert truth 0
  mp : Nat → Nat → Nat → Nat
  mpValid : ∀ t y pt ph, cert pt t → cert ph (implication pair t y) → cert (mp y pt ph) y
  headProofs : Nat → Nat → Nat → Nat → Nat → Nat → List Nat
  headValid : ∀ D H A d h ph,
    d ≤ D → cert ph h →
    Aligned cert
      (heads D H A d h) (headProofs D H A d h ph)
  gateProof : Nat → Nat → Nat → Nat
  gateValid : ∀ a b c, cert (gateProof a b c) (gate a b c)

end PA196CertificateStack.Commands

namespace PA196CertificateStack.Commands
variable (pair : Nat → Nat → Nat) (decode : Nat → Nat × Nat)
variable (cert : Nat → Nat → Prop)
variable (decodePair : ∀ a b, decode (pair a b) = (a,b))
variable (decodeZero : decode 0 = (0,0))
variable (tailSmaller : ∀ w, w ≠ 0 → (decode w).2 < w)

include decodePair decodeZero tailSmaller in
/-- Folding aligned certificate lists preserves the bounded stack invariant. -/
theorem stack_sound {fs ps : List Nat}
    (h : Aligned cert fs ps)
    (w p : Nat) (hw : BoundedGood decode cert w p) :
    BoundedGood decode cert (stackOf pair fs w) (stackOf pair ps p) := by
  induction h with
  | nil => exact hw
  | @cons f pr fs ps hf hs ih =>
    change BoundedGood decode cert (pair f (stackOf pair fs w)) (pair pr (stackOf pair ps p))
    exact bounded_push pair decode decodePair decodeZero tailSmaller cert _ _ _ _ ih hf

end PA196CertificateStack.Commands

namespace PA196CertificateStack.Commands
variable {pair : Nat → Nat → Nat} {decode : Nat → Nat × Nat}
variable {cert : Nat → Nat → Prop}
variable {heads : Nat → Nat → Nat → Nat → Nat → List Nat}
variable {gate : Nat → Nat → Nat → Nat}

theorem aligned_append {as bs cs ds : List Nat}
    (h : Aligned cert as bs) (k : Aligned cert cs ds) :
    Aligned cert (as ++ cs) (bs ++ ds) := by
  induction h with
  | nil => exact k
  | cons hab hrest ih => exact .cons hab ih

/-- A nonhalting command preserves proof-carrying soundness; a halting Shift
returns a native-certificate candidate of formula 1. -/
theorem command_certificate
    (decodePair : ∀ a b, decode (pair a b) = (a,b))
    (decodeZero : decode 0 = (0,0))
    (tailSmaller : ∀ w, w ≠ 0 → (decode w).2 < w)
    (K : Constructors pair cert heads gate) (c : Command) (s : Store) (p : Proofs)
    (hs : Sound decode cert s p) :
    match step pair decode heads gate c s with
    | none => ∃ proof, cert proof 1
    | some s' => ∃ p', Sound decode cert s' p' := by
  obtain ⟨ht, hw, hh⟩ := hs
  cases c with
  | shift =>
    by_cases halt : s.t + s.h = 1
    · simp only [step, halt, if_true]
      by_cases ht1 : s.t = 1
      · exact ⟨p.t, by simpa [ht1] using ht⟩
      · have hh1 : s.h = 1 := by omega
        exact ⟨p.h, by simpa [hh1] using hh⟩
    · simp only [step, halt, if_false]
      have hp := PA196CertificateStack.bounded_pop decode decodeZero tailSmaller cert K.truth
        K.truthValid s.w p.w hw
      exact ⟨⟨p.h, (popProof decode K.truth s.w p.w).2,
        (popProof decode K.truth s.w p.w).1⟩, hh, hp.2, hp.1⟩
  | mp x =>
    by_cases he : implication pair s.t (s.d+x) = s.h
    · simp only [step, he, if_true]
      have hmp : cert (K.mp (s.d+x) p.t p.h) (s.d+x) :=
        K.mpValid _ _ _ _ ht (by simpa [he] using hh)
      have hpush := PA196CertificateStack.bounded_push pair decode decodePair decodeZero tailSmaller
        cert s.w p.w 0 K.truth hw K.truthValid
      exact ⟨⟨K.mp (s.d+x) p.t p.h, pair K.truth p.w, K.truth⟩, hmp, hpush, K.truthValid⟩
    · simp only [step, he, if_false]
      exact ⟨⟨K.truth, p.w, K.truth⟩, K.truthValid, hw, K.truthValid⟩
  | ax a x y =>
    simp only [step]
    have aligned := aligned_append (K.headValid (s.d+x) (s.h+y) a s.d s.h p.h (by omega) hh)
      (Aligned.cons ht Aligned.nil)
    have hpush := stack_sound pair decode cert decodePair decodeZero tailSmaller aligned s.w p.w hw
    exact ⟨⟨K.gateProof (s.h+y) (s.d+x) a,
      stackOf pair (K.headProofs (s.d+x) (s.h+y) a s.d s.h p.h ++ [p.t]) p.w, K.truth⟩,
      K.gateValid _ _ _, hpush, K.truthValid⟩

end PA196CertificateStack.Commands

#print axioms PA196CertificateStack.Commands.command_certificate

namespace PA196CertificateStack.Commands
variable {pair : Nat → Nat → Nat} {decode : Nat → Nat × Nat}
variable {cert : Nat → Nat → Prop}
variable {heads : Nat → Nat → Nat → Nat → Nat → List Nat}
variable {gate : Nat → Nat → Nat → Nat}

def run (pair : Nat → Nat → Nat) (decode : Nat → Nat × Nat)
    (heads : Nat → Nat → Nat → Nat → Nat → List Nat)
    (gate : Nat → Nat → Nat → Nat) : List Command → Store → Option Store
  | [], s => some s
  | c :: cs, s => (step pair decode heads gate c s).bind (run pair decode heads gate cs)

theorem run_halt_certificate
    (decodePair : ∀ a b, decode (pair a b) = (a,b))
    (decodeZero : decode 0 = (0,0))
    (tailSmaller : ∀ w, w ≠ 0 → (decode w).2 < w)
    (K : Constructors pair cert heads gate) (cs : List Command) (s : Store) (p : Proofs)
    (hs : Sound decode cert s p)
    (halt : run pair decode heads gate cs s = none) : ∃ proof, cert proof 1 := by
  induction cs generalizing s p with
  | nil => simp [run] at halt
  | cons c cs ih =>
    have hc := command_certificate decodePair decodeZero tailSmaller K c s p hs
    cases he : step pair decode heads gate c s with
    | none => simpa only [he] using hc
    | some next =>
      obtain ⟨p', hp'⟩ : ∃ p', Sound decode cert next p' := by simpa only [he] using hc
      have hrest : run pair decode heads gate cs next = none := by simpa [run, he] using halt
      exact ih next p' hp' hrest

/-- The exact Cantor numeric stack with a zero initial command store. -/
theorem cantor_initial_halt_certificate
    (K : Constructors Cantor.pair cert heads gate) (cs : List Command)
    (halt : run Cantor.pair Cantor.decode heads gate cs ⟨0,0,0,0⟩ = none) :
    ∃ proof, cert proof 1 := by
  apply run_halt_certificate Cantor.decode_pair rfl Cantor.pair_tail_smaller K cs
    ⟨0,0,0,0⟩ ⟨K.truth,0,K.truth⟩
  · exact ⟨K.truthValid, (good_iff_bounded Cantor.decode rfl Cantor.pair_tail_smaller cert 0 0).mp
      (good_empty Cantor.decode rfl cert 0), K.truthValid⟩
  · exact halt

end PA196CertificateStack.Commands

#print axioms PA196CertificateStack.Commands.run_halt_certificate
#print axioms PA196CertificateStack.Commands.cantor_initial_halt_certificate

namespace PA196CertificateStack.Commands
variable {pair : Nat → Nat → Nat} {decode : Nat → Nat × Nat}
variable {cert : Nat → Nat → Prop}
variable {heads : Nat → Nat → Nat → Nat → Nat → List Nat}
variable {gate : Nat → Nat → Nat → Nat}

/-- A deterministic certificate update for the exact numeric command step.
`Sum.inl` is a certificate emitted on Shift halt; `Sum.inr` is the next
proof-carrying store. -/
def proofStep (K : Constructors pair cert heads gate) (c : Command) (s : Store) (p : Proofs) :
    Nat ⊕ Proofs :=
  match c with
  | .shift =>
      if s.t + s.h = 1 then .inl (if s.t = 1 then p.t else p.h)
      else .inr ⟨p.h, (popProof decode K.truth s.w p.w).2,
        (popProof decode K.truth s.w p.w).1⟩
  | .mp x =>
      let y := s.d+x
      if implication pair s.t y = s.h then
        .inr ⟨K.mp y p.t p.h, pair K.truth p.w, K.truth⟩
      else .inr ⟨K.truth,p.w,K.truth⟩
  | .ax a x y =>
      .inr ⟨K.gateProof (s.h+y) (s.d+x) a,
        stackOf pair (K.headProofs (s.d+x) (s.h+y) a s.d s.h p.h ++ [p.t]) p.w,
        K.truth⟩

theorem proof_step_correct
    (decodePair : ∀ a b, decode (pair a b) = (a,b))
    (decodeZero : decode 0 = (0,0))
    (tailSmaller : ∀ w, w ≠ 0 → (decode w).2 < w)
    (K : Constructors pair cert heads gate) (c : Command) (s : Store) (p : Proofs)
    (hs : Sound decode cert s p) :
    match step pair decode heads gate c s, proofStep (decode := decode) K c s p with
    | none, .inl proof => cert proof 1
    | some s', .inr p' => Sound decode cert s' p'
    | _, _ => False := by
  obtain ⟨ht, hw, hh⟩ := hs
  cases c with
  | shift =>
    by_cases halt : s.t + s.h = 1
    · simp only [step, proofStep, halt, if_true]
      split
      · rename_i ht1; simpa [ht1] using ht
      · rename_i ht1
        have hh1 : s.h = 1 := by omega
        simpa [hh1] using hh
    · simp only [step, proofStep, halt, if_false]
      have hp := PA196CertificateStack.bounded_pop decode decodeZero tailSmaller cert K.truth
        K.truthValid s.w p.w hw
      exact ⟨hh, hp.2, hp.1⟩
  | mp x =>
    by_cases he : implication pair s.t (s.d+x) = s.h
    · simp only [step, proofStep, he, if_true]
      have hmp := K.mpValid s.t (s.d+x) p.t p.h ht (by simpa [he] using hh)
      have hpush := PA196CertificateStack.bounded_push pair decode decodePair decodeZero tailSmaller
        cert s.w p.w 0 K.truth hw K.truthValid
      exact ⟨hmp, hpush, K.truthValid⟩
    · simp only [step, proofStep, he, if_false]
      exact ⟨K.truthValid, hw, K.truthValid⟩
  | ax a x y =>
    simp only [step, proofStep]
    have aligned := aligned_append (K.headValid (s.d+x) (s.h+y) a s.d s.h p.h (by omega) hh)
      (Aligned.cons ht Aligned.nil)
    have hpush := stack_sound pair decode cert decodePair decodeZero tailSmaller aligned s.w p.w hw
    exact ⟨K.gateValid _ _ _, hpush, K.truthValid⟩

/-- The explicit extractor returns the first halt certificate, or none. -/
def extract (K : Constructors pair cert heads gate) : List Command → Store → Proofs → Option Nat
  | [], _, _ => none
  | c :: cs, s, p =>
      match step pair decode heads gate c s, proofStep (decode := decode) K c s p with
      | none, .inl proof => some proof
      | some s', .inr p' => extract K cs s' p'
      | _, _ => none

theorem extract_correct
    (decodePair : ∀ a b, decode (pair a b) = (a,b))
    (decodeZero : decode 0 = (0,0))
    (tailSmaller : ∀ w, w ≠ 0 → (decode w).2 < w)
    (K : Constructors pair cert heads gate) (cs : List Command) (s : Store) (p : Proofs)
    (hs : Sound decode cert s p)
    (halt : run pair decode heads gate cs s = none) :
    ∃ proof, extract (decode := decode) K cs s p = some proof ∧ cert proof 1 := by
  induction cs generalizing s p with
  | nil => simp [run] at halt
  | cons c cs ih =>
    have hp := proof_step_correct decodePair decodeZero tailSmaller K c s p hs
    cases he : step pair decode heads gate c s with
    | none =>
      cases hf : proofStep (decode := decode) K c s p with
      | inl proof =>
        have good : cert proof 1 := by simpa only [he, hf] using hp
        exact ⟨proof, by simp [extract, he, hf], good⟩
      | inr ps => simp only [he, hf] at hp
    | some next =>
      cases hf : proofStep (decode := decode) K c s p with
      | inl proof => simp only [he, hf] at hp
      | inr ps =>
        have good : Sound decode cert next ps := by simpa only [he, hf] using hp
        have rest : run pair decode heads gate cs next = none := by simpa [run, he] using halt
        obtain ⟨proof, hex, hc⟩ := ih next ps good rest
        exact ⟨proof, by simpa [extract, he, hf] using hex, hc⟩

end PA196CertificateStack.Commands

#print axioms PA196CertificateStack.Commands.proof_step_correct
#print axioms PA196CertificateStack.Commands.extract_correct

namespace PA196CertificateStack.Commands
variable {cert : Nat → Nat → Prop}
variable {heads : Nat → Nat → Nat → Nat → Nat → List Nat}
variable {gate : Nat → Nat → Nat → Nat}

/-- Explicit certificate extraction for the exact numeric Cantor stack,
starting from PA196's zero command store. -/
theorem cantor_initial_extract_correct
    (K : Constructors Cantor.pair cert heads gate) (cs : List Command)
    (halt : run Cantor.pair Cantor.decode heads gate cs ⟨0,0,0,0⟩ = none) :
    ∃ proof, extract (decode := Cantor.decode) K cs ⟨0,0,0,0⟩ ⟨K.truth,0,K.truth⟩ = some proof ∧
      cert proof 1 := by
  apply extract_correct Cantor.decode_pair rfl Cantor.pair_tail_smaller K cs
    ⟨0,0,0,0⟩ ⟨K.truth,0,K.truth⟩
  · exact ⟨K.truthValid, (good_iff_bounded Cantor.decode rfl Cantor.pair_tail_smaller cert 0 0).mp
      (good_empty Cantor.decode rfl cert 0), K.truthValid⟩
  · exact halt

end PA196CertificateStack.Commands

#print axioms PA196CertificateStack.Commands.cantor_initial_extract_correct

/- Exact numeric heads and certificate encodings from PA196/Commands/Code.lean
and PA196/Arithmetic/Certificates/{MPGen,Leaves}.lean. This is a standalone
copy, not an imported or machine-checked linkage to the 4.35 development. -/
namespace PA196CertificateStack.Native
open PA196CertificateStack.Cantor
open PA196CertificateStack.Commands

def I (a b : Nat) : Nat := 4 * pair a b
def M (a b : Nat) : Nat := 4 * pair a b + 1
def U (a b : Nat) : Nat := 4 * pair b a + 2
def E (a b : Nat) : Nat := 4 * pair a b + 3
def N (a : Nat) : Nat := I a 1
def conj (a b : Nat) : Nat := N (I a (N b))
def ex (a b : Nat) : Nat := N (U a (N b))
def head1 (D H : Nat) : Nat := I (ex D (U D H)) H
def head2 (D A H : Nat) : Nat := I (U D (U A H)) (U A (U D H))
def head3 (D A H : Nat) : Nat := I (M H D) (I (E H A) (M A D))
def head4 (D A H : Nat) : Nat := I (E H D) (I (M A H) (M A D))
def head5 (D H : Nat) : Nat := ex D (E H D)
def head6 (D A H : Nat) : Nat := I (U D A) (I (U D (I A H)) (U D H))
def rho8 (a b c u : Nat) : Nat := I (I (I c u) a) (I (I a c) (I b c))
def eqVac (a b c : Nat) : Nat := I (E a b) (U c (E a b))
def memVac (a b c : Nat) : Nat := I (M a b) (U c (M a b))
def point (_a b c : Nat) : Nat := I c (M c b)
def separation (a b c : Nat) : Nat :=
  U b (conj (I (M a b) (point a b c)) (I (M c b) c))
def separationTail (a b c : Nat) : Nat := U c (I (separation a b c) (N (point a b c)))
def bundle (a b c : Nat) : Nat := N (I (eqVac a b c) (I (memVac a b c) (separationTail a b c)))
def gate (a b c : Nat) : Nat := if c = a ∨ c = b then 0 else bundle a b c
def heads (D H A d h : Nat) : List Nat :=
  [head6 D A H, head5 D H, head4 D A H, head3 D A H,
   head2 D A H, head1 D H, rho8 D A H d, U d h]

def pack2 (a b : Nat) : Nat := pair a (pair b 0)
def pack3 (a b c : Nat) : Nat := pair a (pack2 b c)
def pack4 (a b c d : Nat) : Nat := pair a (pack3 b c d)
def leaf (tag payload : Nat) : Nat := pair 1 (pair tag payload)
def mpTree (b p q : Nat) : Nat := pair 0 (pack3 b p q)
def genTree (v p : Nat) : Nat := pair 1 (pack2 v p)
def mpCertificate (b minor major : Nat) : Nat :=
  pair ((decode minor).1 + (decode major).1 + 1)
    (mpTree b (decode minor).2 (decode major).2)
def genCertificate (v child : Nat) : Nat :=
  pair ((decode child).1 + 1) (genTree v (decode child).2)
def headProofs (D H A d _h ph : Nat) : List Nat :=
  [leaf 7 (pack3 D A H), leaf 6 (pack2 D H), leaf 5 (pack3 D A H),
   leaf 4 (pack3 D A H), leaf 3 (pack3 D A H), leaf 2 (pack2 D H),
   leaf 8 (pack4 D A H d), genCertificate d ph]
def gateProof (a b c : Nat) : Nat :=
  if c = a ∨ c = b then 739 else leaf 9 (pack3 a b c)

/-- The following are the concrete checker obligations. They are hypotheses,
not axioms declared by this file or theorems proved here. -/
structure CheckerInterfaces (cert : Nat → Nat → Prop) : Prop where
  truth : cert 739 0
  mp : ∀ a b p q, cert p a → cert q (I a b) → cert (mpCertificate b p q) b
  gen : ∀ v a p, cert p a → cert (genCertificate v p) (U v a)
  head1 : ∀ D H, cert (leaf 2 (pack2 D H)) (head1 D H)
  head2 : ∀ D A H, cert (leaf 3 (pack3 D A H)) (head2 D A H)
  head3 : ∀ D A H, cert (leaf 4 (pack3 D A H)) (head3 D A H)
  head4 : ∀ D A H, cert (leaf 5 (pack3 D A H)) (head4 D A H)
  head5 : ∀ D H, cert (leaf 6 (pack2 D H)) (head5 D H)
  head6 : ∀ D A H, cert (leaf 7 (pack3 D A H)) (head6 D A H)
  r8 : ∀ D A H d, d ≤ D → cert (leaf 8 (pack4 D A H d)) (rho8 D A H d)
  bundle : ∀ a b c, c ≠ a → c ≠ b → cert (leaf 9 (pack3 a b c)) (bundle a b c)

/-- The imported checker's numeric equations, once supplied for `cert`,
instantiate the generic proof-carrying command interpreter. -/
def checkerConstructors (cert : Nat → Nat → Prop) (h : CheckerInterfaces cert) :
    Constructors pair cert heads gate where
  truth := 739
  truthValid := h.truth
  mp := mpCertificate
  mpValid := by
    intro a b p q hp hq
    exact h.mp a b p q hp (by simpa [I, implication] using hq)
  headProofs := headProofs
  headValid := by
    intro D H A d h0 ph hle hph
    exact .cons (h.head6 D A H) <|
      .cons (h.head5 D H) <|
      .cons (h.head4 D A H) <|
      .cons (h.head3 D A H) <|
      .cons (h.head2 D A H) <|
      .cons (h.head1 D H) <|
      .cons (h.r8 D A H d hle) <|
      .cons (h.gen d h0 ph hph) .nil
  gateProof := gateProof
  gateValid := by
    intro a b c
    by_cases guard : c = a ∨ c = b
    · simpa [gateProof, gate, guard] using h.truth
    · have ha : c ≠ a := fun ha => guard (Or.inl ha)
      have hb : c ≠ b := fun hb => guard (Or.inr hb)
      simpa [gateProof, gate, guard] using h.bundle a b c ha hb

theorem native_halt_extractor (cert : Nat → Nat → Prop) (h : CheckerInterfaces cert)
    (cs : List Command) (halt : run pair decode heads gate cs ⟨0,0,0,0⟩ = none) :
    ∃ proof, extract (decode := decode) (checkerConstructors cert h) cs
        ⟨0,0,0,0⟩ ⟨739,0,739⟩ = some proof ∧ cert proof 1 := by
  exact cantor_initial_extract_correct (checkerConstructors cert h) cs halt

example : leaf 8 (pack4 0 0 0 0) = 739 := by decide
end PA196CertificateStack.Native

#print axioms PA196CertificateStack.Native.native_halt_extractor
