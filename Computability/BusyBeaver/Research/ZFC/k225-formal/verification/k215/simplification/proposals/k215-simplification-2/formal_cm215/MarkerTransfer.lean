import PositiveSimulation

/-! A local marker simulation on arbitrary two-way tapes.
The local invariant is strengthened by a single auxiliary clause at 156.
Consequently its proof is a one-step induction; no run-history case is needed.
The theorem is parameterized by finite row facts, instantiated separately. -/
namespace MarkerTransfer

abbrev Q := Fin 303
structure Row where
  write : Bool
  right : Bool
  target : Q
  deriving DecidableEq, Repr
abbrev TM := Q → Bool → Option Row
abbrev Tape := Int → Bool
structure Conf where
  q : Q
  head : Int
  tape : Tape

def write (t : Tape) (h : Int) (b : Bool) : Tape := fun x => if x = h then b else t x

def delta (right : Bool) : Int := if right then 1 else -1

def next (M : TM) (c : Conf) : Conf :=
  match M c.q (c.tape c.head) with
  | none => c
  | some r => ⟨r.target, c.head + delta r.right, write c.tape c.head r.write⟩

def Halt (M : TM) (c : Conf) : Prop := M c.q (c.tape c.head) = none

def phi (q : Q) : Q := if q = 176 then 52 else q

def lift (c : Conf) : Conf := ⟨phi c.q, c.head, c.tape⟩

def mapRow (r : Row) : Row := { r with target := phi r.target }

def Inv (c : Conf) : Prop :=
  (c.q = 52 → c.tape (c.head - 1) = true) ∧
  (c.q = 176 → c.tape c.head = false → c.tape (c.head - 1) = false) ∧
  (c.q = 156 → c.tape (c.head + 1) = true)

def incoming52P : Option Row → Prop
  | none => True
  | some r => r.target = 52 → r.write = true ∧ r.right = true

def incoming176P (q : Q) : Option Row → Prop
  | none => True
  | some r => r.target = 176 →
      (r.write = false ∧ r.right = true) ∨
      (q = 156 ∧ r.write = true ∧ r.right = true)

def incoming156P : Option Row → Prop
  | none => True
  | some r => r.target = 156 → r.write = true ∧ r.right = false

instance (r : Option Row) : Decidable (incoming52P r) := by
  cases r <;> unfold incoming52P <;> infer_instance
instance (q : Q) (r : Option Row) : Decidable (incoming176P q r) := by
  cases r <;> unfold incoming176P <;> infer_instance
instance (r : Option Row) : Decidable (incoming156P r) := by
  cases r <;> unfold incoming156P <;> infer_instance

structure Facts (O N : TM) : Prop where
  common : ∀ q b, q ≠ 52 → q ≠ 176 → N q b = (O q b).map mapRow
  old52 : ∀ b, O 52 b = some ⟨b, true, if b then 150 else 154⟩
  old176 : ∀ b, O 176 b = some ⟨b, true, if b then 150 else 168⟩
  new52 : ∀ b, N 52 b = some (if b then ⟨true, true, 150⟩ else ⟨false, false, 176⟩)
  new176 : ∀ b, N 176 b = some ⟨b, true, if b then 129 else 185⟩
  new129 : N 129 false = some ⟨false, true, 154⟩
  new185 : N 185 false = some ⟨false, true, 168⟩
  in52 : ∀ q b, incoming52P (O q b)
  in176 : ∀ q b, incoming176P q (O q b)
  in156 : ∀ q b, incoming156P (O q b)

theorem write_read (t : Tape) (h : Int) : write t h (t h) = t := by
  funext x
  by_cases hx : x = h <;> simp [write, hx]

theorem next_readOnly {M : TM} {q z : Q} {t : Tape} {h : Int} {b r : Bool}
    (hb : t h = b) (hm : M q b = some ⟨b, r, z⟩) :
    next M ⟨q, h, t⟩ = ⟨z, h + delta r, t⟩ := by
  simp only [next, hb, hm]
  have hw : write t h b = t := by rw [← hb]; exact write_read t h
  rw [hw]

theorem inv_start (h : Int) (t : Tape) : Inv ⟨0, h, t⟩ := by
  simp [Inv]

theorem inv_next {O N : TM} (F : Facts O N) {c : Conf} (hc : Inv c) : Inv (next O c) := by
  rcases c with ⟨q, h, t⟩
  rcases hc with ⟨h52, h176, h156⟩
  cases he : O q (t h) with
  | none => simpa [next, he, Inv] using And.intro h52 (And.intro h176 h156)
  | some r =>
      have a52 := F.in52 q (t h)
      have a176 := F.in176 q (t h)
      have a156 := F.in156 q (t h)
      rw [he] at a52 a176 a156
      change (r.target = 52 → r.write = true ∧ r.right = true) at a52
      change (r.target = 176 → (r.write = false ∧ r.right = true) ∨
          (q = 156 ∧ r.write = true ∧ r.right = true)) at a176
      change (r.target = 156 → r.write = true ∧ r.right = false) at a156
      simp only [next, he, Inv]
      refine ⟨?_, ?_, ?_⟩
      · intro hz
        obtain ⟨hw, hd⟩ := a52 hz
        simp [hd, hw, delta, write]
      · intro hz hb
        rcases a176 hz with ⟨hw, hd⟩ | ⟨hq, hw, hd⟩
        · simp [hd, hw, delta, write]
        · have ht := h156 hq
          change t (h + 1) = true at ht
          have hh : h + 1 ≠ h := by omega
          simp [hd, delta, write, hh] at hb
          rw [ht] at hb
          contradiction
      · intro hz
        obtain ⟨hw, hd⟩ := a156 hz
        have hx : h + -1 + 1 = h := by omega
        simp [hd, hw, delta, write, hx]

/-- Every old step is reproduced by one or three target steps, with the entire
head and tape identical at the synchronization boundary. -/
theorem local_sim {O N : TM} (F : Facts O N) {c : Conf} (hc : Inv c) :
    ∃ j, PositiveSimulation.iter (next N) (j + 1) (lift c) = lift (next O c) := by
  rcases c with ⟨q, h, t⟩
  by_cases hq52 : q = 52
  · subst q
    cases hb : t h with
    | false =>
        have hm := hc.1 rfl
        have ho : next O ⟨52, h, t⟩ = ⟨154, h + 1, t⟩ := by
          simpa [delta] using next_readOnly hb (F.old52 false)
        have h1 : next N ⟨52, h, t⟩ = ⟨176, h - 1, t⟩ := by
          simpa [delta, Int.sub_eq_add_neg] using next_readOnly hb (F.new52 false)
        have h2 : next N ⟨176, h - 1, t⟩ = ⟨129, h, t⟩ := by
          simpa [delta] using next_readOnly hm (F.new176 true)
        have h3 : next N ⟨129, h, t⟩ = ⟨154, h + 1, t⟩ := by
          simpa [delta] using next_readOnly hb F.new129
        refine ⟨2, ?_⟩
        change next N (next N (next N ⟨52, h, t⟩)) = lift (next O ⟨52, h, t⟩)
        rw [h1, h2, h3, ho]
        rfl
    | true =>
        have ho : next O ⟨52, h, t⟩ = ⟨150, h + 1, t⟩ := by
          simpa [delta] using next_readOnly hb (F.old52 true)
        have hn : next N ⟨52, h, t⟩ = ⟨150, h + 1, t⟩ := by
          simpa [delta] using next_readOnly hb (F.new52 true)
        refine ⟨0, ?_⟩
        change next N ⟨52, h, t⟩ = lift (next O ⟨52, h, t⟩)
        rw [hn, ho]
        rfl
  · by_cases hq176 : q = 176
    · subst q
      cases hb : t h with
      | false =>
          have hm := hc.2.1 rfl hb
          have ho : next O ⟨176, h, t⟩ = ⟨168, h + 1, t⟩ := by
            simpa [delta] using next_readOnly hb (F.old176 false)
          have h1 : next N ⟨52, h, t⟩ = ⟨176, h - 1, t⟩ := by
            simpa [delta, Int.sub_eq_add_neg] using next_readOnly hb (F.new52 false)
          have h2 : next N ⟨176, h - 1, t⟩ = ⟨185, h, t⟩ := by
            simpa [delta] using next_readOnly hm (F.new176 false)
          have h3 : next N ⟨185, h, t⟩ = ⟨168, h + 1, t⟩ := by
            simpa [delta] using next_readOnly hb F.new185
          refine ⟨2, ?_⟩
          change next N (next N (next N ⟨52, h, t⟩)) = lift (next O ⟨176, h, t⟩)
          rw [h1, h2, h3, ho]
          rfl
      | true =>
          have ho : next O ⟨176, h, t⟩ = ⟨150, h + 1, t⟩ := by
            simpa [delta] using next_readOnly hb (F.old176 true)
          have hn : next N ⟨52, h, t⟩ = ⟨150, h + 1, t⟩ := by
            simpa [delta] using next_readOnly hb (F.new52 true)
          refine ⟨0, ?_⟩
          change next N ⟨52, h, t⟩ = lift (next O ⟨176, h, t⟩)
          rw [hn, ho]
          rfl
    · refine ⟨0, ?_⟩
      have hn := F.common q (t h) hq52 hq176
      have hp : phi q = q := by simp [phi, hq176]
      cases he : O q (t h) with
      | none => simp [PositiveSimulation.iter, next, lift, hp, hn, he]
      | some r => simp [PositiveSimulation.iter, next, lift, hp, hn, he, mapRow]

theorem halt_lift {O N : TM} (F : Facts O N) (c : Conf) : Halt O c ↔ Halt N (lift c) := by
  rcases c with ⟨q, h, t⟩
  by_cases h52 : q = 52
  · subst q
    simp [Halt, lift, phi, F.old52, F.new52]
  · by_cases h176 : q = 176
    · subst q
      simp [Halt, lift, phi, F.old176, F.new52]
    · have hn := F.common q (t h) h52 h176
      have hp : phi q = q := by simp [phi, h176]
      cases he : O q (t h) <;> simp [Halt, lift, hp, hn, he]

theorem halt_stable (M : TM) (c : Conf) (hc : Halt M c) : Halt M (next M c) := by
  unfold Halt at hc
  simp only [next, hc]
  exact hc

/-- This is an all-initial-tapes theorem from the designated start state.
It says nothing about arbitrary initial controls with a false marker invariant. -/
theorem all_tapes_equihalt {O N : TM} (F : Facts O N) (h : Int) (t : Tape) :
    (∃ n, Halt O (PositiveSimulation.iter (next O) n ⟨0, h, t⟩)) ↔
    (∃ n, Halt N (PositiveSimulation.iter (next N) n ⟨0, h, t⟩)) := by
  let R : Conf → Conf → Prop := fun c d => Inv c ∧ d = lift c
  have hs : ∀ c d, R c d → ∃ j, R (next O c) (PositiveSimulation.iter (next N) (j + 1) d) := by
    rintro c d ⟨hc, rfl⟩
    obtain ⟨j, hj⟩ := local_sim F hc
    exact ⟨j, inv_next F hc, hj⟩
  have hh : ∀ c d, R c d → (Halt O c ↔ Halt N d) := by
    rintro c d ⟨_, rfl⟩
    exact halt_lift F c
  exact PositiveSimulation.halts_iff (next O) (next N) (Halt O) (Halt N) R hs hh
    (halt_stable N) ⟨inv_start h t, rfl⟩

#print axioms all_tapes_equihalt
end MarkerTransfer
