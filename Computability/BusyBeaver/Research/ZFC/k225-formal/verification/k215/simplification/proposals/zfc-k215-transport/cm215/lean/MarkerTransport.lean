import PositiveStuttering

namespace MarkerTransport

abbrev State := Fin 303

structure Row where
  write : Bool
  right : Bool
  next : State
  deriving DecidableEq

abbrev Table := State → Bool → Option Row

def phi (q : State) : State := if q = 176 then 52 else q
def renameRow (r : Row) : Row := { r with next := phi r.next }

structure Certificate (old new : Table) : Prop where
  outer : ∀ q b, q ≠ 52 → q ≠ 176 →
    new (phi q) b = (old q b).map renameRow
  stopped : ∀ q b, old q b = none → new (phi q) b = none
  incoming52 : ∀ q b, match old q b with
    | none => True
    | some r => r.next = 52 → r.write = true ∧ r.right = true
  incoming156 : ∀ q b, match old q b with
    | none => True
    | some r => r.next = 156 → r.write = true ∧ r.right = false
  incoming176 : ∀ q b, match old q b with
    | none => True
    | some r => r.next = 176 →
      (r.write = false ∧ r.right = true) ∨
      (q = 156 ∧ b = true ∧ r.write = true ∧ r.right = true)
  old52zero : old 52 false = some ⟨false, true, 154⟩
  old52one : old 52 true = some ⟨true, true, 150⟩
  old176zero : old 176 false = some ⟨false, true, 168⟩
  old176one : old 176 true = some ⟨true, true, 150⟩
  new52zero : new 52 false = some ⟨false, false, 176⟩
  new52one : new 52 true = some ⟨true, true, 150⟩
  new176zero : new 176 false = some ⟨false, true, 185⟩
  new176one : new 176 true = some ⟨true, true, 129⟩
  new185zero : new 185 false = some ⟨false, true, 168⟩
  new129zero : new 129 false = some ⟨false, true, 154⟩

abbrev Tape := Int → Bool

structure Config where
  q : State
  h : Int
  tape : Tape

def write (t : Tape) (h : Int) (b : Bool) : Tape :=
  fun i => if i = h then b else t i

@[simp] theorem write_here (t : Tape) (h : Int) (b : Bool) :
    write t h b h = b := by simp [write]

@[simp] theorem write_right (t : Tape) (h : Int) (b : Bool) :
    write t h b (h + 1) = t (h + 1) := by
  simp [write, show h + 1 ≠ h by omega]

@[simp] theorem write_left (t : Tape) (h : Int) (b : Bool) :
    write t h b (h - 1) = t (h - 1) := by
  simp [write, show h - 1 ≠ h by omega]

theorem write_read (t : Tape) (h : Int) : write t h (t h) = t := by
  funext i
  by_cases hi : i = h <;> simp_all [write]

def perform (c : Config) (r : Row) : Config :=
  ⟨r.next, if r.right then c.h + 1 else c.h - 1,
    write c.tape c.h r.write⟩

def step (table : Table) (c : Config) : Option Config :=
  (table c.q (c.tape c.h)).map (perform c)

def mapConfig (c : Config) : Config := { c with q := phi c.q }

def Inv (c : Config) : Prop :=
  (c.q = 52 → c.tape (c.h - 1) = true) ∧
  (c.q = 176 → c.tape c.h = true ∨ c.tape (c.h - 1) = false) ∧
  (c.q = 156 → c.tape (c.h + 1) = true)

theorem start_inv (h : Int) (t : Tape) : Inv ⟨0, h, t⟩ := by
  simp [Inv]

theorem preserve (cert : Certificate old new) :
    ∀ c c', Inv c → step old c = some c' → Inv c' := by
  intro c c' hi hs
  cases he : old c.q (c.tape c.h) with
  | none => simp [step, he] at hs
  | some r =>
    have hc : perform c r = c' := by simpa [step, he] using hs
    subst c'
    have h52 := cert.incoming52 c.q (c.tape c.h)
    have h156 := cert.incoming156 c.q (c.tape c.h)
    have h176 := cert.incoming176 c.q (c.tape c.h)
    simp only [he] at h52 h156 h176
    constructor
    · intro hq
      obtain ⟨hw, hd⟩ := h52 hq
      simp [perform, hw, hd]
    constructor
    · intro hq
      rcases h176 hq with ⟨hw, hd⟩ | ⟨hq', hb, hw, hd⟩
      · right
        simp [perform, hw, hd]
      · left
        simpa [perform, hw, hd] using hi.2.2 hq'
    · intro hq
      obtain ⟨hw, hd⟩ := h156 hq
      simp [perform, hw, hd]

theorem terminal (cert : Certificate old new) :
    ∀ c, Inv c → step old c = none → step new (mapConfig c) = none := by
  intro c _ hs
  have he : old c.q (c.tape c.h) = none := by
    cases hx : old c.q (c.tape c.h) <;> simp_all [step]
  simpa [step, mapConfig] using cert.stopped c.q (c.tape c.h) he


theorem read_step {table : Table} {q z : State} {h : Int} {t : Tape} {d : Bool}
    (hr : table q (t h) = some ⟨t h, d, z⟩) :
    step table ⟨q, h, t⟩ = some ⟨z, if d then h + 1 else h - 1, t⟩ := by
  simp [step, hr, perform, write_read]

theorem block (cert : Certificate old new) :
    ∀ c c', Inv c → step old c = some c' →
      ∃ m, 0 < m ∧
        PositiveStuttering.Steps (step new) m (mapConfig c) (mapConfig c') := by
  intro c c' hi hs
  rcases c with ⟨q, h, t⟩
  by_cases h52 : q = 52
  · subst q
    cases hb : t h with
    | false =>
      have hl : t (h - 1) = true := hi.1 rfl
      have ho : step old ⟨52, h, t⟩ = some ⟨154, h + 1, t⟩ :=
        read_step (table := old) (q := 52) (h := h) (t := t) (d := true) (z := 154) (by simpa [hb] using cert.old52zero)
      have hc := Option.some.inj (ho.symm.trans hs)
      subst c'
      have hn1 : step new ⟨52, h, t⟩ = some ⟨176, h - 1, t⟩ :=
        read_step (table := new) (q := 52) (h := h) (t := t) (d := false) (z := 176) (by simpa [hb] using cert.new52zero)
      have hn2 : step new ⟨176, h - 1, t⟩ = some ⟨129, h, t⟩ := by
        simpa using (read_step (table := new) (q := 176) (h := h - 1)
          (t := t) (d := true) (z := 129)
          (by simpa [hl] using cert.new176one))
      have hn3 : step new ⟨129, h, t⟩ = some ⟨154, h + 1, t⟩ :=
        read_step (table := new) (q := 129) (h := h) (t := t) (d := true) (z := 154) (by simpa [hb] using cert.new129zero)
      refine ⟨3, by decide, ?_⟩
      simpa [mapConfig, phi] using
        (PositiveStuttering.Steps.next hn1
          (PositiveStuttering.Steps.next hn2
            (PositiveStuttering.Steps.next hn3
              (PositiveStuttering.Steps.refl _))))
    | true =>
      have ho : step old ⟨52, h, t⟩ = some ⟨150, h + 1, t⟩ :=
        read_step (table := old) (q := 52) (h := h) (t := t) (d := true) (z := 150) (by simpa [hb] using cert.old52one)
      have hc := Option.some.inj (ho.symm.trans hs)
      subst c'
      have hn : step new ⟨52, h, t⟩ = some ⟨150, h + 1, t⟩ :=
        read_step (table := new) (q := 52) (h := h) (t := t) (d := true) (z := 150) (by simpa [hb] using cert.new52one)
      refine ⟨1, by decide, ?_⟩
      simpa [mapConfig, phi] using
        (PositiveStuttering.Steps.next hn (PositiveStuttering.Steps.refl _))
  · by_cases h176 : q = 176
    · subst q
      cases hb : t h with
      | false =>
        have hl : t (h - 1) = false := by
          rcases hi.2.1 rfl with hh | hh
          · simp [hb] at hh
          · exact hh
        have ho : step old ⟨176, h, t⟩ = some ⟨168, h + 1, t⟩ :=
          read_step (table := old) (q := 176) (h := h) (t := t) (d := true) (z := 168) (by simpa [hb] using cert.old176zero)
        have hc := Option.some.inj (ho.symm.trans hs)
        subst c'
        have hn1 : step new ⟨52, h, t⟩ = some ⟨176, h - 1, t⟩ :=
          read_step (table := new) (q := 52) (h := h) (t := t) (d := false) (z := 176) (by simpa [hb] using cert.new52zero)
        have hn2 : step new ⟨176, h - 1, t⟩ = some ⟨185, h, t⟩ := by
          simpa using (read_step (table := new) (q := 176) (h := h - 1)
            (t := t) (d := true) (z := 185)
            (by simpa [hl] using cert.new176zero))
        have hn3 : step new ⟨185, h, t⟩ = some ⟨168, h + 1, t⟩ :=
          read_step (table := new) (q := 185) (h := h) (t := t) (d := true) (z := 168) (by simpa [hb] using cert.new185zero)
        refine ⟨3, by decide, ?_⟩
        simpa [mapConfig, phi] using
          (PositiveStuttering.Steps.next hn1
            (PositiveStuttering.Steps.next hn2
              (PositiveStuttering.Steps.next hn3
                (PositiveStuttering.Steps.refl _))))
      | true =>
        have ho : step old ⟨176, h, t⟩ = some ⟨150, h + 1, t⟩ :=
          read_step (table := old) (q := 176) (h := h) (t := t) (d := true) (z := 150) (by simpa [hb] using cert.old176one)
        have hc := Option.some.inj (ho.symm.trans hs)
        subst c'
        have hn : step new ⟨52, h, t⟩ = some ⟨150, h + 1, t⟩ :=
          read_step (table := new) (q := 52) (h := h) (t := t) (d := true) (z := 150) (by simpa [hb] using cert.new52one)
        refine ⟨1, by decide, ?_⟩
        simpa [mapConfig, phi] using
          (PositiveStuttering.Steps.next hn (PositiveStuttering.Steps.refl _))
    · cases he : old q (t h) with
      | none => simp [step, he] at hs
      | some r =>
        have hc : perform ⟨q, h, t⟩ r = c' := by
          simpa [step, he] using hs
        subst c'
        have hn : step new (mapConfig ⟨q, h, t⟩) =
            some (mapConfig (perform ⟨q, h, t⟩ r)) := by
          simp only [step, mapConfig]
          rw [cert.outer q (t h) h52 h176]
          simp [he, perform, renameRow]
        exact ⟨1, by decide,
          PositiveStuttering.Steps.next hn (PositiveStuttering.Steps.refl _)⟩

theorem simulation (cert : Certificate old new) :
    PositiveStuttering.Simulation (step old) (step new) mapConfig Inv :=
  ⟨preserve cert, terminal cert, block cert⟩

theorem halts_iff (cert : Certificate old new) {c : Config} (hi : Inv c) :
    PositiveStuttering.Halts (step old) c ↔
      PositiveStuttering.Halts (step new) (mapConfig c) :=
  (simulation cert).halts_iff hi

/-- Arbitrary initial whole tape and head position, designated initial control 0. -/
theorem all_tape_halts_iff (cert : Certificate old new) (h : Int) (t : Tape) :
    PositiveStuttering.Halts (step old) ⟨0, h, t⟩ ↔
      PositiveStuttering.Halts (step new) ⟨0, h, t⟩ := by
  simpa [mapConfig, phi] using (halts_iff cert (start_inv h t))

#print axioms all_tape_halts_iff

end MarkerTransport
