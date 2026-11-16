import DiophantineConsistency.PRALanguage
import PA196.Literal
import Mathlib.Computability.Primrec.List

/-!
The actual PA196 literal table, viewed as a primitive-recursive bounded
halting test for the existing iPRA function-code language. Tape halves are
binary naturals, with the head bit at the least significant bit of the right
half. Every state outside the 196-row working domain is totalized by a
self-loop, exactly corresponding to a halted `M6.Zip.step`.

The 392 table entries below are kernel-checked against the imported
`PA196.Literal.transition`. `zip_step_binding` proves the numeric step agrees
with the imported finite-support zipper semantics on every configuration;
`code_halts_iff_literal` proves its existential clock is exactly the imported
literal machine's blank-tape halting predicate in the standard naturals.

`boundedCode` is chosen from a proved primitive-recursive representation,
not assumed to denote the clock. Its choice is noncomputable and no explicit
serialized code is exported. The final iPRA sentence is syntax only: no
object-level reduction to PA consistency, PA-internal totality theorem, or
equivalence in iPRA is asserted in this file.
-/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace PA196Bounded
abbrev Conf := ℕ × ℕ × ℕ

def rows : List (ℕ × ℕ × ℕ) := [
  (1, 1, 1),
  (1, 1, 61),
  (1, 1, 82),
  (1, 1, 1),
  (0, 0, 2),
  (1, 0, 3),
  (0, 0, 4),
  (1, 0, 3),
  (0, 0, 6),
  (1, 0, 3),
  (1, 1, 7),
  (0, 0, 5),
  (0, 0, 9),
  (1, 0, 3),
  (0, 1, 7),
  (0, 1, 10),
  (0, 1, 14),
  (1, 1, 13),
  (0, 0, 15),
  (1, 0, 3),
  (0, 0, 16),
  (0, 1, 10),
  (0, 0, 26),
  (1, 1, 18),
  (0, 1, 19),
  (1, 1, 20),
  (0, 0, 79),
  (1, 0, 31),
  (0, 0, 11),
  (0, 1, 22),
  (0, 0, 23),
  (1, 0, 3),
  (1, 0, 2),
  (0, 0, 2),
  (0, 1, 24),
  (0, 1, 32),
  (0, 1, 84),
  (0, 0, 95),
  (0, 1, 28),
  (1, 1, 29),
  (0, 1, 30),
  (1, 1, 31),
  (0, 1, 24),
  (0, 1, 57),
  (0, 1, 33),
  (1, 1, 22),
  (0, 0, 34),
  (1, 0, 3),
  (0, 0, 35),
  (0, 1, 1),
  (0, 1, 36),
  (1, 1, 25),
  (0, 1, 122),
  (1, 1, 41),
  (0, 1, 38),
  (0, 0, 39),
  (0, 1, 40),
  (1, 1, 41),
  (0, 1, 42),
  (1, 1, 43),
  (0, 1, 44),
  (1, 1, 45),
  (0, 1, 21),
  (1, 1, 46),
  (0, 1, 47),
  (1, 1, 32),
  (0, 1, 32),
  (1, 1, 33),
  (0, 0, 69),
  (1, 0, 3),
  (1, 1, 35),
  (1, 0, 2),
  (0, 1, 49),
  (1, 1, 36),
  (0, 1, 28),
  (1, 1, 20),
  (0, 0, 11),
  (0, 1, 36),
  (0, 0, 5),
  (1, 0, 51),
  (0, 1, 24),
  (0, 1, 25),
  (0, 1, 13),
  (0, 0, 16),
  (0, 1, 53),
  (1, 1, 54),
  (0, 1, 55),
  (1, 1, 56),
  (0, 1, 24),
  (0, 1, 52),
  (0, 1, 58),
  (1, 1, 59),
  (0, 1, 60),
  (0, 0, 16),
  (0, 1, 25),
  (1, 1, 47),
  (0, 0, 35),
  (0, 1, 61),
  (0, 1, 16),
  (1, 1, 49),
  (0, 1, 63),
  (1, 1, 64),
  (0, 0, 39),
  (1, 0, 51),
  (0, 1, 22),
  (1, 1, 52),
  (0, 0, 11),
  (0, 1, 49),
  (0, 1, 58),
  (0, 0, 16),
  (0, 1, 65),
  (1, 1, 66),
  (0, 1, 59),
  (1, 1, 67),
  (0, 1, 52),
  (1, 1, 57),
  (0, 1, 48),
  (0, 1, 25),
  (0, 0, 28),
  (1, 0, 68),
  (0, 0, 102),
  (1, 0, 30),
  (0, 1, 0),
  (1, 1, 61),
  (1, 1, 125),
  (1, 0, 51),
  (0, 1, 70),
  (1, 1, 196),
  (0, 0, 126),
  (1, 1, 31),
  (0, 1, 40),
  (1, 1, 60),
  (0, 0, 79),
  (1, 1, 71),
  (0, 1, 53),
  (1, 0, 72),
  (0, 1, 73),
  (1, 1, 74),
  (0, 1, 69),
  (1, 1, 75),
  (0, 1, 76),
  (1, 1, 77),
  (0, 1, 79),
  (1, 0, 110),
  (0, 0, 98),
  (1, 1, 54),
  (0, 1, 48),
  (0, 1, 33),
  (0, 1, 81),
  (0, 0, 41),
  (0, 1, 50),
  (1, 1, 132),
  (0, 1, 130),
  (1, 1, 21),
  (0, 1, 101),
  (1, 1, 90),
  (0, 1, 92),
  (1, 1, 93),
  (0, 1, 73),
  (1, 1, 72),
  (0, 1, 91),
  (1, 1, 119),
  (0, 1, 95),
  (1, 1, 96),
  (0, 1, 62),
  (0, 1, 1),
  (0, 1, 27),
  (1, 1, 97),
  (0, 1, 89),
  (1, 1, 88),
  (1, 0, 99),
  (1, 0, 85),
  (0, 1, 19),
  (1, 1, 100),
  (0, 1, 58),
  (1, 1, 58),
  (0, 1, 117),
  (1, 1, 115),
  (0, 0, 26),
  (1, 1, 195),
  (0, 1, 95),
  (0, 0, 131),
  (0, 1, 102),
  (1, 1, 103),
  (0, 1, 67),
  (1, 1, 56),
  (0, 1, 55),
  (1, 1, 104),
  (0, 1, 21),
  (1, 1, 105),
  (0, 1, 21),
  (0, 0, 10),
  (0, 1, 59),
  (1, 1, 41),
  (0, 1, 106),
  (1, 1, 8),
  (0, 1, 91),
  (1, 1, 107),
  (0, 0, 131),
  (0, 0, 85),
  (0, 1, 108),
  (1, 1, 94),
  (0, 0, 109),
  (0, 0, 2),
  (0, 1, 38),
  (1, 1, 68),
  (0, 1, 59),
  (1, 1, 110),
  (0, 1, 59),
  (1, 1, 111),
  (0, 1, 66),
  (0, 0, 16),
  (0, 1, 14),
  (1, 1, 110),
  (0, 1, 21),
  (1, 1, 112),
  (0, 1, 113),
  (1, 0, 20),
  (0, 1, 30),
  (1, 1, 65),
  (0, 1, 38),
  (1, 0, 108),
  (0, 1, 121),
  (0, 0, 16),
  (0, 1, 114),
  (0, 0, 16),
  (0, 1, 24),
  (0, 1, 47),
  (0, 1, 48),
  (0, 1, 32),
  (0, 1, 70),
  (1, 1, 86),
  (0, 1, 19),
  (1, 1, 118),
  (0, 1, 126),
  (1, 1, 28),
  (0, 1, 122),
  (1, 1, 107),
  (0, 1, 94),
  (1, 1, 86),
  (0, 1, 83),
  (1, 1, 98),
  (0, 1, 87),
  (1, 1, 87),
  (0, 1, 17),
  (1, 0, 109),
  (0, 1, 70),
  (1, 1, 101),
  (0, 1, 96),
  (1, 1, 108),
  (1, 0, 39),
  (1, 0, 99),
  (0, 1, 80),
  (1, 1, 78),
  (0, 1, 120),
  (1, 1, 133),
  (0, 1, 124),
  (1, 1, 123),
  (0, 1, 123),
  (1, 1, 128),
  (0, 1, 44),
  (1, 1, 90),
  (0, 0, 5),
  (0, 0, 131),
  (0, 1, 127),
  (1, 1, 59),
  (0, 1, 11),
  (1, 1, 37),
  (0, 1, 78),
  (1, 1, 58),
  (0, 1, 134),
  (1, 1, 58),
  (0, 1, 86),
  (1, 1, 135),
  (0, 1, 12),
  (1, 1, 136),
  (0, 0, 168),
  (1, 1, 140),
  (0, 1, 116),
  (1, 1, 140),
  (0, 0, 158),
  (1, 1, 78),
  (0, 1, 140),
  (1, 1, 137),
  (0, 1, 139),
  (1, 1, 141),
  (0, 1, 138),
  (1, 1, 142),
  (0, 1, 19),
  (1, 1, 160),
  (0, 1, 144),
  (1, 1, 136),
  (0, 1, 145),
  (1, 1, 144),
  (0, 1, 143),
  (1, 1, 138),
  (0, 1, 126),
  (1, 1, 147),
  (0, 1, 116),
  (1, 1, 135),
  (0, 1, 12),
  (1, 1, 149),
  (0, 1, 136),
  (1, 1, 137),
  (0, 1, 149),
  (1, 1, 78),
  (0, 1, 86),
  (1, 1, 134),
  (0, 1, 152),
  (1, 1, 183),
  (0, 1, 150),
  (1, 1, 174),
  (0, 1, 148),
  (1, 1, 155),
  (0, 1, 78),
  (1, 1, 156),
  (0, 1, 157),
  (1, 1, 150),
  (0, 1, 116),
  (1, 1, 153),
  (0, 1, 58),
  (1, 0, 185),
  (0, 1, 141),
  (1, 1, 58),
  (0, 1, 160),
  (1, 1, 161),
  (0, 1, 139),
  (1, 1, 162),
  (0, 1, 162),
  (1, 1, 163),
  (0, 1, 158),
  (1, 1, 164),
  (0, 1, 86),
  (1, 1, 165),
  (0, 1, 146),
  (1, 1, 159),
  (0, 1, 166),
  (1, 1, 167),
  (0, 1, 12),
  (1, 1, 168),
  (0, 1, 58),
  (1, 1, 139),
  (0, 1, 151),
  (1, 1, 161),
  (0, 1, 170),
  (1, 1, 171),
  (0, 1, 172),
  (1, 1, 137),
  (0, 0, 172),
  (1, 1, 154),
  (0, 1, 174),
  (1, 1, 183),
  (0, 1, 173),
  (1, 1, 175),
  (0, 1, 176),
  (1, 1, 154),
  (0, 1, 169),
  (1, 1, 177),
  (0, 0, 142),
  (1, 1, 159),
  (0, 1, 179),
  (1, 1, 179),
  (0, 1, 178),
  (1, 1, 180),
  (0, 1, 64),
  (1, 1, 181),
  (0, 0, 158),
  (1, 0, 167),
  (0, 1, 183),
  (1, 1, 78),
  (0, 1, 179),
  (1, 1, 184),
  (0, 1, 145),
  (1, 1, 185),
  (0, 1, 184),
  (1, 1, 186),
  (0, 1, 116),
  (1, 1, 187),
  (0, 1, 183),
  (1, 1, 122),
  (0, 1, 152),
  (1, 1, 189),
  (0, 1, 188),
  (1, 1, 190),
  (0, 1, 182),
  (1, 1, 191),
  (0, 1, 129),
  (0, 0, 131),
  (0, 1, 192),
  (1, 1, 193),
  (0, 1, 137),
  (1, 1, 194)
]
theorem table_matches_literal : ∀ q : Fin 196, ∀ b : Bool,
    rows.getD (2*q.val + b.toNat) (0,0,196) =
      ((PA196.Literal.transition q.val b).1.toNat,
       (PA196.Literal.transition q.val b).2.1.toNat,
       (PA196.Literal.transition q.val b).2.2) := by decide +kernel

def row (c : Conf) : ℕ × ℕ × ℕ :=
  rows.getD (2*c.1 + c.2.2%2) (0,0,196)
def next (c : Conf) : Conf :=
  if c.1 < 196 then
    let a := row c
    if a.2.1 = 1 then (a.2.2,2*c.2.1+a.1,c.2.2/2)
    else (a.2.2,c.2.1/2,c.2.1%2+2*(a.1+2*(c.2.2/2)))
  else c

theorem primrec_row : Primrec row := by
  unfold row
  have hq : Primrec (fun c : Conf => c.1) := Primrec.fst
  have hr : Primrec (fun c : Conf => c.2.2) := Primrec.snd.comp Primrec.snd
  have hb : Primrec (fun c : Conf => c.2.2 % 2) := Primrec.nat_mod.comp hr (Primrec.const 2)
  have hi : Primrec (fun c : Conf => 2 * c.1 + c.2.2 % 2) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hq) hb
  exact (Primrec.list_getD (0,0,196)).comp (Primrec.const rows) hi

theorem primrec_next : Primrec next := by
  have hq : Primrec (fun c : Conf => c.1) := Primrec.fst
  have hl : Primrec (fun c : Conf => c.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun c : Conf => c.2.2) := Primrec.snd.comp Primrec.snd
  have ha : Primrec row := primrec_row
  have hw : Primrec (fun c : Conf => (row c).1) := Primrec.fst.comp ha
  have hd : Primrec (fun c : Conf => (row c).2.1) := Primrec.fst.comp (Primrec.snd.comp ha)
  have hn : Primrec (fun c : Conf => (row c).2.2) := Primrec.snd.comp (Primrec.snd.comp ha)
  have hL : Primrec (fun c : Conf => 2 * c.2.1 + (row c).1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) hl) hw
  have hR : Primrec (fun c : Conf => c.2.2 / 2) := Primrec.nat_div.comp hr (Primrec.const 2)
  have hLL : Primrec (fun c : Conf => c.2.1 / 2) := Primrec.nat_div.comp hl (Primrec.const 2)
  have hRR : Primrec (fun c : Conf => c.2.1 % 2 + 2 * ((row c).1 + 2 * (c.2.2 / 2))) :=
    Primrec.nat_add.comp (Primrec.nat_mod.comp hl (Primrec.const 2))
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec.nat_add.comp hw (Primrec.nat_mul.comp (Primrec.const 2) hR)))
  have hright : Primrec (fun c : Conf => ((row c).2.2,2*c.2.1+(row c).1,c.2.2/2)) := hn.pair (hL.pair hR)
  have hleft : Primrec (fun c : Conf => ((row c).2.2,c.2.1/2,c.2.1%2+2*((row c).1+2*(c.2.2/2)))) := hn.pair (hLL.pair hRR)
  have hbody : Primrec (fun c : Conf => if (row c).2.1 = 1 then ((row c).2.2,2*c.2.1+(row c).1,c.2.2/2) else ((row c).2.2,c.2.1/2,c.2.1%2+2*((row c).1+2*(c.2.2/2)))) :=
    Primrec.ite (Primrec.eq.comp hd (Primrec.const 1)) hright hleft
  exact (Primrec.ite (Primrec.nat_lt.comp hq (Primrec.const 196)) hbody Primrec.id).of_eq (by intro c; rfl)

def run (n : ℕ) : Conf := Nat.rec (0,0,0) (fun _ c => next c) n

theorem primrec_run : Primrec run := by
  exact Primrec.nat_rec₁ (0,0,0) (Primrec.comp₂ primrec_next Primrec₂.right)

def bounded (n : ℕ) : ℕ := if 196 ≤ (run n).1 then 1 else 0

theorem primrec_bounded : Primrec bounded := by
  apply Primrec.ite
  · exact Primrec.nat_le.comp (Primrec.const 196) (Primrec.fst.comp primrec_run)
  · exact Primrec.const 1
  · exact Primrec.const 0


/-- Tape sides are binary numerals whose least significant bit is nearest the head. -/
def bits : List Bool → ℕ
  | [] => 0
  | b :: bs => b.toNat + 2 * bits bs

theorem bits_trim (bs : List Bool) : bits (M6.Zip.trim bs) = bits bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [M6.Zip.trim]
    split
    next h =>
      have hz : bits bs = 0 := by rw [← ih, h.2]; rfl
      simp [h.1, bits, hz]
    next h => simp [bits, ih]

theorem bits_head (bs : List Bool) : bits bs % 2 = (bs.headD false).toNat := by
  cases bs with
  | nil => rfl
  | cons b bs => cases b <;> simp [bits]

theorem bits_tail (bs : List Bool) : bits bs / 2 = bits bs.tail := by
  cases bs with
  | nil => rfl
  | cons b bs =>
    cases b with
    | false => simp [bits]
    | true => simp only [bits, List.tail_cons, Bool.toNat_true]; omega

def encodeZip (c : M6.Zip.Conf) : Conf := (c.q, bits c.l, bits c.r)
def zipTotalStep (c : M6.Zip.Conf) : M6.Zip.Conf :=
  (M6.Zip.step PA196.Literal.machine c).getD c

set_option linter.unnecessarySeqFocus false in
/-- The numeric transition agrees on every finite-support zipper tape. -/
theorem zip_step_binding (c : M6.Zip.Conf) : next (encodeZip c) = encodeZip (zipTotalStep c) := by
  by_cases hq : c.q < 196
  · have ht := table_matches_literal ⟨c.q, hq⟩ (c.r.headD false)
    have hr : row (encodeZip c) =
        ((PA196.Literal.transition c.q (c.r.headD false)).1.toNat,
         (PA196.Literal.transition c.q (c.r.headD false)).2.1.toNat,
         (PA196.Literal.transition c.q (c.r.headD false)).2.2) := by
      simpa only [row, encodeZip, bits_head] using ht
    change row (c.q, bits c.l, bits c.r) = _ at hr
    simp only [next, encodeZip, hq, ↓reduceIte]
    rw [hr]
    simp only [zipTotalStep, M6.Zip.step, PA196.Literal.machine, hq, ↓reduceIte]
    generalize he : PA196.Literal.transition c.q (c.r.headD false) = a at *
    rcases a with ⟨w,d,q'⟩
    cases w <;> cases d <;>
      simp [M6.Zip.zc, M6.Zip.zl, bits_trim, bits, bits_head, bits_tail] <;> omega
  · simp [next, encodeZip, hq, zipTotalStep, M6.Zip.step, PA196.Literal.machine]


def blankZip : M6.Zip.Conf := ⟨0, [], []⟩
def zipRun (n : ℕ) : M6.Zip.Conf := Nat.rec blankZip (fun _ c => zipTotalStep c) n

theorem zip_run_binding (n : ℕ) : encodeZip (zipRun n) = run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change encodeZip (zipTotalStep (zipRun n)) = next (run n)
    rw [← zip_step_binding, ih]

theorem zip_run_before (n : ℕ) (h : ∀ i < n, (zipRun i).q < 196) :
    M6.Zip.run PA196.Literal.machine n blankZip = some (zipRun n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := h n (by omega)
    have old := ih (by intro i hi; exact h i (by omega))
    cases he : M6.Zip.step PA196.Literal.machine (zipRun n) with
    | none =>
      have hne : M6.Zip.step PA196.Literal.machine (zipRun n) ≠ none := by
        simp only [M6.Zip.step, PA196.Literal.machine, hs, ↓reduceIte]
        rcases htr : PA196.Literal.transition (zipRun n).q ((zipRun n).r.headD false) with ⟨w,d,q⟩
        cases d <;> simp
      exact False.elim (hne he)
    | some c =>
      have hrun : M6.Zip.run PA196.Literal.machine (n+1) blankZip = some c := by
        rw [M6.Zip.run_add, old]
        simp [M6.Zip.run, he]
      change M6.Zip.run PA196.Literal.machine (n+1) blankZip = some (zipTotalStep (zipRun n))
      rw [zipTotalStep, he]
      exact hrun

theorem zip_run_some (n : ℕ) (c : M6.Zip.Conf)
    (h : M6.Zip.run PA196.Literal.machine n blankZip = some c) : zipRun n = c := by
  induction n generalizing c with
  | zero => simpa [M6.Zip.run, zipRun] using h
  | succ n ih =>
    rw [M6.Zip.run_add] at h
    cases he : M6.Zip.run PA196.Literal.machine n blankZip with
    | none => simp [he] at h
    | some prev =>
      simp only [he] at h
      cases hs : M6.Zip.step PA196.Literal.machine prev with
      | none => simp [M6.Zip.run, hs] at h
      | some dest =>
        have hd : dest = c := by simpa [M6.Zip.run, hs] using h
        have hp : zipRun n = prev := ih prev he
        change zipTotalStep (zipRun n) = c
        rw [hp, zipTotalStep, hs]
        exact hd

theorem bounded_eq_one (n : ℕ) : bounded n = 1 ↔ 196 ≤ (run n).1 := by
  simp [bounded]

/-- The bounded numeric semantics is exactly the imported literal Zip halting predicate. -/
theorem exists_bounded_iff_literal_halts :
    (∃ n, bounded n = 1) ↔ M6.Zip.Halts PA196.Literal.machine blankZip := by
  constructor
  · intro ⟨n, hn⟩
    have hex : ∃ n, 196 ≤ (zipRun n).q := by
      refine ⟨n, ?_⟩
      have hh := (bounded_eq_one n).mp hn
      simpa [← zip_run_binding, encodeZip] using hh
    let k := Nat.find hex
    have hk : 196 ≤ (zipRun k).q := Nat.find_spec hex
    have hbefore : ∀ i < k, (zipRun i).q < 196 := by
      intro i hi
      have hn := Nat.find_min hex hi
      omega
    have hr := zip_run_before k hbefore
    refine ⟨zipRun k, ⟨k, hr⟩, ?_⟩
    simp [M6.Zip.step, PA196.Literal.machine, show ¬(zipRun k).q < 196 by omega]
  · intro ⟨c, ⟨n, hn⟩, hh⟩
    have hq : ¬c.q < 196 := by
      intro hlt
      simp only [M6.Zip.step, PA196.Literal.machine, hlt, ↓reduceIte] at hh
      rcases htr : PA196.Literal.transition c.q (c.r.headD false) with ⟨w,d,q⟩
      rw [htr] at hh
      cases d <;> simp at hh
    have hr := zip_run_some n c hn
    refine ⟨n, (bounded_eq_one n).mpr ?_⟩
    have eqn := zip_run_binding n
    have heq : (run n).1 = c.q := by simpa [encodeZip, hr] using congrArg Prod.fst eqn.symm
    omega


open DiophantineConsistency.PRAFiniteFunctionCodes
open DiophantineConsistency.PRALanguage
open LO LO.FirstOrder
open scoped LO.FirstOrder
open List.Vector

theorem bounded_vector_primrec : Primrec (fun v : List.Vector ℕ 1 => bounded v.head) :=
  primrec_bounded.comp Primrec.vector_head

/-- One actual iPRA function-code whose standard interpretation is this clock. -/
noncomputable def boundedCode : Code 1 :=
  Classical.choose (exists_code_of_primrec bounded_vector_primrec)

theorem boundedCode_spec : eval boundedCode = fun v : List.Vector ℕ 1 => bounded v.head :=
  Classical.choose_spec (exists_code_of_primrec bounded_vector_primrec)

theorem boundedCode_eval (n : ℕ) : eval boundedCode (n ::ᵥ nil) = bounded n := by
  rw [boundedCode_spec]
  rfl

noncomputable def boundedTerm : Semiterm language Empty 1 := .func boundedCode (fun _ => #0)
noncomputable def haltSentence : Sentenceᵢ language :=
  ∃⁰ (.rel .eq ![boundedTerm, .func oneCode Fin.elim0])

theorem boundedTerm_val (n : ℕ) :
    letI : Structure language ℕ := natStructure
    Semiterm.val ![n] Empty.elim boundedTerm = bounded n := by
  change eval boundedCode (List.Vector.ofFn ![n]) = bounded n
  have hv : List.Vector.ofFn ![n] = n ::ᵥ nil := by
    ext i
    cases i using Fin.cases with
    | zero => rfl
    | succ j => exact Fin.elim0 j
  rw [hv, boundedCode_eval]

theorem code_halts_iff_literal :
    (∃ n, eval boundedCode (n ::ᵥ nil) = 1) ↔
      M6.Zip.Halts PA196.Literal.machine blankZip := by
  simpa only [boundedCode_eval] using exists_bounded_iff_literal_halts

/-- The actual iPRA-language term has the same standard-Nat halting test. -/
theorem term_halts_iff_literal :
    letI : Structure language ℕ := natStructure
    (∃ n, Semiterm.val ![n] Empty.elim boundedTerm = 1) ↔
      M6.Zip.Halts PA196.Literal.machine blankZip := by
  simpa only [boundedTerm_val] using exists_bounded_iff_literal_halts

end PA196Bounded
