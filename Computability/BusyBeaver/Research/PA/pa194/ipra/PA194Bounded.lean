import DiophantineConsistency.PRALanguage
import PA194Literal
import PA194Rows
import Mathlib.Computability.Primrec.List

/-! Primitive-recursive bounded halting for the pinned PA194 literal table.
The standard-natural-number bridge proves equivalence with M6.Zip halting.
The generated machine and numeric table are independently kernel-compared.
The chosen function code is noncomputable; no iPRA machine reduction is proved. -/
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0
namespace PA194Bounded
abbrev Conf := ℕ × ℕ × ℕ

def rows : List (ℕ × ℕ × ℕ) := PA194Rows.rows
theorem table_matches_literal : ∀ q : Fin 194, ∀ b : Bool,
    rows.getD (2*q.val + b.toNat) (0,0,194) =
      ((PA194.Literal.transition q.val b).1.toNat,
       (PA194.Literal.transition q.val b).2.1.toNat,
       (PA194.Literal.transition q.val b).2.2) := by decide +kernel

def row (c : Conf) : ℕ × ℕ × ℕ :=
  rows.getD (2*c.1 + c.2.2%2) (0,0,194)
def next (c : Conf) : Conf :=
  if c.1 < 194 then
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
  exact (Primrec.list_getD (0,0,194)).comp (Primrec.const rows) hi

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
  exact (Primrec.ite (Primrec.nat_lt.comp hq (Primrec.const 194)) hbody Primrec.id).of_eq (by intro c; rfl)

def run (n : ℕ) : Conf := Nat.rec (0,0,0) (fun _ c => next c) n

theorem primrec_run : Primrec run := by
  exact Primrec.nat_rec₁ (0,0,0) (Primrec.comp₂ primrec_next Primrec₂.right)

def bounded (n : ℕ) : ℕ := if 194 ≤ (run n).1 then 1 else 0

theorem primrec_bounded : Primrec bounded := by
  apply Primrec.ite
  · exact Primrec.nat_le.comp (Primrec.const 194) (Primrec.fst.comp primrec_run)
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
  (M6.Zip.step PA194.Literal.machine c).getD c

set_option linter.unnecessarySeqFocus false in
/-- The numeric transition agrees on every finite-support zipper tape. -/
theorem zip_step_binding (c : M6.Zip.Conf) : next (encodeZip c) = encodeZip (zipTotalStep c) := by
  by_cases hq : c.q < 194
  · have ht := table_matches_literal ⟨c.q, hq⟩ (c.r.headD false)
    have hr : row (encodeZip c) =
        ((PA194.Literal.transition c.q (c.r.headD false)).1.toNat,
         (PA194.Literal.transition c.q (c.r.headD false)).2.1.toNat,
         (PA194.Literal.transition c.q (c.r.headD false)).2.2) := by
      simpa only [row, encodeZip, bits_head] using ht
    change row (c.q, bits c.l, bits c.r) = _ at hr
    simp only [next, encodeZip, hq, ↓reduceIte]
    rw [hr]
    simp only [zipTotalStep, M6.Zip.step, PA194.Literal.machine, hq, ↓reduceIte]
    generalize he : PA194.Literal.transition c.q (c.r.headD false) = a at *
    rcases a with ⟨w,d,q'⟩
    cases w <;> cases d <;>
      simp [M6.Zip.zc, M6.Zip.zl, bits_trim, bits, bits_head, bits_tail] <;> omega
  · simp [next, encodeZip, hq, zipTotalStep, M6.Zip.step, PA194.Literal.machine]


def blankZip : M6.Zip.Conf := ⟨0, [], []⟩
def zipRun (n : ℕ) : M6.Zip.Conf := Nat.rec blankZip (fun _ c => zipTotalStep c) n

theorem zip_run_binding (n : ℕ) : encodeZip (zipRun n) = run n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change encodeZip (zipTotalStep (zipRun n)) = next (run n)
    rw [← zip_step_binding, ih]

theorem zip_run_before (n : ℕ) (h : ∀ i < n, (zipRun i).q < 194) :
    M6.Zip.run PA194.Literal.machine n blankZip = some (zipRun n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hs := h n (by omega)
    have old := ih (by intro i hi; exact h i (by omega))
    cases he : M6.Zip.step PA194.Literal.machine (zipRun n) with
    | none =>
      have hne : M6.Zip.step PA194.Literal.machine (zipRun n) ≠ none := by
        simp only [M6.Zip.step, PA194.Literal.machine, hs, ↓reduceIte]
        rcases htr : PA194.Literal.transition (zipRun n).q ((zipRun n).r.headD false) with ⟨w,d,q⟩
        cases d <;> simp
      exact False.elim (hne he)
    | some c =>
      have hrun : M6.Zip.run PA194.Literal.machine (n+1) blankZip = some c := by
        rw [M6.Zip.run_add, old]
        simp [M6.Zip.run, he]
      change M6.Zip.run PA194.Literal.machine (n+1) blankZip = some (zipTotalStep (zipRun n))
      rw [zipTotalStep, he]
      exact hrun

theorem zip_run_some (n : ℕ) (c : M6.Zip.Conf)
    (h : M6.Zip.run PA194.Literal.machine n blankZip = some c) : zipRun n = c := by
  induction n generalizing c with
  | zero => simpa [M6.Zip.run, zipRun] using h
  | succ n ih =>
    rw [M6.Zip.run_add] at h
    cases he : M6.Zip.run PA194.Literal.machine n blankZip with
    | none => simp [he] at h
    | some prev =>
      simp only [he] at h
      cases hs : M6.Zip.step PA194.Literal.machine prev with
      | none => simp [M6.Zip.run, hs] at h
      | some dest =>
        have hd : dest = c := by simpa [M6.Zip.run, hs] using h
        have hp : zipRun n = prev := ih prev he
        change zipTotalStep (zipRun n) = c
        rw [hp, zipTotalStep, hs]
        exact hd

theorem bounded_eq_one (n : ℕ) : bounded n = 1 ↔ 194 ≤ (run n).1 := by
  simp [bounded]

/-- The bounded numeric semantics is exactly the imported literal Zip halting predicate. -/
theorem exists_bounded_iff_literal_halts :
    (∃ n, bounded n = 1) ↔ M6.Zip.Halts PA194.Literal.machine blankZip := by
  constructor
  · intro ⟨n, hn⟩
    have hex : ∃ n, 194 ≤ (zipRun n).q := by
      refine ⟨n, ?_⟩
      have hh := (bounded_eq_one n).mp hn
      simpa [← zip_run_binding, encodeZip] using hh
    let k := Nat.find hex
    have hk : 194 ≤ (zipRun k).q := Nat.find_spec hex
    have hbefore : ∀ i < k, (zipRun i).q < 194 := by
      intro i hi
      have hn := Nat.find_min hex hi
      omega
    have hr := zip_run_before k hbefore
    refine ⟨zipRun k, ⟨k, hr⟩, ?_⟩
    simp [M6.Zip.step, PA194.Literal.machine, show ¬(zipRun k).q < 194 by omega]
  · intro ⟨c, ⟨n, hn⟩, hh⟩
    have hq : ¬c.q < 194 := by
      intro hlt
      simp only [M6.Zip.step, PA194.Literal.machine, hlt, ↓reduceIte] at hh
      rcases htr : PA194.Literal.transition c.q (c.r.headD false) with ⟨w,d,q⟩
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
      M6.Zip.Halts PA194.Literal.machine blankZip := by
  simpa only [boundedCode_eval] using exists_bounded_iff_literal_halts

/-- The actual iPRA-language term has the same standard-Nat halting test. -/
theorem term_halts_iff_literal :
    letI : Structure language ℕ := natStructure
    (∃ n, Semiterm.val ![n] Empty.elim boundedTerm = 1) ↔
      M6.Zip.Halts PA194.Literal.machine blankZip := by
  simpa only [boundedTerm_val] using exists_bounded_iff_literal_halts

end PA194Bounded
