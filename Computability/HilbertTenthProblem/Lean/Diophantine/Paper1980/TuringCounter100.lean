import Diophantine.Paper1980.TuringStack100

/-!
# A three-counter program simulating a Turing machine

`EXPLORATION_THREE_RAW_COUNTER_UNIVERSAL_COMPILER.md`, §§2–3: from `(x, 0, 0)` the loader moves
the binary digits of `x` onto `B`, most significant on top; then, at every simulated step, `A`
holds the tape strictly left of the head and `B` the head cell and the cells to its right,
nearest on top, with `C = 0`.  A step pops `B` for the scanned symbol and, by the finite
table, writes (push on `B`), moves right (push the scanned symbol on `A`), or moves left (pop
`A`, push the scanned symbol and then the popped one on `B`).  On a halt the registers are
cleared and the accepting halt is entered.

Here the machine is Mathlib's `Turing.TM0` with finite symbol and state types, and the program
`prog` is laid out in blocks of a fixed stride: the loader, the two bit pushes, the cleanup,
one pop block per state, one dispatch block per state and digit, and one left-move block per
state and pair of digits.  `accepts_iff` is §3's conclusion: the program accepts `x` exactly
when the machine halts on the binary digits of `x`, most significant first.
-/

namespace Jones1980

open Turing TMStack

namespace TMCounter

variable {Γ Λ : Type} [Inhabited Γ] [Fintype Γ] [Inhabited Λ] [Fintype Λ]

variable (Γ) in
/-- The block stride. -/
def S : ℕ := 4 * base Γ + 10

variable (Γ) in
/-- The offset of the second push of a left move. -/
def P : ℕ := 2 * base Γ + 4

variable (Λ) in
/-- The number of states. -/
def nQ : ℕ := Fintype.card Λ

/-- The index of a state. -/
noncomputable def qi (q : Λ) : ℕ := Fintype.equivFin Λ q

variable (Λ) in
/-- The state of an index. -/
noncomputable def qs (i : ℕ) : Λ :=
  if h : i < Fintype.card Λ then (Fintype.equivFin Λ).symm ⟨i, h⟩ else default

theorem qi_lt (q : Λ) : qi q < nQ Λ := (Fintype.equivFin Λ q).isLt

theorem qs_qi (q : Λ) : qs Λ (qi q) = q := by
  unfold qs qi
  rw [dif_pos (Fintype.equivFin Λ q).isLt]
  simp

variable (Γ) in
/-- The dispatch block of state index `i` and digit `j`. -/
def dispId (i j : ℕ) : ℕ := 4 + nQ Λ + i * base Γ + j

variable (Γ Λ) in
/-- The left-move block of state index `i` and digits `j`, `j'`. -/
def leftId (i j j' : ℕ) : ℕ := 4 + nQ Λ + nQ Λ * base Γ + (i * base Γ + j) * base Γ + j'

variable (Γ Λ) in
/-- The number of blocks. -/
def nBlocks : ℕ := 4 + nQ Λ + nQ Λ * base Γ + nQ Λ * base Γ * base Γ

variable (TM : TM0.Machine Γ Λ) (enc : Bool → Γ) (pre : List Γ)

/-- The dispatch block of a state and a scanned digit. -/
noncomputable def dispCode (q : Λ) (j ℓ o : ℕ) : CInstr :=
  match TM q (sym j) with
  | none => .test 2 (S Γ * 3) (S Γ * 3)
  | some (q', .write a) => CProgram.pushM 1 2 (base Γ) (code a) ℓ (S Γ * (4 + qi q')) o
  | some (q', .move .right) =>
      CProgram.pushM 0 2 (base Γ) (code (sym (Γ := Γ) j)) ℓ (S Γ * (4 + qi q')) o
  | some (_, .move .left) =>
      CProgram.popM 0 2 (base Γ) ℓ (fun j' => S Γ * leftId Γ Λ (qi q) j j') o

/-- The left-move block: push the scanned symbol, then the popped one. -/
noncomputable def leftCode (q : Λ) (j j' ℓ o : ℕ) : CInstr :=
  match TM q (sym j) with
  | some (q', .move .left) =>
      if o < P Γ then CProgram.pushM 1 2 (base Γ) (code (sym (Γ := Γ) j)) ℓ (ℓ + P Γ) o
      else CProgram.pushM 1 2 (base Γ) (code (sym (Γ := Γ) j')) (ℓ + P Γ) (S Γ * (4 + qi q'))
        (o - P Γ)
  | _ => .stop

variable (Γ) in
/-- The cleanup block. -/
def cleanCode (o : ℕ) : CInstr :=
  if o = 0 then .test 0 (S Γ * 3 + 1) (S Γ * 3)
  else if o = 1 then .test 1 (S Γ * 3 + 2) (S Γ * 3 + 1)
  else if o = 2 then .test 2 (S Γ * 3 + 3) (S Γ * 3 + 2)
  else .accept

/-- Where the loader goes when it is done: the first prefix push, or the initial state's loop. -/
noncomputable def startAddr : ℕ :=
  if pre.length = 0 then S Γ * (4 + qi (default : Λ)) else S Γ * nBlocks Γ Λ

/-- The instruction at offset `o` of block `i`. -/
noncomputable def blockCode (i o : ℕ) : CInstr :=
  if i = 0 then
    (if o = 0 then .test 0 (startAddr (Λ := Λ) pre) 1
     else if o = 1 then .inc 0 2
     else CProgram.popM 0 2 2 2 (fun j => S Γ * (1 + j)) (o - 2))
  else if i < 3 then
    CProgram.pushM 1 2 (base Γ) (code (enc (decide (i - 1 = 1)))) (S Γ * i) 0 o
  else if i = 3 then cleanCode Γ o
  else if i < 4 + nQ Λ then
    CProgram.popM 1 2 (base Γ) (S Γ * i) (fun j => S Γ * dispId Γ (Λ := Λ) (i - 4) j) o
  else if i < 4 + nQ Λ + nQ Λ * base Γ then
    dispCode TM (qs Λ ((i - 4 - nQ Λ) / base Γ)) ((i - 4 - nQ Λ) % base Γ) (S Γ * i) o
  else if i < nBlocks Γ Λ then
    leftCode TM (qs Λ ((i - 4 - nQ Λ - nQ Λ * base Γ) / base Γ / base Γ))
      ((i - 4 - nQ Λ - nQ Λ * base Γ) / base Γ % base Γ)
      ((i - 4 - nQ Λ - nQ Λ * base Γ) % base Γ) (S Γ * i) o
  else if i < nBlocks Γ Λ + pre.length then
    CProgram.pushM 1 2 (base Γ) (code (pre.reverse.getD (i - nBlocks Γ Λ) default)) (S Γ * i)
      (if i + 1 < nBlocks Γ Λ + pre.length then S Γ * (i + 1) else S Γ * (4 + qi (default : Λ))) o
  else .stop

/-- **The simulating program.** -/
noncomputable def prog : CProgram :=
  ⟨S Γ * (nBlocks Γ Λ + pre.length), fun ℓ => blockCode TM enc pre (ℓ / S Γ) (ℓ % S Γ)⟩

/-! ### Placement -/

theorem S_pos : 0 < S Γ := by unfold S; omega

theorem placed {i size : ℕ} {f : ℕ → CInstr} (hi : i < nBlocks Γ Λ + pre.length) (hs : size ≤ S Γ)
    (hf : ∀ o, o < size → blockCode TM enc pre i o = f o) :
    (prog TM enc pre).Placed (S Γ * i) size f := by
  intro o ho
  have hS := S_pos (Γ := Γ)
  refine ⟨?_, ?_⟩
  · show S Γ * i + o < S Γ * (nBlocks Γ Λ + pre.length)
    have : S Γ * (i + 1) ≤ S Γ * (nBlocks Γ Λ + pre.length) := Nat.mul_le_mul_left _ hi
    rw [Nat.mul_succ] at this
    omega
  · show blockCode TM enc pre ((S Γ * i + o) / S Γ) ((S Γ * i + o) % S Γ) = f o
    rw [show S Γ * i + o = o + S Γ * i by ring, Nat.add_mul_div_left _ _ hS,
      Nat.add_mul_mod_self_left, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.zero_add]
    exact hf o ho

/-- Registers as a triple. -/
theorem reg_ext {w : Fin 3 → ℕ} {a b c : ℕ} (h0 : w 0 = a) (h1 : w 1 = b) (h2 : w 2 = c) :
    w = ![a, b, c] := by
  funext i
  fin_cases i <;> simp [h0, h1, h2]

theorem push_sz {d : ℕ} (hd : d < base Γ) : base Γ + 3 + d ≤ P Γ := by unfold P; omega

theorem base_pos : 0 < base Γ := by have := two_le_base Γ; omega

theorem div_mod_id {i j b : ℕ} (hb : 0 < b) (hj : j < b) : (i * b + j) / b = i ∧ (i * b + j) % b = j := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ hb, Nat.div_eq_of_lt hj, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

end TMCounter

end Jones1980
