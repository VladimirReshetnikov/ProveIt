import DiophantineConsistency.Bm2963.Bm2963Kernel
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.ReduceModChar

/-! # The block-mask2963 kernel modulo the controller modulus

`K ≡ 25047958135 (mod C0)`, `C0 = d·λ = 139261·1362521 = 189746036981`: the
residue premise of `Bm2963ConstructionUnit.gamma_unit` (the counterpart of
`Adm942KernelResidue.K_mod`).

The kernel is never materialized. With selectors at their index, the single
reflected selector band is one Horner fold of the 942 selector weights in
`ZMod C0` over `WangTiles942.orderedRows`, times `r^1015`
(`selector_reflection`: `ρ^(1956−j) = ρ^1015·ρ^(941−j)`); the 34 label weights
are a separate short sum times `r^971` (`control_reflection`). Both folds are
checked by `decide +kernel` (the selector fold in 20 chunks of 48 rows,
`run_chain`), and `2^47 mod C0` by `reduce_mod_char`. The
residue agrees with the recipe of
`research/block-mask2963-calibration/tools/check_recipe.py`. The fold
machinery (`evaluate`, `run`, `Control`, `controlReflection`) is the
admissible942 one, restated so that this module depends on the block-mask2963
kernel only. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
noncomputable section
namespace Bm2963KernelResidue
open DiophantineConsistency DiophantineConsistency.WangTiles942
open scoped BigOperators

/-- High-to-low evaluation of the selector weights of a row list. -/
def evaluate {R : Type*} [Semiring R] (r : R) : List (ℕ × Tile) → R
  | [] => 0
  | a :: l => (selectorWeight a.2 : R) * r ^ l.length + evaluate r l

theorem evaluate_sum {R : Type*} [CommSemiring R] (r : R) (l : List (ℕ × Tile)) :
    evaluate r l = ∑ j : Fin l.length, (selectorWeight l[j.val].2 : R) * r ^ (l.length - 1 - j.val) := by
  induction l with
  | nil => simp only [evaluate, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
  | cons a l ih =>
      simp only [List.length_cons, evaluate, Fin.sum_univ_succ, Fin.val_zero,
        List.getElem_cons_zero, Nat.add_sub_cancel, Nat.sub_zero, Fin.val_succ,
        List.getElem_cons_succ, ih]
      simp only [Nat.sub_sub, Nat.add_comm]

theorem evaluate_ordered {R : Type*} [CommSemiring R] (r : R) :
    evaluate r orderedRows = ∑ i : Fin 942, (selectorWeight (tile i) : R) * r ^ (941 - i.val) := by
  rw [evaluate_sum]
  refine Fintype.sum_equiv (finCongr ordered_count) _ _ (fun j => ?_)
  simp only [finCongr_apply, Fin.val_cast, tile, ordered_count]

/-- The single selector band, as one fold. -/
theorem selector_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ i : Fin 942, (selectorWeight (tile i) : R) * r ^ (1956 - i.val)) =
      evaluate r orderedRows * r ^ 1015 := by
  rw [evaluate_ordered, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hi := i.isLt
  rw [show 1956 - i.val = (941 - i.val) + 1015 by omega, pow_add]
  ring

/-- The 34 label entries. -/
abbrev Control := Fin 8 ⊕ (Fin 9 ⊕ (Fin 8 ⊕ Fin 9))

/-- The label weights, reflected at `985`. -/
def controlReflection {R : Type*} [CommSemiring R] (r : R) : R :=
  ∑ e : Control, (CurrentKernel2011.weight (.inr e) : R) * r ^ (985 - Bm2963Kernel.position (.inr e))

theorem control_reflection {R : Type*} [CommSemiring R] (r : R) :
    (∑ e : Control, (CurrentKernel2011.weight (.inr e) : R) *
      r ^ (1956 - Bm2963Kernel.position (.inr e))) =
      controlReflection r * r ^ 971 := by
  rw [controlReflection, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  have he := Bm2963Kernel.position_le (.inr e)
  rw [show 1956 - Bm2963Kernel.position (.inr e) = (985 - Bm2963Kernel.position (.inr e)) + 971 by
      omega, pow_add]
  ring

/-- The whole kernel over every commutative semiring, for an arbitrary radix. -/
theorem rawWord_cast {R : Type*} [CommSemiring R] (r : ℕ) :
    (Bm2963Kernel.rawWord r : R) =
      (r : R) ^ 18 + (r : R) ^ 1005 + (r : R) ^ 2972 +
        (evaluate (r : R) orderedRows * (r : R) ^ 1015 +
          controlReflection (r : R) * (r : R) ^ 971) := by
  rw [Bm2963Kernel.rawWord_eq]
  simp only [Nat.cast_add, Nat.cast_sum, Nat.cast_mul, Nat.cast_pow]
  rw [Fintype.sum_sum_type, ← selector_reflection, ← control_reflection]
  rfl

/-- The same fold as a linear Horner accumulator. -/
def run {R : Type*} [Semiring R] (r : R) : List (ℕ × Tile) → R → R
  | [], z => z
  | a :: l, z => run r l (z * r + (selectorWeight a.2 : R))

theorem run_eq {R : Type*} [CommSemiring R] (r : R) (l : List (ℕ × Tile)) (z : R) :
    run r l z = z * r ^ l.length + evaluate r l := by
  induction l generalizing z with
  | nil => simp [run, evaluate]
  | cons a l ih =>
    rw [run, ih, evaluate, List.length_cons, pow_succ]
    ring

theorem evaluate_eq_run {R : Type*} [CommSemiring R] (r : R) (l : List (ℕ × Tile)) :
    evaluate r l = run r l 0 := by
  simp only [run_eq, zero_mul, zero_add]

/-! The modulus `C0` is written as the literal `189746036981` everywhere: with an
`abbrev` for it, the kernel check of `K_mod` compared `K % C0` with
`K % 189746036981` by evaluating `K` (more than 4.5 GB here; probably why the
admissible942 module, built that way, took 31 minutes). -/

theorem run_append {R : Type*} [Semiring R] (r : R) (l₁ l₂ : List (ℕ × Tile)) (z : R) :
    run r (l₁ ++ l₂) z = run r l₂ (run r l₁ z) := by
  induction l₁ generalizing z with
  | nil => rfl
  | cons a l ih => exact ih _

theorem drop_drop' {α : Type*} : ∀ (a k : ℕ) (l : List α), (l.drop a).drop k = l.drop (a + k)
  | 0, k, l => by simp
  | _ + 1, k, [] => by simp
  | a + 1, k, x :: l => by
    rw [List.drop_succ_cons, drop_drop' a k l, show a + 1 + k = (a + k) + 1 by omega,
      List.drop_succ_cons]

/-- One chunk of the fold: the next `k` rows. -/
theorem run_chain {R : Type*} [Semiring R] (r : R) (l : List (ℕ × Tile)) (a k b : ℕ) (z w : R)
    (hb : a + k = b) (h : run r ((l.drop a).take k) z = w) :
    run r (l.drop a) z = run r (l.drop b) w := by
  conv_lhs => rw [← List.take_append_drop k (l.drop a)]
  rw [run_append, h, drop_drop', hb]

/-! The selector fold, checked by `decide +kernel` in 20 chunks of 48 rows: one
closed evaluation of all 942 rows reached 4.5 GB and did not finish on this
machine. -/

private theorem chunk_0 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 0).take 48) 0 = 137161596300 := by
  decide +kernel

private theorem chunk_48 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 48).take 48) 137161596300 = 181983199297 := by
  decide +kernel

private theorem chunk_96 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 96).take 48) 181983199297 = 78937431050 := by
  decide +kernel

private theorem chunk_144 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 144).take 48) 78937431050 = 133473049447 := by
  decide +kernel

private theorem chunk_192 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 192).take 48) 133473049447 = 15434426232 := by
  decide +kernel

private theorem chunk_240 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 240).take 48) 15434426232 = 80324504366 := by
  decide +kernel

private theorem chunk_288 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 288).take 48) 80324504366 = 123058106017 := by
  decide +kernel

private theorem chunk_336 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 336).take 48) 123058106017 = 120554131608 := by
  decide +kernel

private theorem chunk_384 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 384).take 48) 120554131608 = 166302353883 := by
  decide +kernel

private theorem chunk_432 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 432).take 48) 166302353883 = 95306556775 := by
  decide +kernel

private theorem chunk_480 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 480).take 48) 95306556775 = 102948896927 := by
  decide +kernel

private theorem chunk_528 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 528).take 48) 102948896927 = 413040570 := by
  decide +kernel

private theorem chunk_576 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 576).take 48) 413040570 = 65428732392 := by
  decide +kernel

private theorem chunk_624 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 624).take 48) 65428732392 = 48474087515 := by
  decide +kernel

private theorem chunk_672 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 672).take 48) 48474087515 = 25207866178 := by
  decide +kernel

private theorem chunk_720 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 720).take 48) 25207866178 = 34833436159 := by
  decide +kernel

private theorem chunk_768 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 768).take 48) 34833436159 = 118517621387 := by
  decide +kernel

private theorem chunk_816 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 816).take 48) 118517621387 = 175645979093 := by
  decide +kernel

private theorem chunk_864 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 864).take 48) 175645979093 = 172445916123 := by
  decide +kernel

private theorem chunk_912 :
    run (135674952407 : ZMod 189746036981) ((orderedRows.drop 912).take 48) 172445916123 = 151792283673 := by
  decide +kernel

private theorem rows_common :
    evaluate (135674952407 : ZMod 189746036981) orderedRows = 151792283673 := by
  rw [evaluate_eq_run]
  change run _ (orderedRows.drop 0) 0 = _
  rw [run_chain _ orderedRows 0 48 48 _ _ rfl chunk_0,
    run_chain _ orderedRows 48 48 96 _ _ rfl chunk_48,
    run_chain _ orderedRows 96 48 144 _ _ rfl chunk_96,
    run_chain _ orderedRows 144 48 192 _ _ rfl chunk_144,
    run_chain _ orderedRows 192 48 240 _ _ rfl chunk_192,
    run_chain _ orderedRows 240 48 288 _ _ rfl chunk_240,
    run_chain _ orderedRows 288 48 336 _ _ rfl chunk_288,
    run_chain _ orderedRows 336 48 384 _ _ rfl chunk_336,
    run_chain _ orderedRows 384 48 432 _ _ rfl chunk_384,
    run_chain _ orderedRows 432 48 480 _ _ rfl chunk_432,
    run_chain _ orderedRows 480 48 528 _ _ rfl chunk_480,
    run_chain _ orderedRows 528 48 576 _ _ rfl chunk_528,
    run_chain _ orderedRows 576 48 624 _ _ rfl chunk_576,
    run_chain _ orderedRows 624 48 672 _ _ rfl chunk_624,
    run_chain _ orderedRows 672 48 720 _ _ rfl chunk_672,
    run_chain _ orderedRows 720 48 768 _ _ rfl chunk_720,
    run_chain _ orderedRows 768 48 816 _ _ rfl chunk_768,
    run_chain _ orderedRows 816 48 864 _ _ rfl chunk_816,
    run_chain _ orderedRows 864 48 912 _ _ rfl chunk_864,
    run_chain _ orderedRows 912 48 960 _ _ rfl chunk_912,
    (show orderedRows.drop 960 = [] from List.drop_eq_nil_of_le (by rw [ordered_count]; norm_num))]
  all_goals rfl


private theorem controls_common :
    controlReflection (135674952407 : ZMod 189746036981) = 29309889412 := by
  decide +kernel

private theorem radix_common : ((Bm2963Kernel.radix : ℕ) : ZMod 189746036981) = 135674952407 := by
  change ((2 : ℕ) ^ 47 : ZMod 189746036981) = 135674952407
  simp only [Nat.cast_ofNat]
  reduce_mod_char

/-- Powers as a linear accumulator (`pow_acc`), so that the kernel evaluates them by
repeated multiplication in `ZMod C0`. -/
def powAcc {R : Type*} [Monoid R] (r : R) : ℕ → R → R
  | 0, z => z
  | n + 1, z => powAcc r n (z * r)

theorem pow_acc {R : Type*} [Monoid R] (r : R) (n : ℕ) (z : R) : powAcc r n z = z * r ^ n := by
  induction n generalizing z with
  | zero => simp [powAcc]
  | succ n ih => rw [powAcc, ih, pow_succ', mul_assoc]

/-! The five radix powers, each by `decide +kernel` on `powAcc`. Normalizing the
whole kernel expression, powers included, by one `reduce_mod_char` (the
admissible942 route) took 31 minutes there; here only small residues remain
for it. -/

private theorem pow_18 : (135674952407 : ZMod 189746036981) ^ 18 = 140146040434 := by
  rw [← one_mul ((135674952407 : ZMod 189746036981) ^ 18), ← pow_acc]
  decide +kernel

private theorem pow_1005 : (135674952407 : ZMod 189746036981) ^ 1005 = 116138741133 := by
  rw [← one_mul ((135674952407 : ZMod 189746036981) ^ 1005), ← pow_acc]
  decide +kernel

private theorem pow_2972 : (135674952407 : ZMod 189746036981) ^ 2972 = 53218860586 := by
  rw [← one_mul ((135674952407 : ZMod 189746036981) ^ 2972), ← pow_acc]
  decide +kernel

private theorem pow_1015 : (135674952407 : ZMod 189746036981) ^ 1015 = 15943976764 := by
  rw [← one_mul ((135674952407 : ZMod 189746036981) ^ 1015), ← pow_acc]
  decide +kernel

private theorem pow_971 : (135674952407 : ZMod 189746036981) ^ 971 = 84022773715 := by
  rw [← one_mul ((135674952407 : ZMod 189746036981) ^ 971), ← pow_acc]
  decide +kernel

theorem K_cast_common : (Bm2963Kernel.K : ZMod 189746036981) = 25047958135 := by
  rw [Bm2963Kernel.K, rawWord_cast, radix_common, rows_common, controls_common, pow_18, pow_1005,
    pow_2972, pow_1015, pow_971]
  -- a closing `decide +kernel` here exhausted memory in the kernel check
  reduce_mod_char

attribute [local irreducible] Bm2963Kernel.K

theorem K_mod : Bm2963Kernel.K % 189746036981 = 25047958135 := by
  have h := congrArg ZMod.val K_cast_common
  have hr : (25047958135 : ZMod 189746036981).val = 25047958135 := by decide +kernel
  simpa only [ZMod.val_natCast, hr] using h

end Bm2963KernelResidue

#print axioms Bm2963KernelResidue.K_cast_common
#print axioms Bm2963KernelResidue.K_mod
