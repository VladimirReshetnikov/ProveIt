import DiophantineConsistency.Mixed121.Mixed121High
import DiophantineConsistency.Compact44.CompactHighOriginTransfer

/-! # The high-mask origin and block positivity, at 121x8801

The 121x8801 counterpart of Compact44's `CompactOriginBlockResidue`,
`CompactHighOriginResidue`, `CompactHighOriginMarked` and
`CompactWordBlockPositivity` (`CompactHighOriginTransfer` is generic and
reused).

* Block `0` of a marked word is `0 (mod 4)`. `4 ∣ K` and `4 ∣ 2^(121·42)`, and
  the marker's temporal predecessor is not the marker, so its cell has no
  selector-zero bit.
* `MF_native ≡ 4 (mod 8)` (recipe §3), so a block divisible by four that avoids
  `MF` also avoids `MF − 1`. That is the special origin field of the packing.
* Every block is positive: its temporal predecessor's cell has its own
  selector bit set. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
noncomputable section
namespace Mixed121Origin
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticPacking ArithmeticBinaryCarry
open CompactMarkedTransport CompactForwardCellInputs Mixed121Kernel Mixed121KernelSplit Mixed121Cell
  Mixed121Word Mixed121Block
attribute [local irreducible] paramKernel rho Mixed121Ports.lowNat Mixed121Ports.highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem four_dvd_exp {e : V} (he : 2 ≤ e) : (4 : V) ∣ Exp.exp e := by
  obtain ⟨d, rfl⟩ := exists_add_of_le he
  refine ⟨Exp.exp d, ?_⟩
  rw [add_comm, show d + 2 = d + 1 + 1 by ring, exp_succ, exp_succ]
  ring

theorem low_dvd_four (x : V) : (4:V) ∣ ((paramKernel rho : V)*x % Exp.exp 1064921) := by
  have hp : (4:V) ∣ (paramKernel rho : V)*x := dvd_mul_of_dvd_left kernel_model_dvd_four _
  have hmod := ArithmeticModularCancellation.mod_mod_of_dvd (by norm_num : (0:V)<4)
    (four_dvd_exp (by norm_num : (2:V) ≤ 1064921)) ((paramKernel rho : V)*x)
  apply mod_eq_zero_iff_dvd.mp
  rw [hmod, mod_eq_zero_iff_dvd.mpr hp]

theorem high_dvd_four (x : V) (hx : x < Exp.exp (121*3297+1 : V)) :
    (4:V) ∣ ((paramKernel rho : V)*x / Exp.exp 1064921) := by
  rw [high_product x hx]
  exact dvd_mul_of_dvd_left (four_dvd_exp (by norm_num : (2:V) ≤ 121*42)) _

/-- Block zero of a marked word, with normalized dummy cells, is `0 (mod 4)`. -/
theorem marked_origin_block_mod_four {row dummy : V → V} {N s : V}
    (hw : CompactWord row N s) (hs : 0<s) (hsN : s<N) :
    blk 1064921 (paramKernel rho : V) N s
      (fun j => normalizedCell (row j) (dummy j)) 0 % 4 = 0 := by
  let X : V → V := fun j => normalizedCell (row j) (dummy j)
  have hj : cyc N 0 1 < N := cyc_lt hw.pos 0 1
  have hd (j : V) : dummy j % 2 ≤ 1 := lt_two_iff_le_one.mp (mod_lt (dummy j) (by norm_num))
  have hsmall : X (cyc N 0 1) < Exp.exp (121*3297+1 : V) := by
    exact lt_of_lt_of_le (packedCell_lt_support (row (cyc N 0 1)) (dummy (cyc N 0 1)%2)
      (hw.tile_ne _ hj) (hd _)) (exp_monotone_le.mpr (le_add_of_nonneg_right (by norm_num)))
  have hne : row (cyc N 0 s) ≠ 0 := predecessor_ne_marker hw hs hsN
  have htemp : (4:V) ∣ X (cyc N 0 s) := by
    apply mod_eq_zero_iff_dvd.mp
    exact cell_mod_four _ _ hne (hd _)
  have hlo : (4:V) ∣ lo 1064921 (paramKernel rho : V) X 0 := low_dvd_four _
  have hhi : (4:V) ∣ hi 1064921 (paramKernel rho : V) X (cyc N 0 1) := high_dvd_four _ hsmall
  apply mod_eq_zero_iff_dvd.mpr
  change (4:V) ∣ lo 1064921 (paramKernel rho : V) X 0 +
    hi 1064921 (paramKernel rho : V) X (cyc N 0 1) + X (cyc N 0 s)
  exact dvd_add (dvd_add hlo hhi) htemp

theorem transfer_residue (x m : V) (hx : x % 4 = 0) (hm : m % 8 = 4)
    (h : NoCarry x m) : NoCarry x (m-1) := by
  have hxrep : 4*(x/4) = x := by simpa [hx] using div_add_mod x 4
  have hmrep : 8*(m/8)+4 = m := by simpa [hm] using div_add_mod m 8
  have hmminus : m-1 = 8*(m/8)+3 := by
    calc
      m-1 = (8*(m/8)+4)-1 := congrArg (fun z : V => z-1) hmrep.symm
      _ = 8*(m/8)+3 := by
        have h4 : (4:V) = 3+1 := by norm_num
        rw [h4, ← add_assoc, add_tsub_cancel_right]
  have hbase : NoCarry (4*(x/4)) (8*(m/8)+4) := by simpa only [hxrep, hmrep] using h
  have hc := CompactHighOriginTransfer.transfer_parts (x/4) (m/8) hbase
  simpa only [hxrep, ← hmminus] using hc

theorem symbolic_high_origin (x : V) (hx : x % 4 = 0)
    (h : NoCarry x ((Mixed121Ports.highNat : ℕ) : V)) :
    NoCarry x (((Mixed121Ports.highNat : ℕ) : V)-1) :=
  transfer_residue x _ hx Mixed121Masks.model_high_mod_eight h

/-- A uniform high-mask no-carry gives the origin and non-origin high fields. -/
theorem normalized_high_fields {row dummy : V → V} {N s : V}
    (hw : CompactWord row N s) (hs : 0<s) (hsN : s<N)
    (hall : ∀ j<N, NoCarry
      (blk 1064921 (paramKernel rho : V) N s (fun k => normalizedCell (row k) (dummy k)) j)
      ((Mixed121Ports.highNat : ℕ) : V)) :
    NoCarry (blk 1064921 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (dummy k)) 0) (((Mixed121Ports.highNat : ℕ) : V)-1) ∧
    ∀ j<N, 0<j → NoCarry (blk 1064921 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (dummy k)) j) ((Mixed121Ports.highNat : ℕ) : V) := by
  constructor
  · exact symbolic_high_origin _ (marked_origin_block_mod_four hw hs hsN) (hall 0 hw.pos)
  · intro j hj _; exact hall j hj

theorem pulsed_high_fields {row δ : V → V} {N s : V}
    (hw : CompactWord row N s) (hs : 0<s) (hsN : s<N) (hbool : ∀ j, δ j ≤ 1)
    (hall : ∀ j<N, NoCarry (blk 1064921 (paramKernel rho : V) N s (pulsedCell row δ) j)
      ((Mixed121Ports.highNat : ℕ) : V)) :
    NoCarry (blk 1064921 (paramKernel rho : V) N s (pulsedCell row δ) 0)
      (((Mixed121Ports.highNat : ℕ) : V)-1) ∧
    ∀ j<N, 0<j → NoCarry (blk 1064921 (paramKernel rho : V) N s (pulsedCell row δ) j)
      ((Mixed121Ports.highNat : ℕ) : V) := by
  have he : (fun j => normalizedCell (row j) (δ j)) = pulsedCell row δ := by
    funext j
    change normalizedCell (row j) (δ j) = packedCell (row j) 0 + Exp.exp (121*1063)*δ j
    rw [normalized_eq_pulse, mod_eq_self_of_lt (lt_two_iff_le_one.mpr (hbool j))]
  have hn : ∀ j<N, NoCarry (blk 1064921 (paramKernel rho : V) N s
      (fun k => normalizedCell (row k) (δ k)) j) ((Mixed121Ports.highNat : ℕ) : V) := by
    rw [he]; exact hall
  have h := normalized_high_fields hw hs hsN hn
  rwa [he] at h

/-- A valid row sets its own selector digit to one. -/
theorem packedCell_pos (a d : V) (ha : a < 943) (hd : d ≤ 1) :
    0 < packedCell a d := by
  obtain ⟨n, rfl⟩ := eq_nat_of_lt_nat (n := 943) ha
  have hn : n < 943 := by exact_mod_cast ha
  have h := packedCell_selector (n : V) d hd ⟨n, hn⟩
  have hs : dig 121 (packedCell (n : V) d) (n : V) = 1 := by
    simpa [selector] using h
  by_contra hzero
  have he : packedCell (n : V) d = 0 :=
    le_antisymm (not_lt.mp hzero) (Arithmetic.zero_le _)
  rw [he] at hs
  simp [dig] at hs

/-- Both base and pulsed words have positive blocks everywhere. -/
theorem block_pos {row δ : V → V} {d K N s : V}
    (hw : CompactWord row N s) (j : V) :
    0 < blk d K N s (baseCell row) j ∧
    0 < blk d K N s (pulsedCell row δ) j := by
  have hk : cyc N j s < N := cyc_lt hw.pos j s
  have hp : 0 < baseCell row (cyc N j s) :=
    packedCell_pos (row _) 0 (hw.tile_lt _ hk) (by simp)
  have hq : 0 < pulsedCell row δ (cyc N j s) :=
    lt_of_lt_of_le hp (le_add_of_nonneg_right (Arithmetic.zero_le _))
  constructor <;> unfold blk
  · exact lt_of_lt_of_le hp (le_add_of_nonneg_left (Arithmetic.zero_le _))
  · exact lt_of_lt_of_le hq (le_add_of_nonneg_left (Arithmetic.zero_le _))

#print axioms Mixed121Origin.marked_origin_block_mod_four
#print axioms Mixed121Origin.symbolic_high_origin
#print axioms Mixed121Origin.pulsed_high_fields
#print axioms Mixed121Origin.block_pos
end Mixed121Origin
