import DiophantineConsistency.ArithmeticPackingBlocks

/-! **K3 — the packing scalars** (construction spec §5 Stage P, with
simplification S2: zero carries into and out of every cell), in every model
of IΣ1.

Data: the block width `d` (`= 94517`, `B = 2^d = ρ^2011`), the kernel `K`
(`K·X j < B²`; `K` itself reaches `ρ^2020`),
the low and high mask blocks `MC`, `HP`, the cell count `N` and stride `s`
(internal, possibly nonstandard), and a Σ1-definable cell word
`X : V → V` (`X j = Cell(x_j)` in the spec). The transport blocks are
`lo j = K·X j mod B`, `hi j = ⌊K·X j / B⌋` and the normalized block
`blk j = lo j + hi (j-1 mod N) + X (j-s mod N)` (spec P2: `D_j = Raw_j`).

`PackingInput` lists the per-cell (finite, standard) facts that the Local
Normalization Lemma supplies at every cell `j < N`: the block bound
`X j + blk j < B`, the origin `X 0 ≥ 1`, positivity `blk 0 > 0`, and the four
blockwise mask disjointness facts. From these alone, the global scalars
* `C = Σ_{j<N} B^j X j`, `F = Σ_{j<N} B^j blk j`, `J = rep d N`,
  `q = 2^{dN}`, `α = q - C - F`,
satisfy (`packing_*`):
* `(B-1)·J + 1 = q`;
* `0 < C`, `0 < F`, `0 < α`, `C + F + α = q`;
* **transport**: for every multiplier `W ≡ B^s (mod q-1)`, with
  `z = ⌊(K+W)·C/(q-1)⌋ + 1`: `(K+W)·C + (q-F) = z·(q-1) + 1`;
* **masks**: `NoCarry (C-1) (MC·J+1)` and `NoCarry F (HP·J-1)`.

**Interface for K4–K7.** K4 (rank forcing) consumes `C + F + α = q`, the two
`NoCarry` mask facts and `(B-1)J+1 = q`; K5 (controller) needs `W` free in the
transport law (it uses `W = 2^{R-u} = B^t` with `t ≡ s (mod N)`); K7 reads
`J, F, α, z, C` as coordinates. No unique-Start fact is produced or needed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticPacking
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticRepunit
  ArithmeticPackingBlocks

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-! ## Transport blocks -/

/-- Low half of the cell product `K·X j` at degree `B`. -/
def lo (d K : V) (X : V → V) (j : V) : V := K * X j % Exp.exp d
/-- High half of the cell product `K·X j` at degree `B`. -/
def hi (d K : V) (X : V → V) (j : V) : V := K * X j / Exp.exp d
/-- The normalized transport block `Lo(x_j) + Hi(x_{j-1}) + Cell(x_{j-s})`. -/
def blk (d K N s : V) (X : V → V) (j : V) : V :=
  lo d K X j + hi d K X (cyc N j 1) + X (cyc N j s)

section defs
variable (d K N s : V) (X : V → V) [𝚺₁-Function₁ X]
instance lo_definable : 𝚺₁-Function₁ (lo d K X) := by unfold lo; definability
instance hi_definable : 𝚺₁-Function₁ (hi d K X) := by unfold hi; definability
instance blk_definable : 𝚺₁-Function₁ (blk d K N s X) := by unfold blk; definability
end defs

/-- The per-cell facts supplied by the Local Normalization Lemma. -/
structure PackingInput (d K MC HP N s : V) (X : V → V) : Prop where
  N_gt : 1 < N
  s_lt : s < N
  hi_lt : ∀ j < N, K * X j < Exp.exp d * Exp.exp d
  MC_lt : MC + 1 < Exp.exp d
  HP_pos : 1 ≤ HP
  HP_lt : HP < Exp.exp d
  cell_sum : ∀ j < N, X j + blk d K N s X j < Exp.exp d
  origin : 1 ≤ X 0
  blk_pos : 0 < blk d K N s X 0
  low_origin : NoCarry (X 0 - 1) (MC + 1)
  low : ∀ j < N, 0 < j → NoCarry (X j) MC
  high_origin : NoCarry (blk d K N s X 0) (HP - 1)
  high : ∀ j < N, 0 < j → NoCarry (blk d K N s X j) HP

/-! ## The scalars -/

/-- The source word `C = Σ B^j Cell(x_j)`. -/
def Cw (d N : V) (X : V → V) : V := bsum d X N
/-- The normalized transport word `F = Σ B^j D_j`. -/
def Fw (d K N s : V) (X : V → V) : V := bsum d (blk d K N s X) N
/-- `α = q - C - F`. -/
def alpha (d K N s : V) (X : V → V) : V := Exp.exp (d * N) - Cw d N X - Fw d K N s X
/-- The transport quotient for multiplier `W`. -/
def zq (d K N W : V) (X : V → V) : V := (K + W) * Cw d N X / (Exp.exp (d * N) - 1) + 1

/-- `rot X e + (B^n − 1)·(X / B^(n−e)) = B^e·X`. -/
theorem rot_identity (w n X e : V) (he : e ≤ n) :
    rot w n X e + (Exp.exp (w * n) - 1) * (X / Exp.exp (w * (n - e))) =
      Exp.exp (w * e) * X := by
  unfold rot
  have hX := div_add_mod X (Exp.exp (w * (n - e)))
  have hn : Exp.exp (w * n) = Exp.exp (w * (n - e)) * Exp.exp (w * e) := by
    rw [← exp_mul_add, tsub_add_cancel_of_le he]
  have h1 : Exp.exp (w * n) - 1 + 1 = Exp.exp (w * n) := tsub_add_cancel_of_le (one_le_exp _)
  calc
    _ = X % Exp.exp (w * (n - e)) * Exp.exp (w * e) +
        (Exp.exp (w * n) - 1 + 1) * (X / Exp.exp (w * (n - e))) := by ring
    _ = Exp.exp (w * e) * (Exp.exp (w * (n - e)) * (X / Exp.exp (w * (n - e))) +
        X % Exp.exp (w * (n - e))) := by rw [h1, hn]; ring
    _ = _ := by rw [hX]

private theorem bsum_pos_of_origin {w n : V} {f : V → V} [𝚺₁-Function₁ f]
    (hf : ∀ j < n, f j < Exp.exp w) (hn : 0 < n) (hf0 : 0 < f 0) :
    0 < bsum w f n := by
  have hd := dig_bsum hf hn
  rw [dig_zero_index] at hd
  exact lt_of_lt_of_le (by rwa [hd]) (mod_le _ _)

section main
variable {d K MC HP N s : V} {X : V → V} [𝚺₁-Function₁ X]
  (h : PackingInput d K MC HP N s X)
include h

theorem X_lt : ∀ j < N, X j < Exp.exp d := fun j hj =>
  lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le _)) (h.cell_sum j hj)

theorem blk_lt : ∀ j < N, blk d K N s X j < Exp.exp d := fun j hj =>
  lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le _)) (h.cell_sum j hj)

theorem N_pos : 0 < N := lt_trans (by norm_num) h.N_gt

theorem two_le_B : 2 ≤ Exp.exp d := by
  have h1 : (1 : V) < Exp.exp d :=
    lt_of_le_of_lt (le_add_of_nonneg_left (Arithmetic.zero_le MC)) h.MC_lt
  simpa [one_add_one_eq_two] using lt_iff_succ_le.mp h1

theorem B_le_q : Exp.exp d ≤ Exp.exp (d * N) :=
  exp_monotone_le.mpr (le_mul_of_one_le_right (Arithmetic.zero_le d)
    (pos_iff_one_le.mp (N_pos h)))

theorem q_pos' : 0 < Exp.exp (d * N) - 1 :=
  tsub_pos_of_lt (lt_of_lt_of_le (by norm_num) (le_trans (two_le_B h) (B_le_q h)))

/-- `C + F = Σ B^j (X j + blk j) < q`. -/
theorem C_add_F_lt : Cw d N X + Fw d K N s X < Exp.exp (d * N) := by
  haveI : 𝚺₁-Function₁ (fun j => X j + blk d K N s X j) := by definability
  rw [Cw, Fw, ← bsum_add (h := fun j => X j + blk d K N s X j) h.cell_sum (fun _ _ => rfl)]
  exact bsum_lt h.cell_sum

theorem C_pos : 0 < Cw d N X :=
  bsum_pos_of_origin (X_lt h) (N_pos h) (lt_of_lt_of_le (by norm_num) h.origin)

theorem F_pos : 0 < Fw d K N s X :=
  bsum_pos_of_origin (blk_lt h) (N_pos h) h.blk_pos

/-- **Sizes.** `0 < α` and `C + F + α = q`. -/
theorem packing_alpha : 0 < alpha d K N s X ∧
    Cw d N X + Fw d K N s X + alpha d K N s X = Exp.exp (d * N) := by
  have hlt := C_add_F_lt h
  refine ⟨?_, ?_⟩
  · rw [alpha, tsub_tsub]; exact tsub_pos_of_lt hlt
  · rw [alpha, tsub_tsub, add_tsub_cancel_of_le hlt.le]

theorem F_lt_M : Fw d K N s X < Exp.exp (d * N) - 1 := by
  have hlt := C_add_F_lt h
  have hC := C_pos h
  apply lt_tsub_of_add_lt_left
  exact lt_of_le_of_lt (add_le_add (pos_iff_one_le.mp hC) le_rfl) hlt

theorem transport_formula :
    Fw d K N s X + (Exp.exp (d * N) - 1) *
        (bsum d (hi d K X) N / Exp.exp (d * (N - 1)) + Cw d N X / Exp.exp (d * (N - s))) =
      (K + Exp.exp (d * s)) * Cw d N X := by
  have hX := X_lt h
  have hB := blk_lt h
  have hlo : ∀ j < N, lo d K X j < Exp.exp d := fun j _ => mod_lt _ (exp_pos d)
  have hhi : ∀ j < N, hi d K X j < Exp.exp d := fun j hj =>
    div_lt_of_lt_mul (h.hi_lt j hj)
  have hsplit : ∀ j < N, K * X j = lo d K X j + Exp.exp d * hi d K X j := fun j _ => by
    rw [lo, hi, add_comm]; exact (div_add_mod _ _).symm
  have e1 := bsum_mul_split (w := d) (f := X) K (lo := lo d K X) (hi := hi d K X) hX hlo hhi hsplit
  haveI : 𝚺₁-Function₁ (fun j => hi d K X (cyc N j 1)) := by definability
  haveI : 𝚺₁-Function₁ (fun j => X (cyc N j s)) := by definability
  haveI : 𝚺₁-Function₁ (fun j => lo d K X j + hi d K X (cyc N j 1)) := by definability
  have hF1 : Fw d K N s X = bsum d (fun j => lo d K X j + hi d K X (cyc N j 1)) N +
      bsum d (fun j => X (cyc N j s)) N :=
    bsum_add (fun j hj => hB j hj) (fun _ _ => rfl)
  have hF2 : bsum d (fun j => lo d K X j + hi d K X (cyc N j 1)) N =
      bsum d (lo d K X) N + bsum d (fun j => hi d K X (cyc N j 1)) N :=
    bsum_add (fun j hj => lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le _)) (hB j hj))
      (fun _ _ => rfl)
  have hc1 := bsum_cyc (w := d) (f := hi d K X) (e := 1) h.N_gt hhi
  have hcs := bsum_cyc (w := d) (f := X) (e := s) h.s_lt hX
  have r1 := rot_identity d N (bsum d (hi d K X) N) 1 h.N_gt.le
  have rs := rot_identity d N (bsum d X N) s h.s_lt.le
  rw [mul_one] at r1
  rw [hF1, hF2, hc1, hcs, Cw]
  calc bsum d (lo d K X) N + rot d N (bsum d (hi d K X) N) 1 + rot d N (bsum d X N) s +
        (Exp.exp (d * N) - 1) * (bsum d (hi d K X) N / Exp.exp (d * (N - 1)) +
          bsum d X N / Exp.exp (d * (N - s)))
      = bsum d (lo d K X) N + (rot d N (bsum d (hi d K X) N) 1 +
          (Exp.exp (d * N) - 1) * (bsum d (hi d K X) N / Exp.exp (d * (N - 1)))) +
        (rot d N (bsum d X N) s + (Exp.exp (d * N) - 1) * (bsum d X N / Exp.exp (d * (N - s)))) := by
        ring
    _ = bsum d (lo d K X) N + Exp.exp d * bsum d (hi d K X) N +
        Exp.exp (d * s) * bsum d X N := by rw [r1, rs]
    _ = _ := by rw [← e1]; ring


/-- The transport residue: `(K + B^s)·C ≡ F (mod q-1)`. -/
theorem transport_residue :
    ((K + Exp.exp (d * s)) * Cw d N X) % (Exp.exp (d * N) - 1) = Fw d K N s X := by
  have hM := q_pos' h
  have hm := congrArg (fun z : V => z % (Exp.exp (d * N) - 1)) (transport_formula h)
  rw [mod_add hM, mod_mul hM, mod_self, zero_mul, zero_mod, add_zero,
    mod_eq_self_of_lt (F_lt_M h)] at hm
  simpa only [mod_eq_self_of_lt (F_lt_M h)] using hm.symm

/-- **Transport.** For every multiplier `W ≡ B^s (mod q-1)`,
`(K+W)·C + (q-F) = z·(q-1) + 1` with `z = ⌊(K+W)C/(q-1)⌋ + 1`. -/
theorem packing_transport (W : V)
    (hW : W % (Exp.exp (d * N) - 1) = Exp.exp (d * s) % (Exp.exp (d * N) - 1)) :
    (K + W) * Cw d N X + (Exp.exp (d * N) - Fw d K N s X) =
      zq d K N W X * (Exp.exp (d * N) - 1) + 1 := by
  have hM := q_pos' h
  set M := Exp.exp (d * N) - 1 with hMdef
  have hres : ((K + W) * Cw d N X) % M = Fw d K N s X := by
    have hmul : (W * Cw d N X) % M = (Exp.exp (d * s) * Cw d N X) % M := by
      rw [mod_mul hM, hW, ← mod_mul hM]
    rw [← transport_residue h, add_mul, add_mul, mod_add hM, hmul, ← mod_add hM]
  have hq : Exp.exp (d * N) = M + 1 := (tsub_add_cancel_of_le (one_le_exp _)).symm
  have hdiv := div_add_mod ((K + W) * Cw d N X) M
  rw [hres] at hdiv
  have hFq : Fw d K N s X ≤ Exp.exp (d * N) :=
    le_trans (F_lt_M h).le tsub_le_self
  rw [zq, ← hMdef]
  calc (K + W) * Cw d N X + (Exp.exp (d * N) - Fw d K N s X)
      = (M * ((K + W) * Cw d N X / M) + Fw d K N s X) + (Exp.exp (d * N) - Fw d K N s X) := by
        rw [hdiv]
    _ = M * ((K + W) * Cw d N X / M) + Exp.exp (d * N) := by
        rw [add_assoc, add_tsub_cancel_of_le hFq]
    _ = ((K + W) * Cw d N X / M + 1) * M + 1 := by rw [hq]; ring

/-- **Low mask.** `(C-1) AND (MC·J+1) = 0`. -/
theorem packing_low_mask : NoCarry (Cw d N X - 1) (MC * rep d N + 1) := by
  have hN := N_pos h
  have hX := X_lt h
  haveI : 𝚺₁-Function₁ (fun j => X j - 1 * (1 - j)) := by definability
  haveI : 𝚺₁-Function₁ (fun j : V => MC + 1 * (1 - j)) := by definability
  haveI : 𝚺₁-Function₁ (fun _ : V => MC) := by definability
  have hMC : MC < Exp.exp d := lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le 1)) h.MC_lt
  have e1 : Cw d N X - 1 = bsum d (fun j => X j - 1 * (1 - j)) N :=
    (bsum_sub_origin hN hX h.origin).symm
  have e2 : MC * rep d N + 1 = bsum d (fun j : V => MC + 1 * (1 - j)) N := by
    rw [bsum_add_origin (f := fun _ : V => MC) hN (fun _ _ => hMC) h.MC_lt, bsum_const_rep hMC]
  rw [e1, e2]
  apply bsum_noCarry
  · exact fun j hj => lt_of_le_of_lt tsub_le_self (hX j hj)
  · intro j _
    rcases zero_or_succ j with rfl | ⟨i, rfl⟩
    · simpa using h.MC_lt
    · simpa [one_sub_succ] using hMC
  · intro j hj
    rcases zero_or_succ j with rfl | ⟨i, rfl⟩
    · simpa using h.low_origin
    · simpa [one_sub_succ] using h.low (i + 1) hj (by simp)

/-- **High mask.** `F AND (HP·J-1) = 0`. -/
theorem packing_high_mask : NoCarry (Fw d K N s X) (HP * rep d N - 1) := by
  have hN := N_pos h
  have hB := blk_lt h
  haveI : 𝚺₁-Function₁ (fun j : V => HP - 1 * (1 - j)) := by definability
  haveI : 𝚺₁-Function₁ (fun _ : V => HP) := by definability
  have e2 : HP * rep d N - 1 = bsum d (fun j : V => HP - 1 * (1 - j)) N := by
    rw [bsum_sub_origin (f := fun _ : V => HP) hN (fun _ _ => h.HP_lt) h.HP_pos,
      bsum_const_rep h.HP_lt]
  rw [e2, Fw]
  apply bsum_noCarry hB
  · exact fun j _ => lt_of_le_of_lt tsub_le_self h.HP_lt
  · intro j hj
    rcases zero_or_succ j with rfl | ⟨i, rfl⟩
    · simpa using h.high_origin
    · simpa [one_sub_succ] using h.high (i + 1) hj (by simp)

/-- **The repunit.** `(B-1)·J + 1 = q`. -/
theorem packing_repunit : (Exp.exp d - 1) * rep d N + 1 = Exp.exp (d * N) :=
  repunit_identity d N

end main

end DiophantineConsistency.ArithmeticPacking
