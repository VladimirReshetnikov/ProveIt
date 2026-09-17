/-
# The nonrecursive block expansion and the word coefficients (Theorem 2.2)

Theorem 2.2 of the accompanying article (`docs/combined`) gives the finite,
nonrecursive formula for the homogeneous components of the BCH series,
equation (2.homblocks):

`Zₙ = ∑_{k=1}^{n} (-1)^{k-1}/k ∑_{(rᵢ,sᵢ) : rᵢ+sᵢ > 0, ∑ᵢ (rᵢ+sᵢ) = n}
        X^{r₁} Y^{s₁} ⋯ X^{r_k} Y^{s_k} / ∏ᵢ rᵢ! sᵢ!`,

and, reading off coefficients in the free algebra, the formula (2.wordcut)
for the coefficient `c(w)` of a word `w`: the sum over all cuts of `w` into
`k` blocks of the form `X^r Y^s` of `(-1)^{k-1}/k ∏ 1/(rᵢ! sᵢ!)`.

* `blockTuples k n` is the finite set of `k`-tuples of pairs `(rᵢ, sᵢ)` with
  `rᵢ + sᵢ > 0` and `∑ᵢ (rᵢ + sᵢ) = n` (`mem_blockTuples`);
* `blockWord X Y rs = X^{r₁} Y^{s₁} ⋯ X^{r_k} Y^{s_k}`, `blockWeight rs = ∏ᵢ (rᵢ! sᵢ!)⁻¹`;
* `powBlock_eq_sum_blockTuples`: `(Uᵏ)ₙ = ∑_{rs ∈ blockTuples k n} blockWeight rs • blockWord X Y rs`;
* `bchHom_eq_sum_blockTuples`: equation (2.homblocks), in any algebra;
* `coeff_bchHom`: equation (2.wordcut) in the free algebra: the coefficient of
  `w` in `Zₙ(X, Y)` is `∑_k (-1)^{k-1}/k ∑_{rs ∈ blockTuples k n, word(rs) = w} blockWeight rs`.
-/
import BCH.Formal.Free

open Finset

namespace BCH

section Blocks

variable (𝕂 : Type*) [RCLike 𝕂]

/-- The `k`-tuples of blocks `(rᵢ, sᵢ)`, each of positive degree `rᵢ + sᵢ`, of total degree
`n`, defined by recursion on `k`. -/
def blockTuples : (k : ℕ) → ℕ → Finset (Fin k → ℕ × ℕ)
  | 0, n => if n = 0 then {![]} else ∅
  | k + 1, n => (antidiagonal n).biUnion fun p =>
      if p.1 = 0 then ∅ else
        (antidiagonal p.1).biUnion fun rs₀ => (blockTuples k p.2).image (Fin.cons rs₀)

/-- Membership in `blockTuples`: all blocks have positive degree and the degrees add up
to `n`. -/
theorem mem_blockTuples : ∀ {k n : ℕ} {rs : Fin k → ℕ × ℕ},
    rs ∈ blockTuples k n ↔ (∀ i, 0 < (rs i).1 + (rs i).2) ∧ ∑ i, ((rs i).1 + (rs i).2) = n
  | 0, n, rs => by
    simp only [blockTuples]
    split_ifs with h
    · subst h
      exact ⟨fun _ => ⟨fun i => i.elim0, by simp⟩,
        fun _ => Finset.mem_singleton.mpr (Subsingleton.elim _ _)⟩
    · simp only [Finset.notMem_empty, false_iff, not_and]
      intro _ hsum
      exact h (by simpa using hsum.symm)
  | k + 1, n, rs => by
    simp only [blockTuples, Finset.mem_biUnion, mem_antidiagonal, Prod.exists]
    constructor
    · rintro ⟨a, b, hab, hmem⟩
      split_ifs at hmem with ha
      · exact absurd hmem (Finset.notMem_empty _)
      rw [Finset.mem_biUnion] at hmem
      obtain ⟨rs₀, hrs₀, hmem⟩ := hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨rs', hrs', rfl⟩ := hmem
      rw [mem_antidiagonal] at hrs₀
      obtain ⟨hpos, hsum⟩ := mem_blockTuples.mp hrs'
      refine ⟨fun i => ?_, ?_⟩
      · refine Fin.cases ?_ (fun j => ?_) i
        · rw [Fin.cons_zero]; omega
        · rw [Fin.cons_succ]; exact hpos j
      · rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        omega
    · rintro ⟨hpos, hsum⟩
      have h0 := hpos 0
      rw [Fin.sum_univ_succ] at hsum
      refine ⟨(rs 0).1 + (rs 0).2, n - ((rs 0).1 + (rs 0).2), by omega, ?_⟩
      rw [if_neg (by omega), Finset.mem_biUnion]
      refine ⟨rs 0, mem_antidiagonal.mpr rfl, ?_⟩
      rw [Finset.mem_image]
      refine ⟨Fin.tail rs, ?_, Fin.cons_self_tail rs⟩
      rw [mem_blockTuples]
      exact ⟨fun j => hpos j.succ, by simp only [Fin.tail]; omega⟩

/-- Summation over `blockTuples (k + 1) n`, unfolded along the first block. -/
theorem sum_blockTuples_succ {M : Type*} [AddCommMonoid M] (k n : ℕ)
    (F : (Fin (k + 1) → ℕ × ℕ) → M) :
    ∑ rs ∈ blockTuples (k + 1) n, F rs =
      ∑ p ∈ antidiagonal n, if p.1 = 0 then 0 else
        ∑ rs₀ ∈ antidiagonal p.1, ∑ rs ∈ blockTuples k p.2, F (Fin.cons rs₀ rs) := by
  rw [blockTuples, Finset.sum_biUnion]
  · refine sum_congr rfl fun p _ => ?_
    split_ifs with h0
    · simp
    · rw [Finset.sum_biUnion]
      · refine sum_congr rfl fun rs₀ _ => ?_
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact (Fin.cons_inj.mp hxy).2
      · intro a _ b _ hab
        rw [Function.onFun, Finset.disjoint_left]
        intro rs hra hrb
        rw [Finset.mem_image] at hra hrb
        obtain ⟨x, _, rfl⟩ := hra
        obtain ⟨y, _, hy⟩ := hrb
        have h0' := congrFun hy 0
        rw [Fin.cons_zero, Fin.cons_zero] at h0'
        exact hab h0'.symm
  · intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_left]
    intro rs hrp hrq
    rw [Finset.mem_coe, mem_antidiagonal] at hp hq
    split_ifs at hrp hrq with hp0 hq0
    · exact absurd hrp (Finset.notMem_empty _)
    · exact absurd hrp (Finset.notMem_empty _)
    · exact absurd hrq (Finset.notMem_empty _)
    rw [Finset.mem_biUnion] at hrp hrq
    obtain ⟨a, ha, hra⟩ := hrp
    obtain ⟨b, hb, hrb⟩ := hrq
    rw [Finset.mem_image] at hra hrb
    obtain ⟨x, _, rfl⟩ := hra
    obtain ⟨y, _, hy⟩ := hrb
    have h0' := congrFun hy 0
    rw [Fin.cons_zero, Fin.cons_zero] at h0'
    subst h0'
    rw [mem_antidiagonal] at ha hb
    apply hpq
    ext <;> omega

/-- The word `X^{r₁} Y^{s₁} ⋯ X^{r_k} Y^{s_k}` of a tuple of blocks, in any monoid. -/
def blockWord {M : Type*} [Monoid M] (X Y : M) {k : ℕ} (rs : Fin k → ℕ × ℕ) : M :=
  (List.ofFn fun i => X ^ (rs i).1 * Y ^ (rs i).2).prod

/-- The weight `∏ᵢ (rᵢ! sᵢ!)⁻¹` of a tuple of blocks. -/
noncomputable def blockWeight {k : ℕ} (rs : Fin k → ℕ × ℕ) : 𝕂 :=
  ∏ i, ((Nat.factorial (rs i).1 * Nat.factorial (rs i).2 : ℕ) : 𝕂)⁻¹

variable {𝕂}

lemma blockWord_zero {M : Type*} [Monoid M] (X Y : M) (rs : Fin 0 → ℕ × ℕ) :
    blockWord X Y rs = 1 := by
  simp [blockWord]

lemma blockWord_cons {M : Type*} [Monoid M] (X Y : M) {k : ℕ} (rs₀ : ℕ × ℕ)
    (rs : Fin k → ℕ × ℕ) :
    blockWord X Y (Fin.cons rs₀ rs) = X ^ rs₀.1 * Y ^ rs₀.2 * blockWord X Y rs := by
  simp [blockWord, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ]

lemma map_blockWord {M N : Type*} [Monoid M] [Monoid N] (f : M →* N) (X Y : M) {k : ℕ}
    (rs : Fin k → ℕ × ℕ) : f (blockWord X Y rs) = blockWord (f X) (f Y) rs := by
  simp [blockWord, map_list_prod, List.map_ofFn, Function.comp_def, map_mul, map_pow]

lemma blockWeight_zero (rs : Fin 0 → ℕ × ℕ) : blockWeight 𝕂 rs = 1 := by
  simp [blockWeight]

lemma blockWeight_cons {k : ℕ} (rs₀ : ℕ × ℕ) (rs : Fin k → ℕ × ℕ) :
    blockWeight 𝕂 (Fin.cons rs₀ rs) =
      ((Nat.factorial rs₀.1 * Nat.factorial rs₀.2 : ℕ) : 𝕂)⁻¹ * blockWeight 𝕂 rs := by
  simp [blockWeight, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

variable {𝔸 : Type*} [Ring 𝔸] [Algebra 𝕂 𝔸]

/-- The degree-`n` part of `Uᵏ` as a sum over `k`-tuples of blocks. -/
theorem powBlock_eq_sum_blockTuples (X Y : 𝔸) :
    ∀ k n : ℕ, powBlock 𝕂 X Y k n = ∑ rs ∈ blockTuples k n, blockWeight 𝕂 rs • blockWord X Y rs
  | 0, n => by
    rw [powBlock_zero]
    simp only [blockTuples]
    split_ifs <;> simp [blockWord_zero, blockWeight_zero]
  | k + 1, n => by
    rw [powBlock_succ, sum_blockTuples_succ]
    refine sum_congr rfl fun p _ => ?_
    split_ifs with h0
    · simp [uBlock, h0]
    · rw [uBlock, if_neg h0, expBlock, powBlock_eq_sum_blockTuples X Y k, Finset.sum_mul]
      refine sum_congr rfl fun rs₀ _ => ?_
      rw [Finset.mul_sum]
      refine sum_congr rfl fun rs _ => ?_
      rw [blockWord_cons, blockWeight_cons, smul_mul_smul_comm]

/-- **Theorem 2.2, equation (2.homblocks)**: the nonrecursive block expansion of `Zₙ(X, Y)`,
`Zₙ = ∑_{k=1}^{n} (-1)^{k-1}/k ∑_{rs ∈ blockTuples k n} X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k} / ∏ rᵢ!sᵢ!`. -/
theorem bchHom_eq_sum_blockTuples (X Y : 𝔸) (n : ℕ) :
    bchHom 𝕂 X Y n = ∑ k ∈ range n, ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹) •
      ∑ rs ∈ blockTuples (k + 1) n, blockWeight 𝕂 rs • blockWord X Y rs := by
  simp only [bchHom, powBlock_eq_sum_blockTuples]

end Blocks

section Coefficients

variable {𝕂 : Type*} [RCLike 𝕂]

instance : DecidableEq (FreeMonoid (Fin 2)) := fun a b =>
  decidable_of_iff (FreeMonoid.toList a = FreeMonoid.toList b)
    FreeMonoid.toList.injective.eq_iff

/-- The word of a tuple of blocks in the free monoid on the two letters. -/
abbrev blockMonoid {k : ℕ} (rs : Fin k → ℕ × ℕ) : FreeMonoid (Fin 2) :=
  blockWord (FreeMonoid.of 0) (FreeMonoid.of 1) rs

lemma blockWord_gen {k : ℕ} (rs : Fin k → ℕ × ℕ) :
    blockWord (genX 𝕂) (genY 𝕂) rs = MonoidAlgebra.single (blockMonoid rs) 1 := by
  have h := map_blockWord (MonoidAlgebra.of 𝕂 (FreeMonoid (Fin 2))) (FreeMonoid.of 0)
    (FreeMonoid.of 1) rs
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.of_apply, MonoidAlgebra.of_apply] at h
  exact h.symm

/-- The coefficient of a word in a single block word. -/
lemma coeff_blockWord_gen {k : ℕ} (rs : Fin k → ℕ × ℕ) (w : FreeMonoid (Fin 2)) :
    (blockWord (genX 𝕂) (genY 𝕂) rs).coeff w = if blockMonoid rs = w then 1 else 0 := by
  rw [blockWord_gen, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The word coefficient `c(w)` of the BCH series: the coefficient of `w` in `Z_{|w|}(X, Y)`. -/
noncomputable def wordCoeff (𝕂 : Type*) [RCLike 𝕂] (w : FreeMonoid (Fin 2)) : 𝕂 :=
  (bchHom 𝕂 (genX 𝕂) (genY 𝕂) (FreeMonoid.length w)).coeff w

/-- **Theorem 2.2, equation (2.wordcut)**: the coefficient of a word `w` in `Zₙ(X, Y)` is
`∑_{k=1}^{n} (-1)^{k-1}/k ∑ ∏ᵢ (rᵢ! sᵢ!)⁻¹`, the inner sum over the cuts of `w` into `k`
blocks `X^{r₁}Y^{s₁} ⋯ X^{r_k}Y^{s_k} = w` of positive degrees. -/
theorem coeff_bchHom (n : ℕ) (w : FreeMonoid (Fin 2)) :
    (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n).coeff w =
      ∑ k ∈ range n, ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹) *
        ∑ rs ∈ (blockTuples (k + 1) n).filter (fun rs => blockMonoid rs = w), blockWeight 𝕂 rs := by
  classical
  rw [bchHom_eq_sum_blockTuples, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  refine sum_congr rfl fun k _ => ?_
  rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, MonoidAlgebra.coeff_sum,
    Finsupp.finsetSum_apply, Finset.sum_filter]
  congr 1
  refine sum_congr rfl fun rs _ => ?_
  rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul, coeff_blockWord_gen]
  split_ifs <;> simp

/-- **Theorem 2.2, equation (2.wordcut)** for `c(w)`. -/
theorem wordCoeff_eq (w : FreeMonoid (Fin 2)) :
    wordCoeff 𝕂 w =
      ∑ k ∈ range (FreeMonoid.length w), ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹) *
        ∑ rs ∈ (blockTuples (k + 1) (FreeMonoid.length w)).filter
          (fun rs => blockMonoid rs = w), blockWeight 𝕂 rs :=
  coeff_bchHom _ w

/-- `Zₙ(X, Y) = ∑_{|w| = n} c(w) w` in the free algebra: the coefficient of `w` in `Zₙ` is
`c(w)` when `|w| = n`, and `0` otherwise. -/
theorem coeff_bchHom_eq_wordCoeff (n : ℕ) (w : FreeMonoid (Fin 2)) :
    (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n).coeff w =
      if FreeMonoid.length w = n then wordCoeff 𝕂 w else 0 := by
  split_ifs with h
  · rw [wordCoeff, h]
  · have hhom := bchHom_isHomogeneous genX_isHomogeneous genY_isHomogeneous (𝕂 := 𝕂) n
    by_contra hne
    exact h (hhom w (Finsupp.mem_support_iff.mpr hne))

end Coefficients

end BCH
