/-
# The Dynkin–Specht–Wever lemma and Dynkin's formula (Lemma 3.4, Theorem 4.1)

This file formalizes, in the free algebra `𝕂⟨X, Y⟩` of `BCH.Formal.Free`:

* the right Dynkin operator `R`, the linear extension of the right-nested
  bracketing of words `R(a₁ ⋯ aₙ) = [a₁, [a₂, …, [aₙ₋₁, aₙ]]]` (equation (1.4) of
  the accompanying article, `docs/combined`);
* the identity `R(ab) = φ(a) R(b) + ε(b) R(a)`, where `φ` is the adjoint
  representation `X ↦ ad_X` of the free algebra on itself and `ε(b)` the
  constant term of `b`;
* **Lemma 3.4 (Dynkin–Specht–Wever)** in its Lie form: for a homogeneous Lie
  polynomial `P` of degree `n`, `R(P) = n P` (`R_of_mem_lieGen`);
* **Theorem 4.1 (Dynkin's formula)**, equation (4.2): `Zₙ = (1/n) R(Zₙ)
  = (1/n) ∑_w c(w) R(w)` with `c(w)` the word coefficients of `Zₙ`
  (`bchHom_eq_inv_smul_R`, `bchHom_eq_dynkin`), and equation (4.1), the
  all-terms form `Zₙ = (1/n) ∑_k (-1)^{k-1}/k ∑ R(X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k}) / ∏ rᵢ!sᵢ!`
  (`bchHom_eq_dynkin_blocks`).

The proof of the lemma is the classical one: `φ` restricted to the Lie
polynomials is the adjoint representation `ad` (both are Lie homomorphisms
agreeing on the generators), so for homogeneous Lie polynomials `A, B` of
degrees `p, q ≥ 1` with `R(A) = pA`, `R(B) = qB` one gets
`R([A, B]) = φ(A) R(B) - φ(B) R(A) = q [A, B] - p [B, A] = (p + q) [A, B]`;
the statement is propagated along the Lie span componentwise, using that the
Lie polynomials are graded.
-/
import BCH.Formal.LieSeries
import BCH.Formal.WordCut

open Finset

attribute [local instance 100] LieRing.ofAssociativeRing

namespace BCH

section Dynkin

variable (𝕂 : Type*) [RCLike 𝕂]

/-- The generator of index `i` (`gen 0 = X`, `gen 1 = Y`). -/
noncomputable def gen (i : Fin 2) : FreeTwo 𝕂 := MonoidAlgebra.single (FreeMonoid.of i) 1

lemma gen_zero : gen 𝕂 0 = genX 𝕂 := rfl

lemma gen_one : gen 𝕂 1 = genY 𝕂 := rfl

/-- The right-nested bracket of a word, on lists of letters. -/
noncomputable def rbList : List (Fin 2) → FreeTwo 𝕂
  | [] => 0
  | [i] => gen 𝕂 i
  | i :: j :: rest => ⁅gen 𝕂 i, rbList (j :: rest)⁆

/-- The right-nested bracket `R(w)` of a word `w`. -/
noncomputable def rb (w : FreeMonoid (Fin 2)) : FreeTwo 𝕂 := rbList 𝕂 (FreeMonoid.toList w)

lemma rb_one : rb 𝕂 1 = 0 := rfl

lemma rb_of (i : Fin 2) : rb 𝕂 (FreeMonoid.of i) = gen 𝕂 i := rfl

lemma FreeMonoid.eq_one_of_toList_eq_nil {w : FreeMonoid (Fin 2)} (h : FreeMonoid.toList w = []) :
    w = 1 :=
  FreeMonoid.toList.injective (h.trans FreeMonoid.toList_one.symm)

lemma rb_of_mul (i : Fin 2) {w : FreeMonoid (Fin 2)} (hw : w ≠ 1) :
    rb 𝕂 (FreeMonoid.of i * w) = ⁅gen 𝕂 i, rb 𝕂 w⁆ := by
  obtain ⟨j, rest, hrest⟩ : ∃ j rest, FreeMonoid.toList w = j :: rest := by
    cases h : FreeMonoid.toList w with
    | nil => exact absurd (FreeMonoid.eq_one_of_toList_eq_nil h) hw
    | cons j rest => exact ⟨j, rest, rfl⟩
  rw [rb, rb, FreeMonoid.toList_mul, FreeMonoid.toList_of, hrest]
  rfl

variable {𝕂}

/-- The coefficient map as a linear map. -/
noncomputable def coeffₗ : FreeTwo 𝕂 →ₗ[𝕂] (FreeMonoid (Fin 2) →₀ 𝕂) where
  toFun a := a.coeff
  map_add' := MonoidAlgebra.coeff_add
  map_smul' := MonoidAlgebra.coeff_smul

/-- The right Dynkin operator: the linear extension of `w ↦ R(w)`. -/
noncomputable def R : FreeTwo 𝕂 →ₗ[𝕂] FreeTwo 𝕂 :=
  (Finsupp.linearCombination 𝕂 (rb 𝕂)).comp coeffₗ

lemma R_single (w : FreeMonoid (Fin 2)) (c : 𝕂) :
    R (MonoidAlgebra.single w c) = c • rb 𝕂 w := by
  simp [R, coeffₗ, MonoidAlgebra.coeff_single, Finsupp.linearCombination_single]

/-- `R` on an element with coefficients `c(w)`: `R(a) = ∑_w c(w) R(w)`. -/
lemma R_apply (a : FreeTwo 𝕂) : R a = a.coeff.sum fun w c => c • rb 𝕂 w := by
  simp [R, coeffₗ, Finsupp.linearCombination_apply]

variable (𝕂)

/-- The adjoint representation of the free algebra on itself, `φ(X) = ad_X`. -/
noncomputable def adRep : FreeTwo 𝕂 →ₐ[𝕂] Module.End 𝕂 (FreeTwo 𝕂) :=
  MonoidAlgebra.lift 𝕂 (Module.End 𝕂 (FreeTwo 𝕂)) (FreeMonoid (Fin 2))
    (FreeMonoid.lift fun i => LieAlgebra.ad 𝕂 (FreeTwo 𝕂) (gen 𝕂 i))

/-- The word action `u ↦ ad_{a₁} ∘ ⋯ ∘ ad_{aₖ}`. -/
noncomputable def adWord : FreeMonoid (Fin 2) →* Module.End 𝕂 (FreeTwo 𝕂) :=
  FreeMonoid.lift fun i => LieAlgebra.ad 𝕂 (FreeTwo 𝕂) (gen 𝕂 i)

lemma adRep_single (u : FreeMonoid (Fin 2)) (c : 𝕂) :
    adRep 𝕂 (MonoidAlgebra.single u c) = c • adWord 𝕂 u :=
  MonoidAlgebra.lift_single _ _ _

lemma adRep_gen (i : Fin 2) : adRep 𝕂 (gen 𝕂 i) = LieAlgebra.ad 𝕂 (FreeTwo 𝕂) (gen 𝕂 i) := by
  rw [gen, adRep_single, one_smul, adWord, FreeMonoid.lift_eval_of]
  rfl

lemma FreeMonoid.mul_ne_one_of_right {u w : FreeMonoid (Fin 2)} (hw : w ≠ 1) : u * w ≠ 1 := by
  intro h
  have h1 : FreeMonoid.length (u * w) = 0 := by rw [h, FreeMonoid.length_one]
  rw [FreeMonoid.length_mul] at h1
  apply hw
  apply FreeMonoid.eq_one_of_toList_eq_nil
  exact List.length_eq_zero_iff.mp (by change FreeMonoid.length w = 0; omega)

/-- `R(u w) = ad_{u₁} ⋯ ad_{uₖ} R(w)` for a nonempty word `w`. -/
lemma rb_mul (u : FreeMonoid (Fin 2)) {w : FreeMonoid (Fin 2)} (hw : w ≠ 1) :
    rb 𝕂 (u * w) = adWord 𝕂 u (rb 𝕂 w) := by
  induction u using FreeMonoid.inductionOn' with
  | one => simp
  | mul_of i u ih =>
    rw [mul_assoc, rb_of_mul 𝕂 i (FreeMonoid.mul_ne_one_of_right hw), ih, map_mul,
      Module.End.mul_apply, adWord, FreeMonoid.lift_eval_of, LieAlgebra.ad_apply]

variable {𝕂}

/-- The basic identity `R(ab) = φ(a) R(b) + ε(b) R(a)`, `ε(b)` the constant term of `b`. -/
theorem R_mul (a b : FreeTwo 𝕂) : R (a * b) = adRep 𝕂 a (R b) + (b.coeff 1) • R a := by
  classical
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    rw [add_mul, map_add, ha, ha', map_add, LinearMap.add_apply, map_add, smul_add]
    abel
  | single u c =>
    induction b using MonoidAlgebra.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      rw [mul_add, map_add, hb, hb', map_add, map_add, MonoidAlgebra.coeff_add,
        Finsupp.add_apply, add_smul]
      abel
    | single w d =>
      rw [MonoidAlgebra.single_mul_single, R_single, R_single, R_single, adRep_single,
        MonoidAlgebra.coeff_single, Finsupp.single_apply, LinearMap.smul_apply, map_smul]
      by_cases hw : w = 1
      · subst hw
        rw [if_pos rfl, mul_one, rb_one, map_zero, smul_zero, smul_zero, zero_add, smul_smul,
          mul_comm c d]
      · rw [if_neg hw, zero_smul, add_zero, rb_mul 𝕂 u hw, smul_smul]

/-- On the Lie polynomials, `φ` is the adjoint representation. -/
theorem adRep_eq_ad_of_mem {A : FreeTwo 𝕂} (hA : A ∈ lieGen 𝕂) :
    adRep 𝕂 A = LieAlgebra.ad 𝕂 (FreeTwo 𝕂) A := by
  induction hA using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact adRep_gen 𝕂 0
    · exact adRep_gen 𝕂 1
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]
  | lie x y _ _ hx hy =>
    rw [LieHom.map_lie, Ring.lie_def, map_sub, map_mul, map_mul, hx, hy, Ring.lie_def]

lemma coeff_one_eq_zero_of_isHomogeneous {p : ℕ} {a : FreeTwo 𝕂} (ha : IsHomogeneous p a)
    (hp : p ≠ 0) : a.coeff 1 = 0 := by
  by_contra h
  have := ha 1 (Finsupp.mem_support_iff.mpr h)
  rw [FreeMonoid.length_one] at this
  exact hp this.symm

/-- Lie polynomials have no constant term. -/
lemma proj_zero_of_mem_lieGen {P : FreeTwo 𝕂} (hP : P ∈ lieGen 𝕂) : proj 0 P = 0 := by
  induction hP using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact proj_of_isHomogeneous_ne genX_isHomogeneous one_ne_zero
    · exact proj_of_isHomogeneous_ne genY_isHomogeneous one_ne_zero
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
  | smul c x _ hx => rw [map_smul, hx, smul_zero]
  | lie x y _ _ hx hy =>
    obtain ⟨N, M, key⟩ := proj_lie x y 0
    rw [key]
    refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun q _ => ?_
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ : p = 0 ∧ q = 0 := by omega
      rw [hx, hy, lie_zero]
    · rfl

/-- **Lemma 3.4 (Dynkin–Specht–Wever), componentwise**: for a Lie polynomial `P`,
`R(Pₙ) = n Pₙ` for every homogeneous component `Pₙ`. -/
theorem R_proj_of_mem_lieGen {P : FreeTwo 𝕂} (hP : P ∈ lieGen 𝕂) :
    ∀ n : ℕ, R (proj n P) = (n : 𝕂) • proj n P := by
  induction hP using LieSubalgebra.lieSpan_induction with
  | mem x hx =>
    intro n
    have hgen : ∀ i : Fin 2, R (proj n (gen 𝕂 i)) = (n : 𝕂) • proj n (gen 𝕂 i) := by
      intro i
      have hi : IsHomogeneous 1 (gen 𝕂 i) := by
        have := IsHomogeneous.single (𝕂 := 𝕂) (FreeMonoid.of i) 1
        rwa [FreeMonoid.length_of] at this
      by_cases hn : n = 1
      · subst hn
        rw [proj_of_isHomogeneous hi, gen, R_single, rb_of, one_smul, Nat.cast_one, one_smul]
        rfl
      · rw [proj_of_isHomogeneous_ne hi (Ne.symm hn), map_zero, smul_zero]
    rcases hx with rfl | rfl
    · exact hgen 0
    · exact hgen 1
  | zero => intro n; simp
  | add x y _ _ hx hy => intro n; rw [map_add, map_add, hx n, hy n, smul_add]
  | smul c x _ hx => intro n; rw [map_smul, map_smul, hx n, smul_comm]
  | lie x y hxmem hymem hx hy =>
    intro n
    obtain ⟨N, M, key⟩ := proj_lie x y n
    rw [key, map_sum, Finset.smul_sum]
    refine sum_congr rfl fun p _ => ?_
    rw [map_sum, Finset.smul_sum]
    refine sum_congr rfl fun q _ => ?_
    split_ifs with hpq
    · by_cases hp : p = 0
      · subst hp; rw [proj_zero_of_mem_lieGen hxmem, zero_lie, map_zero, smul_zero]
      by_cases hq : q = 0
      · subst hq; rw [proj_zero_of_mem_lieGen hymem, lie_zero, map_zero, smul_zero]
      have hA := hx p
      have hB := hy q
      have hAmem : proj p x ∈ lieGen 𝕂 := proj_mem_lieSpan hxmem p
      have hBmem : proj q y ∈ lieGen 𝕂 := proj_mem_lieSpan hymem q
      have hcA : (proj p x).coeff 1 = 0 :=
        coeff_one_eq_zero_of_isHomogeneous (proj_isHomogeneous p x) hp
      have hcB : (proj q y).coeff 1 = 0 :=
        coeff_one_eq_zero_of_isHomogeneous (proj_isHomogeneous q y) hq
      have hsub : ⁅proj p x, proj q y⁆ = proj p x * proj q y - proj q y * proj p x :=
        Ring.lie_def _ _
      conv_lhs => rw [hsub]
      rw [map_sub, R_mul, R_mul, hA, hB, adRep_eq_ad_of_mem hAmem, adRep_eq_ad_of_mem hBmem,
        map_smul, map_smul, LieAlgebra.ad_apply, LieAlgebra.ad_apply, hcA, hcB, zero_smul,
        zero_smul, add_zero, add_zero, ← lie_skew (proj q y) (proj p x), smul_neg,
        sub_neg_eq_add, ← hpq, Nat.cast_add, add_smul, add_comm]
    · rw [map_zero, smul_zero]

/-- **Lemma 3.4 (Dynkin–Specht–Wever)**: for a homogeneous Lie polynomial `P` of degree `n`,
`R(P) = n P`. -/
theorem R_of_mem_lieGen {n : ℕ} {P : FreeTwo 𝕂} (hP : P ∈ lieGen 𝕂) (hn : IsHomogeneous n P) :
    R P = (n : 𝕂) • P := by
  have h := R_proj_of_mem_lieGen hP n
  rwa [proj_of_isHomogeneous hn] at h

/-- **Dynkin's formula**, operator form: `R(Zₙ) = n Zₙ`. -/
theorem R_bchHom (n : ℕ) :
    R (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n) = (n : 𝕂) • bchHom 𝕂 (genX 𝕂) (genY 𝕂) n :=
  R_of_mem_lieGen (bchHom_mem_lieGen n)
    (bchHom_isHomogeneous genX_isHomogeneous genY_isHomogeneous n)

/-- **Theorem 4.1, equation (4.2)**: `Zₙ = (1/n) R(Zₙ)` for `n ≥ 1`. -/
theorem bchHom_eq_inv_smul_R {n : ℕ} (hn : 0 < n) :
    bchHom 𝕂 (genX 𝕂) (genY 𝕂) n = (n : 𝕂)⁻¹ • R (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n) := by
  rw [R_bchHom, smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn.ne'), one_smul]

/-- **Theorem 4.1, equation (4.2)** in terms of word coefficients:
`Zₙ = (1/n) ∑_w c(w) R(w)` where `c(w)` are the coefficients of `Zₙ`. -/
theorem bchHom_eq_dynkin {n : ℕ} (hn : 0 < n) :
    bchHom 𝕂 (genX 𝕂) (genY 𝕂) n =
      (n : 𝕂)⁻¹ • (bchHom 𝕂 (genX 𝕂) (genY 𝕂) n).coeff.sum (fun w c => c • rb 𝕂 w) := by
  rw [← R_apply]
  exact bchHom_eq_inv_smul_R hn

/-- **Theorem 4.1, equation (4.1)** (Dynkin's all-terms formula), degree-`n` part:
`Zₙ = (1/n) ∑_{k=1}^{n} (-1)^{k-1}/k ∑_{(rᵢ,sᵢ)} R(X^{r₁}Y^{s₁}⋯X^{r_k}Y^{s_k}) / ∏ᵢ rᵢ!sᵢ!`,
the inner sum over the `k`-tuples of blocks of positive degree and total degree `n`. -/
theorem bchHom_eq_dynkin_blocks {n : ℕ} (hn : 0 < n) :
    bchHom 𝕂 (genX 𝕂) (genY 𝕂) n =
      (n : 𝕂)⁻¹ • ∑ k ∈ range n, ((-1 : 𝕂) ^ k * ((k + 1 : ℕ) : 𝕂)⁻¹) •
        ∑ rs ∈ blockTuples (k + 1) n, blockWeight 𝕂 rs • R (blockWord (genX 𝕂) (genY 𝕂) rs) := by
  rw [bchHom_eq_inv_smul_R hn]
  congr 1
  rw [bchHom_eq_sum_blockTuples, map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_smul, map_sum]
  refine congrArg _ (sum_congr rfl fun rs _ => ?_)
  rw [map_smul]

end Dynkin

end BCH
