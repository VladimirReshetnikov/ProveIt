import IPRADerivations.Geometry.EulerRodrigues

/-!
# The universal axis identities of a rotation matrix

Packet: `geometry/euler_rodrigues_ipra`, Lemma `lem:universal` (`eq:axis-adj`, `eq:s-identities`,
`eq:scalar-identities`), cleared of the factor `1/2`: for a `3 × 3` matrix `R` with `Rᵀ R = I` and
`det R = 1`, with `t = tr R`, `S' = 2S = R + Rᵀ − (t − 1) I`, `T' = 2T = R − Rᵀ` and
`a = 2w = (R₃₂ − R₂₃, R₁₃ − R₃₁, R₂₁ − R₁₂)`:

* `det (I − R) = 0`, `adj (I − R) = S'`;
* `R S' = Rᵀ S' = S'`, `S'² = (3 − t) S'` (`S² = dS`), `tr S' = 3 − t` (`tr S = d`), `T' S' = S' T' = 0`,
  `adj S' = 0`;
* `‖R − I‖²_F = 6 − 2t` (`= 4d`), `(t − 1)² + a·a = 4` (`c² + w·w = 1`), `a aᵀ = (t + 1) S'`
  (`w wᵀ = (1 + c) S`).

The proofs are matrix algebra over any commutative ring (`adj R = Rᵀ` from `R adj R = I`), with the
`3 × 3` shift identities and the Newton identity `tr (R²) = t² − 2 tr (adj R)`; no division is used.
Each identity is then read on the integer matrix terms of `Core/LinearAlgebra`.
-/

namespace LeanProofs.IPRA.Geometry.EulerRodriguesUniversal

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn Matrix
open scoped Fm

section Ring

variable {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R)

theorem det_shift3 : (1 - M).det = 1 - M.trace + M.adjugate.trace - M.det := by
  simp [Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.trace_fin_three]; ring

theorem adj_shift3 : (1 - M).adjugate = (1 - M.trace) • (1 : Matrix (Fin 3) (Fin 3) R) + M + M.adjugate := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.one_apply] <;> ring

theorem newton3 : (M * M).trace = M.trace ^ 2 - 2 * M.adjugate.trace := by
  simp [Matrix.adjugate_fin_three, Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]; ring

/-- `a·a = tr (Mᵀ M) − tr (M M)` for `a = (M₂₁ − M₁₂, M₀₂ − M₂₀, M₁₀ − M₀₁)`. -/
theorem skew_norm3 :
    (M 2 1 - M 1 2) ^ 2 + (M 0 2 - M 2 0) ^ 2 + (M 1 0 - M 0 1) ^ 2 = (Mᵀ * M).trace - (M * M).trace := by
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three]; ring

/-- `(M − Mᵀ)² = a aᵀ − (a·a) I`. -/
theorem skew_sq3 :
    (M - Mᵀ) * (M - Mᵀ) = Matrix.vecMulVec ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1]
        ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1] -
      ((M 2 1 - M 1 2) ^ 2 + (M 0 2 - M 2 0) ^ 2 + (M 1 0 - M 0 1) ^ 2) • (1 : Matrix (Fin 3) (Fin 3) R) := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.vecMulVec_apply, Matrix.one_apply] <;> ring

variable {M} (hO : Mᵀ * M = 1) (hD : M.det = 1)
include hO hD

/-- `S' = R + Rᵀ − (t − 1) I`. -/
abbrev S' : Matrix (Fin 3) (Fin 3) R := M + Mᵀ - (M.trace - 1) • (1 : Matrix (Fin 3) (Fin 3) R)

theorem adj_eq_transpose : M.adjugate = Mᵀ := by
  have h := Matrix.mul_adjugate M
  rw [hD, one_smul] at h
  calc M.adjugate = (Mᵀ * M) * M.adjugate := by rw [hO, Matrix.one_mul]
    _ = Mᵀ := by rw [Matrix.mul_assoc, h, Matrix.mul_one]

theorem mul_transpose_eq : M * Mᵀ = 1 := by
  have h := Matrix.mul_adjugate M
  rw [hD, one_smul, adj_eq_transpose hO hD] at h
  exact h

theorem det_one_sub : (1 - M).det = 0 := by
  rw [det_shift3, adj_eq_transpose hO hD, Matrix.trace_transpose, hD]; ring

theorem adj_one_sub : (1 - M).adjugate = S' (M := M) := by
  rw [adj_shift3, adj_eq_transpose hO hD]
  ext i j; simp [Matrix.one_apply]; split_ifs <;> ring

theorem mul_S : M * S' (M := M) = S' (M := M) := by
  have h := Matrix.mul_adjugate (1 - M)
  rw [det_one_sub hO hD, zero_smul, adj_one_sub hO hD, Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h
  exact h.symm

theorem transpose_mul_S : Mᵀ * S' (M := M) = S' (M := M) := by
  calc Mᵀ * S' (M := M) = Mᵀ * (M * S' (M := M)) := by rw [mul_S hO hD]
    _ = S' (M := M) := by rw [← Matrix.mul_assoc, hO, Matrix.one_mul]

omit hO hD in
theorem S_symm : (S' (M := M))ᵀ = S' (M := M) := by
  ext i j; simp [Matrix.one_apply, Matrix.transpose_apply]; split_ifs <;> simp_all [eq_comm] <;> ring

theorem S_mul : S' (M := M) * M = S' (M := M) := by
  have h := congrArg Matrix.transpose (transpose_mul_S hO hD)
  rwa [Matrix.transpose_mul, Matrix.transpose_transpose, S_symm] at h

theorem S_mul_transpose : S' (M := M) * Mᵀ = S' (M := M) := by
  have h := congrArg Matrix.transpose (mul_S hO hD)
  rwa [Matrix.transpose_mul, S_symm] at h

/-- `S'² = (3 − t) S'`. -/
theorem S_sq : S' (M := M) * S' (M := M) = (3 - M.trace) • S' (M := M) := by
  have h1 := mul_S hO hD; have h2 := transpose_mul_S hO hD
  conv_lhs => rw [show S' (M := M) = M + Mᵀ - (M.trace - 1) • (1 : Matrix (Fin 3) (Fin 3) R) from rfl]
  rw [Matrix.sub_mul, Matrix.add_mul, h1, h2, Matrix.smul_mul, Matrix.one_mul]
  module

omit hO hD in
/-- `tr S' = 3 − t`. -/
theorem trace_S : (S' (M := M)).trace = 3 - M.trace := by
  simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_transpose, Matrix.trace_smul, Matrix.trace_one]; ring

theorem T_S : (M - Mᵀ) * S' (M := M) = 0 := by
  rw [Matrix.sub_mul, mul_S hO hD, transpose_mul_S hO hD, sub_self]

theorem S_T : S' (M := M) * (M - Mᵀ) = 0 := by
  rw [Matrix.mul_sub, S_mul hO hD, S_mul_transpose hO hD, sub_self]

theorem adj_S : (S' (M := M)).adjugate = 0 := by
  rw [← adj_one_sub hO hD, Matrix.adjugate_adjugate _ (by simp), det_one_sub hO hD]; simp

omit hD in
/-- `‖R − I‖²_F = tr ((R − I)ᵀ (R − I)) = 6 − 2t`. -/
theorem frob : ((M - 1)ᵀ * (M - 1)).trace = 6 - 2 * M.trace := by
  rw [Matrix.transpose_sub, Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hO,
    Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
  simp [Matrix.trace_sub, Matrix.trace_add, Matrix.trace_transpose, Matrix.trace_one]; ring

/-- `(t − 1)² + a·a = 4` (`c² + w·w = 1`). -/
theorem circle : (M.trace - 1) ^ 2 + ((M 2 1 - M 1 2) ^ 2 + (M 0 2 - M 2 0) ^ 2 + (M 1 0 - M 0 1) ^ 2) = 4 := by
  rw [skew_norm3, hO, newton3, adj_eq_transpose hO hD, Matrix.trace_transpose, Matrix.trace_one]
  simp; ring

/-- `a aᵀ = (t + 1) S'` (`w wᵀ = (1 + c) S`). -/
theorem outer_S : Matrix.vecMulVec ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1]
      ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1] = (M.trace + 1) • S' (M := M) := by
  have hT := mul_transpose_eq hO hD
  have hsq := S_sq hO hD
  have hc := circle hO hD
  have sk := skew_sq3 M
  -- `(M + Mᵀ)² − (M − Mᵀ)² = 2 (M Mᵀ + Mᵀ M) = 4 I`.
  have pa : (M + Mᵀ) * (M + Mᵀ) - (M - Mᵀ) * (M - Mᵀ) = (4 : R) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    have e : (M + Mᵀ) * (M + Mᵀ) - (M - Mᵀ) * (M - Mᵀ) = (2 : R) • (M * Mᵀ + Mᵀ * M) := by
      rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub]
      module
    rw [e, hT, hO]; module
  -- `M + Mᵀ = S' + (t − 1) I`, so `(M + Mᵀ)² = (t + 1) S' + (t − 1)² I`.
  have hP : M + Mᵀ = S' (M := M) + (M.trace - 1) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    simp only [S']; abel
  have hP2 : (M + Mᵀ) * (M + Mᵀ) = (M.trace + 1) • S' (M := M) + (M.trace - 1) ^ 2 • (1 : Matrix (Fin 3) (Fin 3) R) := by
    rw [hP, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hsq, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul]
    module
  rw [sk, hP2] at pa
  have key : Matrix.vecMulVec ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1] ![M 2 1 - M 1 2, M 0 2 - M 2 0, M 1 0 - M 0 1] =
      (M.trace + 1) • S' (M := M) + ((M.trace - 1) ^ 2 + ((M 2 1 - M 1 2) ^ 2 + (M 0 2 - M 2 0) ^ 2 + (M 1 0 - M 0 1) ^ 2)
        - 4) • (1 : Matrix (Fin 3) (Fin 3) R) := by
    rw [← sub_eq_zero] at pa ⊢
    rw [← neg_eq_zero, ← pa]; module
  rw [key, hc, _root_.sub_self, zero_smul, _root_.add_zero]

end Ring

/-! ## The iPRA statements -/

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem conjFin_elim {k : ℕ} {f : Fin k → Fm PTm n} (h : Γ ⊢[PRAAx] conjFin f) (i : Fin k) : Γ ⊢[PRAAx] f i := by
  match k, f, h, i with
  | 1, _, h, i => rw [Fin.fin_one_eq_zero i]; exact h
  | _ + 2, _, h, i =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact Prf.andE₁ h
    · exact conjFin_elim (Prf.andE₂ h) j

theorem toZ_of_eqFm {k : ℕ} {M N : Mat k n} (h : Γ ⊢[PRAAx] Mat.eqFm M N) : Mat.toZ Γ M = Mat.toZ Γ N := by
  ext i j
  exact ZT.toZ_eq (conjFin_elim (conjFin_elim h i) j)

abbrev B : Mat 3 18 := fun i j => ZT.var2 ⟨2 * (3 * i + j), by omega⟩ ⟨2 * (3 * i + j) + 1, by omega⟩

/-- The hypotheses `Rᵀ R = I` and `det R = 1`. -/
def orthoB : Fm PTm 18 := Mat.eqFm (Mat.mul (Mat.transpose B) B) Mat.one
def detB : Fm PTm 18 := ZT.eq (Mat.det B) (ZT.natLit 1)

/-- `S' = R + Rᵀ − (t − 1) I`. -/
def SB : Mat 3 18 := Mat.sub (Mat.add B (Mat.transpose B)) (Mat.smul (Mat.trace B - ZT.natLit 1) Mat.one)
/-- `a = (R₂₁ − R₁₂, R₀₂ − R₂₀, R₁₀ − R₀₁)` (zero-based), i.e. `2w`. -/
def aB : Vec 3 18 := ![B 2 1 - B 1 2, B 0 2 - B 2 0, B 1 0 - B 0 1]

abbrev Γ₀ : List (Fm PTm 18) := [detB, orthoB]

theorem hyps : (Mat.toZ Γ₀ B)ᵀ * Mat.toZ Γ₀ B = 1 ∧ (Mat.toZ Γ₀ B).det = 1 := by
  have h1 := toZ_of_eqFm (Γ := Γ₀) (M := Mat.mul (Mat.transpose B) B) (N := Mat.one) (.hyp (by simp [orthoB]))
  have h2 := ZT.toZ_eq (Γ := Γ₀) (u := Mat.det B) (v := ZT.natLit 1) (.hyp (by simp [detB]))
  simp only [Mat.toZ_mul, Mat.toZ_transpose, Mat.toZ_one] at h1
  simp only [Mat.toZ_det, ZT.toZ_natLit, Nat.cast_one] at h2
  exact ⟨h1, h2⟩

theorem toZ_SB : Mat.toZ Γ₀ SB = S' (M := Mat.toZ Γ₀ B) := by
  simp [SB, Mat.toZ_sub, Mat.toZ_add, Mat.toZ_smul, Mat.toZ_transpose, Mat.toZ_one, Mat.toZ_trace, ZT.toZ_sub,
    ZT.toZ_natLit]

/-- `lem:universal`, `eq:axis-adj`: `det (I − R) = 0` and `adj (I − R) = S'`. -/
def axisAdjFormula : Fm PTm 18 :=
  orthoB ⟶ detB ⟶ (ZT.eq (Mat.det (Mat.sub Mat.one B)) (ZT.natLit 0) ⋏ Mat.eqFm (Mat.adj (Mat.sub Mat.one B)) SB)

theorem axis_adj : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 axisAdjFormula := by
  refine closeUniv 18 (.impI (.impI (.andI (ZT.derive ?_) (Mat.derive ?_))))
  · obtain ⟨hO, hD⟩ := hyps
    simp only [Mat.toZ_det, Mat.toZ_sub, Mat.toZ_one, ZT.toZ_natLit, Nat.cast_zero]
    exact det_one_sub hO hD
  · obtain ⟨hO, hD⟩ := hyps
    rw [toZ_SB, Mat.toZ_adj, Mat.toZ_sub, Mat.toZ_one]
    exact adj_one_sub hO hD

/-- `eq:s-identities`: `R S' = S'`, `Rᵀ S' = S'`, `S'² = (3 − t) S'`, `tr S' = 3 − t`, `T' S' = S' T' = 0`,
`adj S' = 0`. -/
def sIdentitiesFormula : Fm PTm 18 :=
  orthoB ⟶ detB ⟶ (Mat.eqFm (Mat.mul B SB) SB ⋏ (Mat.eqFm (Mat.mul (Mat.transpose B) SB) SB ⋏
    (Mat.eqFm (Mat.mul SB SB) (Mat.smul (ZT.natLit 3 - Mat.trace B) SB) ⋏ (ZT.eq (Mat.trace SB) (ZT.natLit 3 - Mat.trace B) ⋏
    (Mat.eqFm (Mat.mul (Mat.sub B (Mat.transpose B)) SB) Mat.zero ⋏ (Mat.eqFm (Mat.mul SB (Mat.sub B (Mat.transpose B))) Mat.zero ⋏
    Mat.eqFm (Mat.adj SB) Mat.zero))))))

theorem s_identities : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 sIdentitiesFormula := by
  obtain ⟨hO, hD⟩ := hyps
  refine closeUniv 18 (.impI (.impI (.andI (Mat.derive ?_) (.andI (Mat.derive ?_) (.andI (Mat.derive ?_)
    (.andI (ZT.derive ?_) (.andI (Mat.derive ?_) (.andI (Mat.derive ?_) (Mat.derive ?_)))))))))
  · rw [Mat.toZ_mul, toZ_SB]; exact mul_S hO hD
  · rw [Mat.toZ_mul, Mat.toZ_transpose, toZ_SB]; exact transpose_mul_S hO hD
  · rw [Mat.toZ_mul, Mat.toZ_smul, toZ_SB, ZT.toZ_sub, Mat.toZ_trace, ZT.toZ_natLit]
    rw [S_sq hO hD]; norm_num
  · rw [Mat.toZ_trace, toZ_SB, ZT.toZ_sub, Mat.toZ_trace, ZT.toZ_natLit, trace_S]; norm_num
  · rw [Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_transpose, toZ_SB, Mat.toZ_zero]; exact T_S hO hD
  · rw [Mat.toZ_mul, Mat.toZ_sub, Mat.toZ_transpose, toZ_SB, Mat.toZ_zero]; exact S_T hO hD
  · rw [Mat.toZ_adj, toZ_SB, Mat.toZ_zero]; exact adj_S hO hD

/-- `eq:scalar-identities`: `‖R − I‖²_F = 6 − 2t`, `(t − 1)² + a·a = 4`, `a aᵀ = (t + 1) S'`. -/
def scalarFormula : Fm PTm 18 :=
  orthoB ⟶ detB ⟶ (ZT.eq (Mat.trace (Mat.mul (Mat.transpose (Mat.sub B Mat.one)) (Mat.sub B Mat.one)))
      (ZT.natLit 6 - ZT.natLit 2 * Mat.trace B) ⋏
    (ZT.eq (ZT.sq (Mat.trace B - ZT.natLit 1) + (ZT.sq (aB 0) + ZT.sq (aB 1) + ZT.sq (aB 2))) (ZT.natLit 4) ⋏
    Mat.eqFm (fun i j => aB i * aB j) (Mat.smul (Mat.trace B + ZT.natLit 1) SB)))

theorem scalar_identities : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 18 scalarFormula := by
  obtain ⟨hO, hD⟩ := hyps
  refine closeUniv 18 (.impI (.impI (.andI (ZT.derive ?_) (.andI (ZT.derive ?_) (Mat.derive ?_)))))
  · rw [Mat.toZ_trace, Mat.toZ_mul, Mat.toZ_transpose, Mat.toZ_sub, Mat.toZ_one, ZT.toZ_sub, ZT.toZ_mul,
      Mat.toZ_trace, ZT.toZ_natLit, ZT.toZ_natLit, frob hO]; norm_num
  · have c := circle hO hD
    simp only [ZT.toZ_add, ZT.toZ_sq, ZT.toZ_sub, Mat.toZ_trace, ZT.toZ_natLit, aB] at c ⊢
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
      ZT.toZ_sub, Mat.toZ_apply] at c ⊢
    push_cast at c ⊢
    linear_combination c
  · have o := outer_S hO hD
    rw [Mat.toZ_smul, toZ_SB, ZT.toZ_add, Mat.toZ_trace, ZT.toZ_natLit, Nat.cast_one, ← o]
    ext i j; fin_cases i <;> fin_cases j <;> simp [aB, Matrix.vecMulVec_apply, ZT.toZ_mul, ZT.toZ_sub]


end LeanProofs.IPRA.Geometry.EulerRodriguesUniversal
