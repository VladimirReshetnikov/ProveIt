import IPRADerivations.DiophantineNumberTheory.KhinchinWidths
import IPRADerivations.DiophantineNumberTheory.KhinchinTailMass
import IPRADerivations.DiophantineNumberTheory.KhinchinCellParams

/-!
# The block hypotheses from `ψ` and the divergence modulus (`hurwitz_khinchin_ipra`, (K2))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"One call to the divergence modulus
supplies the block": "Let `K = K(J,N)`, let `s = 2^K`, and put `B = ⌈log₂ D(s)⌉` … Monotonicity gives
`1 ≤ Σ_{q=s}^{D(s)} ψ(q) ≤ Σ_{k=K}^B 2^k ψ(2^k)` … Hence `S ≥ 1`, as required for (K11)."

The function is `ψ(q) = Ψ(q, x)/C` with a natural-valued numerator body `Ψ` (parameter `x`) and denominator
`C ≥ 1`; it is nonincreasing (`Ψ(q+1) ≤ Ψ(q)`), and the unit-tail modulus `D` (a body `Dm` in `(s, x)`) satisfies
(K-D) cleared: `C + Σ_{q<s} Ψ(q) ≤ Σ_{q<D(s)+1} Ψ(q)` for `s ≥ 1`. With `s = 2^{K₀}` the block has the
`B = D(2^{K₀})` scales `Q_k = 2^{K₀+k}`, `k < B` — `D(s) + 1 ≤ 2^{K₀+B}` already, so no logarithm is needed.

* `mono_far`, `block_le`: monotonicity gives `Ψ(a+i) ≤ Ψ(a)` and the dyadic majorant `Σ_{i<L} Ψ(a+i) ≤ L Ψ(a)`
  (the hypothesis `hblk` of `KhinchinTailMass`);
* `len_mono`, `kd_tail`: (K-D) at `s = 2^{K₀}` gives `C + Σ_{q<2^{K₀}} Ψ ≤ Σ_{q<2^{K₀+B}} Ψ`;
* `wbK`: the width body. The widths are exact on the grid `T = R! G`: `w_k = T t_k / (4 Q_k² C)` with the capped
  mass `t_k = min(2^{K₀+k} Ψ(2^{K₀+k}), C)`, read from the block parameters `X = Xt K₀ ⟨⟨C, x⟩, Q⟩ R G α γ b₀`
  (the numerator range `M = ⟨⟨C, x⟩, Q⟩ ≥ Q` carries `C, x`; `w_at` decodes it);
* `w_exact`: `4 Q_k² C w_k = T t_k` when `4 Q_k² C ≤ R` (so `4 Q_k² C ∣ R!`);
* `cell_cover`: the conclusion of `KhinchinBlock.block_cover` for one cell `g` of the coarse grid `G = p + 1`, with
  `J* = ((4g+1)/4G, (4g+3)/4G)`, from `C ≥ 1`, monotonicity, (K-D), `K₀ ≥ 512 G`, `M ≥ 2^{K₀+B}`,
  `4 C 4^{K₀+B} ≤ R` and `R² ≤ G'` — every other hypothesis of `block_cover` is discharged here
  (`hW` by `KhinchinWidths.hW_of_exact`, `hS` by `hS_of_exact` and `KhinchinTailMass.S_ge_one`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Widths

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (shift_inst2')
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt Qk uB u_at pw_mono2 bB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (block_cover)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinWidths (hW_of_exact hS_of_exact)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinTailMass (S_ge_one)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinDyadic (dyB inst2_dyB)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinAmplify (mn MB inst2_MB mn_le_bound)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinCellParams (αc γc b0c cell_hag cell_hg cell_hD cell_gap)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `1 ≤ t` gives `t = succ (pred t)`. -/
alias pos_of_one := Common.pos_of_one_le

theorem one_le_pw (K : PTm n) : Γ ⊢[PRAAx] le one (pw two K) :=
  pw_one_le (Common.one_le_succ one) K

/-! ## Monotone numerators -/

/-- `ψ` is nonincreasing: `∀q, Ψ(q+1, x) ≤ Ψ(q, x)`. -/
def monoF (Ψ : PTm 2) (x : PTm n) : Fm PTm n :=
  Fm.all (le (inst2 Ψ (succ (var 0)) (Syn.shift x)) (inst2 Ψ (var 0) (Syn.shift x)))

@[simp] theorem subst_monoF {m : ℕ} (σ : Fin n → PTm m) (Ψ : PTm 2) (x : PTm n) :
    (monoF Ψ x).subst σ = monoF Ψ (Syn.subst σ x) := by
  simp only [monoF, Fm.subst_all, subst_le, subst_inst2, ConciseIPRA.PTm.subst_succ, Syn.subst_var,
    Syn.up_zero, subst_up_shift_pal]

theorem shift_monoF (Ψ : PTm 2) (x : PTm n) : Fm.shift (monoF Ψ x) = monoF Ψ (Syn.shift x) := by
  simp [Fm.shift, Syn.shift]

/-- The unit-tail modulus (K-D), cleared: `∀s ≥ 1, C + Σ_{q<s} Ψ(q) ≤ Σ_{q<D(s)+1} Ψ(q)`. -/
def kdF (Ψ Dm : PTm 2) (C x : PTm n) : Fm PTm n :=
  Fm.all (le one (var 0) ⟶
    le (Syn.shift C + ap2 (sumF Ψ) (var 0) (Syn.shift x))
      (ap2 (sumF Ψ) (succ (inst2 Dm (var 0) (Syn.shift x))) (Syn.shift x)))

@[simp] theorem subst_kdF {m : ℕ} (σ : Fin n → PTm m) (Ψ Dm : PTm 2) (C x : PTm n) :
    (kdF Ψ Dm C x).subst σ = kdF Ψ Dm (Syn.subst σ C) (Syn.subst σ x) := by
  simp only [kdF, Fm.subst_all, Fm.subst_imp, subst_le, subst_inst2, subst_ap2, PTm.subst_add,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.up_zero, subst_up_shift_pal]

theorem shift_kdF (Ψ Dm : PTm 2) (C x : PTm n) : Fm.shift (kdF Ψ Dm C x) = kdF Ψ Dm (Syn.shift C) (Syn.shift x) := by
  simp [Fm.shift, Syn.shift]

/-- Monotonicity at any term of the shifted context. -/
theorem mono_shift (Ψ : PTm 2) {x : PTm n} (hmono : Γ ⊢[PRAAx] monoF Ψ x) (t : PTm (n + 1)) :
    Γ.map Fm.shift ⊢[PRAAx] le (inst2 Ψ (succ t) (Syn.shift x)) (inst2 Ψ t (Syn.shift x)) := by
  have h := hmono.shift
  rw [shift_monoF] at h
  have a := Prf.allE t h
  simp only [subst_le, subst_inst2, ConciseIPRA.PTm.subst_succ, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift] at a
  exact a

/-- `Ψ(a + i) ≤ Ψ(a)` for every `i`. -/
theorem mono_far (Ψ : PTm 2) {x : PTm n} (a : PTm n) (hmono : Γ ⊢[PRAAx] monoF Ψ x) :
    Γ ⊢[PRAAx] Fm.all (le (inst2 Ψ (Syn.shift a + var 0) (Syn.shift x)) (inst2 Ψ (Syn.shift a) (Syn.shift x))) := by
  refine PRA.qfInd _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
    exact le_congr (congrInst2 Ψ (add_zero a).eqSymm (.eqRefl x)) (.eqRefl _) (le_refl _)
  · simp only [subst_le, subst_inst2, PTm.subst_add, Syn.subst_var, Syn.repl_zero, subst_repl_shift]
    have m := mono_shift Ψ hmono (Syn.shift a + var 0)
    have m' := le_congr (congrInst2 Ψ (add_succ (Syn.shift a) (var 0)).eqSymm (.eqRefl _)) (.eqRefl _) m
    exact le_trans m'.wk Prf.hyp0

/-- The dyadic majorant: `Σ_{i<L} Ψ(a + i) ≤ L Ψ(a)`. -/
theorem block_le (Ψ : PTm 2) {x : PTm n} (a L : PTm n) (hmono : Γ ⊢[PRAAx] monoF Ψ x) :
    Γ ⊢[PRAAx] le (ap2 (sumF (offB Ψ)) L (pairT a x)) (L * inst2 Ψ a x) := by
  refine sum_le_const (offB Ψ) (.allI (.impI ?_))
  have hf := (mono_far Ψ a hmono).allOpen.wk (ψ := lt (var 0) (Syn.shift L))
  rw [inst2_offB, shift_inst2', show Syn.shift (pairT a x) = pairT (Syn.shift a) (Syn.shift x) by simp [Syn.shift]]
  exact le_congr (congrInst2 Ψ (congrAdd (fst_pair _ _).eqSymm (.eqRefl _)) (snd_pair _ _).eqSymm) (.eqRefl _) hf

/-! ## The divergence modulus -/

/-- Sums of naturals grow with the length. -/
theorem len_mono (f : PTm 2) {a b : PTm n} (x : PTm n) (h : Γ ⊢[PRAAx] le a b) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) a x) (ap2 (sumF f) b x) := by
  have e := natEq ((congrAp2 (sumF f) (eq_add_of_le h) (.eqRefl x)).eqTrans (sum_split f a (monus b a) x))
  ipra_le 𝔞 (ap2 (sumF (offB f)) (monus b a) (pairT a x)) with e

/-- (K-D) at `s = 2^K`, with `B = D(2^K)`: `C + Σ_{q<2^K} Ψ ≤ Σ_{q<2^{K+B}} Ψ`. -/
theorem kd_tail (Ψ Dm : PTm 2) (K : PTm n) {C x : PTm n} (hKD : Γ ⊢[PRAAx] kdF Ψ Dm C x) :
    Γ ⊢[PRAAx] le (C + ap2 (sumF Ψ) (pw two K) x) (ap2 (sumF Ψ) (pw two (K + inst2 Dm (pw two K) x)) x) := by
  have a := Prf.allE (pw two K) hKD
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_inst2, PTm.subst_add, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  have h1 := Prf.impE a (one_le_pw K)
  have hl := LeanProofs.IPRA.AnalyticNumberTheory.Valuation.lt_pw (Γ := Γ) (le_refl two)
    (K + inst2 Dm (pw two K) x)
  have hB : Γ ⊢[PRAAx] le (succ (inst2 Dm (pw two K) x)) (pw two (K + inst2 Dm (pw two K) x)) := by
    ipra_le sl hl + 𝔞 K
  exact le_trans h1 (len_mono Ψ x hB)

/-! ## Exact widths -/

/-- The capped scale mass `t_k = min(2^{K₀+k} Ψ(2^{K₀+k}), C)`. -/
abbrev tval (Ψ : PTm 2) (K0 k C x : PTm n) : PTm n := mn (Qk K0 k * inst2 Ψ (Qk K0 k) x) C

/-- The exact width `w_k = T t_k / (4 Q_k² C)` on the grid `T = R! G`. -/
abbrev wval (Ψ : PTm 2) (K0 k R G C x : PTm n) : PTm n :=
  quo (fact R * G * tval Ψ K0 k C x) (num 4 * (Qk K0 k * Qk K0 k) * C)

/-- The width core in `0 = k, 1 = K₀, 2 = R, 3 = G, 4 = C, 5 = x`. -/
def wCore (Ψ : PTm 2) : PTm 6 :=
  quo (fact (var 2) * var 3 * mn (pw two (var 1 + var 0) * inst2 Ψ (pw two (var 1 + var 0)) (var 5)) (var 4))
    (num 4 * (pw two (var 1 + var 0) * pw two (var 1 + var 0)) * var 4)

/-- The width body over `0 = k`, `1 = X`, for `X = Xt K₀ ⟨⟨C, x⟩, Q⟩ R G α γ b₀`. -/
def wbK (Ψ : PTm 2) : PTm 2 :=
  Syn.subst ![var 0, fstT (var 1), fstT (sndT (sndT (var 1))), fstT (sndT (sndT (sndT (var 1)))),
    fstT (fstT (fstT (sndT (var 1)))), sndT (fstT (fstT (sndT (var 1))))] (wCore Ψ)

theorem inst2_wbK (Ψ : PTm 2) (k X : PTm n) :
    inst2 (wbK Ψ) k X = Syn.subst ![k, fstT X, fstT (sndT (sndT X)), fstT (sndT (sndT (sndT X))),
      fstT (fstT (fstT (sndT X))), sndT (fstT (fstT (sndT X)))] (wCore Ψ) := by
  simp only [inst2, wbK]
  rw [Syn.subst_subst]
  exact congrArg (fun σ => Syn.subst σ (wCore Ψ)) (funext fun i => by fin_cases i <;> simp)

theorem wCore_at (Ψ : PTm 2) (k K0 R G C x : PTm n) :
    Syn.subst ![k, K0, R, G, C, x] (wCore Ψ) = wval Ψ K0 k R G C x := by
  simp [wCore, wval, tval, subst_ap2]

/-- Decoding the width body. -/
theorem w_at (Ψ : PTm 2) (k K0 C x Q R G α γ b0 : PTm n) :
    Γ ⊢[PRAAx] inst2 (wbK Ψ) k (Xt K0 (pairT (pairT C x) Q) R G α γ b0) ≐ wval Ψ K0 k R G C x := by
  rw [inst2_wbK, ← wCore_at]
  have s1 : Γ ⊢[PRAAx] sndT (Xt K0 (pairT (pairT C x) Q) R G α γ b0) ≐
      pairT (pairT (pairT C x) Q) (pairT R (pairT G (pairT α (pairT γ b0)))) := snd_pair _ _
  have s2 := (congrSnd s1).eqTrans (snd_pair (Γ := Γ) (pairT (pairT C x) Q) _)
  have s3 := (congrSnd s2).eqTrans (snd_pair (Γ := Γ) R _)
  have eM := (congrFst s1).eqTrans (fst_pair (Γ := Γ) (pairT (pairT C x) Q) _)
  have eCx := (congrFst eM).eqTrans (fst_pair (Γ := Γ) (pairT C x) Q)
  refine Prf.eqCongr (wCore Ψ) fun i => ?_
  fin_cases i
  · exact .eqRefl _
  · exact fst_pair _ _
  · exact (congrFst s2).eqTrans (fst_pair _ _)
  · exact (congrFst s3).eqTrans (fst_pair _ _)
  · exact (congrFst eCx).eqTrans (fst_pair _ _)
  · exact (congrSnd eCx).eqTrans (snd_pair _ _)

/-- `4 Q_k² C ≤ R` for `k ≤ B` from `4 Q_B² C ≤ R`. -/
theorem r4_at {k K0 B C R : PTm n} (hk : Γ ⊢[PRAAx] le k B)
    (hR4 : Γ ⊢[PRAAx] le (num 4 * (pw two (K0 + B) * pw two (K0 + B)) * C) R) :
    Γ ⊢[PRAAx] le (num 4 * (Qk K0 k * Qk K0 k) * C) R := by
  have hm := pw_mono2 (K0 := K0) hk
  ipra_le sl hR4 + 4 * 𝔞 C * (𝔞 (pw two (K0 + B)) + 𝔞 (pw two (K0 + k))) * sl hm

/-- Exactness: `4 Q_k² C w_k = T t_k` once `4 Q_k² C ≤ R` (so that it divides `R!`). -/
theorem w_exact (Ψ : PTm 2) {K0 k R G C x : PTm n} (hC : Γ ⊢[PRAAx] le one C)
    (hR : Γ ⊢[PRAAx] le (num 4 * (Qk K0 k * Qk K0 k) * C) R) :
    Γ ⊢[PRAAx] num 4 * (Qk K0 k * Qk K0 k) * C * wval Ψ K0 k R G C x ≐ fact R * G * tval Ψ K0 k C x := by
  have hQ := one_le_pw (Γ := Γ) (K0 + k)
  have hd1 : Γ ⊢[PRAAx] le one (num 4 * (Qk K0 k * Qk K0 k) * C) := by
    ipra_le 4 * 𝔞 (Qk K0 k) * 𝔞 (Qk K0 k) * sl hC + 4 * 𝔞 (Qk K0 k) * sl hQ + 4 * sl hQ + 3
  have hd := pos_of_one hd1
  have dv := dvd_mul (tval Ψ K0 k C x) (dvd_mul G (dvd_fact (le_congr hd (.eqRefl R) hR)))
  have e := eq_of_dvd dv
  exact (congrMul hd (congrAp2 quoF (.eqRefl _) hd)).eqTrans e.eqSymm

/-- `hW` of `block_cover` at one scale. -/
theorem hW_pt (Ψ : PTm 2) {k K0 C x Q R G α γ b0 : PTm n} (hC : Γ ⊢[PRAAx] le one C)
    (hR : Γ ⊢[PRAAx] le (num 4 * (Qk K0 k * Qk K0 k) * C) R) :
    Γ ⊢[PRAAx] le (num 4 * (Qk K0 k * Qk K0 k) * inst2 (wbK Ψ) k (Xt K0 (pairT (pairT C x) Q) R G α γ b0))
      (fact R * G) :=
  le_congr (congrMul (.eqRefl _) (w_at Ψ k K0 C x Q R G α γ b0).eqSymm) (.eqRefl _)
    (hW_of_exact (pos_of_one hC) (w_exact (G := G) (x := x) Ψ hC hR) (mn_le_bound _ _))

/-- The capped dyadic mass of `KhinchinTailMass`, decoded. -/
theorem mb_at (Ψ : PTm 2) (k K0 C x : PTm n) :
    Γ ⊢[PRAAx] inst2 (MB (dyB Ψ)) k (pairT C (pairT K0 x)) ≐ tval Ψ K0 k C x := by
  rw [inst2_MB, inst2_dyB]
  have e1 : Γ ⊢[PRAAx] sndT (pairT C (pairT K0 x)) ≐ pairT K0 x := snd_pair _ _
  have eK := (congrFst e1).eqTrans (fst_pair (Γ := Γ) K0 x)
  have ex := (congrSnd e1).eqTrans (snd_pair (Γ := Γ) K0 x)
  have eC : Γ ⊢[PRAAx] fstT (pairT C (pairT K0 x)) ≐ C := fst_pair _ _
  have eQ := KhinchinBlockGeo.congrPw2 (congrAdd eK (.eqRefl k))
  have ea := congrMul eQ (congrInst2 Ψ eQ ex)
  exact congrMonus ea (congrMonus ea eC)

/-- The exactness identity in the form of `KhinchinWidths.hS_of_exact`. -/
theorem hex_pt (Ψ : PTm 2) {k K0 C x Q R G α γ b0 : PTm n} (hC : Γ ⊢[PRAAx] le one C)
    (hR : Γ ⊢[PRAAx] le (num 4 * (Qk K0 k * Qk K0 k) * C) R) :
    Γ ⊢[PRAAx] num 4 * C * inst2 (uB (wbK Ψ)) k (Xt K0 (pairT (pairT C x) Q) R G α γ b0) ≐
      fact R * G * inst2 (MB (dyB Ψ)) k (pairT C (pairT K0 x)) := by
  ipra_lc 4 * 𝔞 C * natEq (u_at (wbK Ψ) k K0 (pairT (pairT C x) Q) R G α γ b0) +
    4 * 𝔞 C * 𝔞 (Qk K0 k) * 𝔞 (Qk K0 k) * natEq (w_at Ψ k K0 C x Q R G α γ b0) +
    natEq (w_exact (G := G) (x := x) Ψ hC hR) - 𝔞 (fact R) * 𝔞 G * natEq (mb_at Ψ k K0 C x)

/-- Shifting a closed hypothesis under one binder. -/
theorem sh {φ : Fm PTm n} (ψ : Fm PTm (n + 1)) (h : Γ ⊢[PRAAx] φ) : (ψ :: Γ.map Fm.shift) ⊢[PRAAx] Fm.shift φ :=
  h.shift.wk

theorem shift_Xt (K0 C x Q R G α γ b0 : PTm n) :
    Syn.shift (Xt K0 (pairT (pairT C x) Q) R G α γ b0) =
      Xt (Syn.shift K0) (pairT (pairT (Syn.shift C) (Syn.shift x)) (Syn.shift Q)) (Syn.shift R) (Syn.shift G)
        (Syn.shift α) (Syn.shift γ) (Syn.shift b0) := by
  simp only [Xt, shift_pairT]

/-- `hS` of `block_cover`: the widths carry the grid, from (K-D) and monotonicity. -/
theorem hS_block (Ψ : PTm 2) {K0 B C x Q R G α γ b0 : PTm n} (hC : Γ ⊢[PRAAx] le one C)
    (hR4 : Γ ⊢[PRAAx] le (num 4 * (pw two (K0 + B) * pw two (K0 + B)) * C) R) (hmono : Γ ⊢[PRAAx] monoF Ψ x)
    (hD : Γ ⊢[PRAAx] le (C + ap2 (sumF Ψ) (pw two K0) x) (ap2 (sumF Ψ) (pw two (K0 + B)) x)) :
    Γ ⊢[PRAAx] le (fact R * G) (num 4 * ap2 (sumF (uB (wbK Ψ))) B (Xt K0 (pairT (pairT C x) Q) R G α γ b0)) := by
  have hblk : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (ap2 (sumF (offB Ψ)) (pw two (Syn.shift K0 + var 0)) (pairT (pw two (Syn.shift K0 + var 0)) (Syn.shift x)))
        (pw two (Syn.shift K0 + var 0) * inst2 Ψ (pw two (Syn.shift K0 + var 0)) (Syn.shift x))) := by
    refine .allI (.impI ?_)
    have hm := sh (lt (var 0) (Syn.shift B)) hmono
    rw [shift_monoF] at hm
    exact block_le Ψ _ _ hm
  refine hS_of_exact (uB (wbK Ψ)) (MB (dyB Ψ)) (pos_of_one hC) (.allI (.impI ?_)) (S_ge_one Ψ K0 B x hD hblk)
  have hC' : (lt (var 0) (Syn.shift B) :: Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift C) := by
    simpa [Fm.shift, Syn.shift] using sh (lt (var 0) (Syn.shift B)) hC
  have hR4' : (lt (var 0) (Syn.shift B) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (num 4 * (pw two (Syn.shift K0 + Syn.shift B) * pw two (Syn.shift K0 + Syn.shift B)) * Syn.shift C)
        (Syn.shift R) := by
    simpa [Fm.shift, Syn.shift] using sh (lt (var 0) (Syn.shift B)) hR4
  have h := hex_pt Ψ (k := var 0) (x := Syn.shift x) (Q := Syn.shift Q) (G := Syn.shift G) (α := Syn.shift α)
    (γ := Syn.shift γ) (b0 := Syn.shift b0) hC' (r4_at (le_of_lt Prf.hyp0) hR4')
  rw [shift_Xt, shift_pairT, shift_pairT,
    show Syn.shift (num 4 * C) = num 4 * Syn.shift C by simp [Syn.shift],
    show Syn.shift (fact R * G) = fact (Syn.shift R) * Syn.shift G by simp [Syn.shift]]
  exact h

theorem le_pairT_right {a b : PTm n} (h : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx] le b (pairT a b) := by
  show Γ ⊢[PRAAx] le b ((a + b) * (a + b) + a)
  ipra_le (𝔞 a + 𝔞 b) * (𝔞 a + sl h) + 2 * 𝔞 a

/-! ## One cell -/

/-- The conclusion of `block_cover` for the cell `g < G = p + 1` (block on `J* = ((4g+1)/4G, (4g+3)/4G)`), with
every hypothesis of `block_cover` discharged from `ψ`, (K-D) and the grid bounds. -/
theorem cell_cover (Ψ : PTm 2) {g p K0 B C x Q R G : PTm n}
    (hg : Γ ⊢[PRAAx] lt g (succ p)) (hC : Γ ⊢[PRAAx] le one C) (hmono : Γ ⊢[PRAAx] monoF Ψ x)
    (hD : Γ ⊢[PRAAx] le (C + ap2 (sumF Ψ) (pw two K0) x) (ap2 (sumF Ψ) (pw two (K0 + B)) x))
    (hK : Γ ⊢[PRAAx] le (num 512 * succ p) K0) (hQ : Γ ⊢[PRAAx] le (pw two (K0 + B)) Q)
    (hR4 : Γ ⊢[PRAAx] le (num 4 * (pw two (K0 + B) * pw two (K0 + B)) * C) R)
    (hRG : Γ ⊢[PRAAx] le (R * R) G) :
    Γ ⊢[PRAAx] le (monus (γc g) (αc g) * (fact R * G))
      (num 8192 * succ (b0c p) * ap2 (sumF (sg (oB (bB (wbK Ψ))))) (fact R * G * pairT (pairT C x) Q)
        (pairT B (Xt K0 (pairT (pairT C x) Q) R G (αc g) (γc g) (b0c p)))) := by
  have hQb := one_le_pw (Γ := Γ) (K0 + B)
  have hQ1 := le_trans hQb hQ
  have hM : Γ ⊢[PRAAx] le (pw two (K0 + B)) (pairT (pairT C x) Q) := le_trans hQ (le_pairT_right hQ1)
  have hQR : Γ ⊢[PRAAx] le (pw two (K0 + B)) R := by
    ipra_le sl hR4 + 𝔞 (pw two (K0 + B)) * (4 * 𝔞 (pw two (K0 + B)) * sl hC + 4 * sl hQb + 3)
  have hR1 := le_trans hQb hQR
  have hG1 : Γ ⊢[PRAAx] le one G := by ipra_le sl hRG + 𝔞 R * sl hR1 + sl hR1
  have e := natEq (cell_gap (Γ := Γ) g)
  have hK4 : Γ ⊢[PRAAx] le (num 256 * succ (b0c p)) (monus (γc g) (αc g) * K0) := by
    ipra_le 2 * sl hK with 𝔞 K0 * e
  refine block_cover (wbK Ψ) (cell_hag g) (cell_hg hg) (cell_hD g) (pos_of_one (le_trans hQb hM))
    (pos_of_one hG1) hM hQR hK4 hRG (.allI (.impI ?_)) (hS_block Ψ hC hR4 hmono hD)
  have hC' : (lt (var 0) (Syn.shift B) :: Γ.map Fm.shift) ⊢[PRAAx] le one (Syn.shift C) := by
    simpa [Fm.shift, Syn.shift] using sh (lt (var 0) (Syn.shift B)) hC
  have hR4' : (lt (var 0) (Syn.shift B) :: Γ.map Fm.shift) ⊢[PRAAx]
      le (num 4 * (pw two (Syn.shift K0 + Syn.shift B) * pw two (Syn.shift K0 + Syn.shift B)) * Syn.shift C)
        (Syn.shift R) := by
    simpa [Fm.shift, Syn.shift] using sh (lt (var 0) (Syn.shift B)) hR4
  rw [shift_Xt, show Syn.shift (fact R * G) = fact (Syn.shift R) * Syn.shift G by simp [Syn.shift]]
  exact hW_pt Ψ hC' (r4_at (le_of_lt Prf.hyp0) hR4')

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinK2Widths
