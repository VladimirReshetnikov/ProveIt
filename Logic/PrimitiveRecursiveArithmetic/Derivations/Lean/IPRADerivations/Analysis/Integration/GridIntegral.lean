import IPRADerivations.Analysis.Integration.RiemannRefinement
import IPRADerivations.Foundations.AuxiliaryEnvelope
import IPRADerivations.Core.BlockSum

/-!
# The finite-grid integral under a uniform continuity modulus

Packet: `foundations/ipra_framework`, `paper/sections/04_analytic_tools.tex`, Theorem `thm:integral`
("Finite-grid integral"), dimension `d = 1`. The integral name is `S_k = 2^{-m_k} ∑_{i < 2^{m_k}} f(i 2^{-m_k})`
with `m_k = μ(k + 3)`. For `k ≤ l` the fine grid of level `m_l` refines the coarse grid of level `m_k`: with
`N = 2^{m_k}` coarse cells and `R = 2^{m_l − m_k}` fine points per cell, the fine point `i` lies in the coarse
cell `⌊i/R⌋`, and the modulus `eq:uc` together with the two evaluation errors bounds the difference of the two
samples by `e = 3 · 2^{-k-3}`. "The weights are nonnegative and sum to one. Taking their finite weighted sum
bounds the difference by the sum of those three errors."

Cleared form, for a fine body `F(i, x)` (the fine samples) and a coarse body `C(c, x)` (the coarse samples):

* `CellUp`: `F(i) ≤ C(⌊i/R⌋) + e` for `i < N R`; `CellDn`: `C(⌊i/R⌋) ≤ F(i) + e`;
* `cell_up`, `cell_dn`: one coarse cell, `∑_{j<R} F(c R + j) ≤ R (C(c) + e)` and
  `R C(c) ≤ ∑_{j<R} F(c R + j) + R e` (the fine index `c R + j` lies in the cell `c` by `BlockSum.qr_block`);
* `grid_upper`, `grid_lower`: `∑_{i<NR} F(i) ≤ R ∑_{c<N} C(c) + N R e` and
  `R ∑_{c<N} C(c) ≤ ∑_{i<NR} F(i) + N R e`, by induction on the number of coarse cells.

Dividing by `N R`: `|S_l − S_k| ≤ e`. The grids of dimension `d ≥ 2`, the modulus and evaluation contracts that
produce `e`, and the passage to a regular name are not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GridIntegral

open_ipra
open LeanProofs.IPRA.Analysis.RiemannRefinement (fine_succ fine_zero shift_le')
open LeanProofs.IPRA.Foundations.AuxiliaryEnvelope (sum_le_const)
open LeanProofs.IPRA.BlockSum (qr_block)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The cell hypotheses -/

/-- `F(i, x) ≤ C(⌊i/R⌋, x) + e` for `i < N R`. -/
def CellUp (F C : PTm 2) (x N R e : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N * Syn.shift R) ⟶
    le (inst2 F (var 0) (Syn.shift x)) (inst2 C (quo (var 0) (Syn.shift R)) (Syn.shift x) + Syn.shift e))

/-- `C(⌊i/R⌋, x) ≤ F(i, x) + e` for `i < N R`. -/
def CellDn (F C : PTm 2) (x N R e : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift N * Syn.shift R) ⟶
    le (inst2 C (quo (var 0) (Syn.shift R)) (Syn.shift x)) (inst2 F (var 0) (Syn.shift x) + Syn.shift e))

theorem subst_CellUp {m : ℕ} (σ : Fin n → PTm m) (F C : PTm 2) (x N R e : PTm n) :
    (CellUp F C x N R e).subst σ =
      CellUp F C (Syn.subst σ x) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ e) := by
  simp only [CellUp, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_ap2, PTm.subst_add,
    PTm.subst_mul, Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

theorem subst_CellDn {m : ℕ} (σ : Fin n → PTm m) (F C : PTm 2) (x N R e : PTm n) :
    (CellDn F C x N R e).subst σ =
      CellDn F C (Syn.subst σ x) (Syn.subst σ N) (Syn.subst σ R) (Syn.subst σ e) := by
  simp only [CellDn, Fm.subst_all, Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_ap2, PTm.subst_add,
    PTm.subst_mul, Syn.subst_var, Syn.up_zero, Syn.subst_shift, Syn.shift_subst, Syn.up_succ]

/-- The hypothesis at a fine index. -/
theorem up_at {F C : PTm 2} {x N R e t : PTm n} (h : Γ ⊢[PRAAx] CellUp F C x N R e)
    (ht : Γ ⊢[PRAAx] lt t (N * R)) : Γ ⊢[PRAAx] le (inst2 F t x) (inst2 C (quo t R) x + e) := by
  have a := Prf.allE t h
  simp only [CellUp, Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_ap2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact Prf.impE a ht

theorem dn_at {F C : PTm 2} {x N R e t : PTm n} (h : Γ ⊢[PRAAx] CellDn F C x N R e)
    (ht : Γ ⊢[PRAAx] lt t (N * R)) : Γ ⊢[PRAAx] le (inst2 C (quo t R) x) (inst2 F t x + e) := by
  have a := Prf.allE t h
  simp only [CellDn, Fm.subst_imp, subst_lt, subst_le, subst_inst2, subst_ap2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  exact Prf.impE a ht

/-- The fine index `c R + j` of a cell lies below `N R`. -/
theorem fine_lt {c j N R : PTm n} (hc : Γ ⊢[PRAAx] lt c N) (hj : Γ ⊢[PRAAx] lt j R) :
    Γ ⊢[PRAAx] lt (c * R + j) (N * R) := by
  unfold lt at hc hj ⊢
  ipra_le 𝔟 R * sl hc + sl hj

/-- The `j`-th fine sample of the cell at `c R`, read through the offset body. -/
theorem off_at (F : PTm 2) (c R j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (offB F) j (pairT (c * R) x) ≐ inst2 F (c * R + j) x := by
  rw [inst2_offB]
  exact congrInst2 F (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-! ## One cell -/

/-- `∑_{j<R} F(c R + j) ≤ R (C(c) + e)`. -/
theorem cell_up {F C : PTm 2} {x N R e c : PTm n} (h : Γ ⊢[PRAAx] CellUp F C x N R e)
    (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) (hc : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] le (ap2 (sumF (offB F)) R (pairT (c * R) x)) (R * (inst2 C c x + e)) := by
  refine sum_le_const (offB F) (.allI (.impI ?_))
  have h' : (lt (var 0) (Syn.shift R) :: Γ.map Fm.shift) ⊢[PRAAx]
      CellUp F C (Syn.shift x) (Syn.shift N) (Syn.shift R) (Syn.shift e) := by
    have a := h.shift
    rw [Fm.shift, subst_CellUp] at a
    exact a.wk
  have hj : (lt (var 0) (Syn.shift R) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift R) := Prf.hyp0
  have hc' : (lt (var 0) (Syn.shift R) :: Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift c) (Syn.shift N) := by
    have a := hc.shift
    simp only [Fm.shift, subst_lt] at a
    exact a.wk
  have hR' : (lt (var 0) (Syn.shift R) :: Γ.map Fm.shift) ⊢[PRAAx]
      Syn.shift R ≐ succ (pred (Syn.shift R)) := by
    have a := hR.shift
    simp only [Fm.shift, Fm.subst_eq] at a
    simpa [Syn.shift] using a.wk
  have s := up_at h' (fine_lt hc' hj)
  have q := Prf.andE₁ (qr_block (i := Syn.shift c) hR' hj)
  have e1 : Syn.shift (pairT (c * R) x) = pairT (Syn.shift c * Syn.shift R) (Syn.shift x) := by
    simp [Syn.shift]
  have e2 : Syn.shift (inst2 C c x + e) = inst2 C (Syn.shift c) (Syn.shift x) + Syn.shift e := by
    simp only [Syn.shift, PTm.subst_add, subst_inst2]
  rw [e1, e2]
  exact le_congr (off_at F _ _ _ _).eqSymm (congrAdd (congrInst2 C q (.eqRefl _)) (.eqRefl _)) s

/-- The lower bound of one cell, `j C(c) ≤ ∑_{i<j} F(c R + i) + j e`, by induction on `j ≤ R`. -/
abbrev DnInv (F C : PTm 2) (c R x e j : PTm n) : Fm PTm n :=
  le (j * inst2 C c x) (ap2 (sumF (offB F)) j (pairT (c * R) x) + j * e)

/-- `R C(c) ≤ ∑_{j<R} F(c R + j) + R e`. -/
theorem cell_dn {F C : PTm 2} {x N R e c : PTm n} (h : Γ ⊢[PRAAx] CellDn F C x N R e)
    (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) (hc : Γ ⊢[PRAAx] lt c N) :
    Γ ⊢[PRAAx] DnInv F C c R x e R := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift R) ⟶
      DnInv F C (Syn.shift c) (Syn.shift R) (Syn.shift x) (Syn.shift e) (var 0)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT, subst_inst2]
    · refine .impI ?_
      have z := natEq (sum_zero (Γ := le zero R :: Γ) (offB F) (pairT (c * R) x))
      ipra_le 0 using rw [z]; ring
    · refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift R) ::
          (le (var 0) (Syn.shift R) ⟶
            DnInv F C (Syn.shift c) (Syn.shift R) (Syn.shift x) (Syn.shift e) (var 0)) :: Γ.map Fm.shift
      have hk : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift R) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] DnInv F C (Syn.shift c) (Syn.shift R) (Syn.shift x) (Syn.shift e) (var 0) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have h' : Δ ⊢[PRAAx] CellDn F C (Syn.shift x) (Syn.shift N) (Syn.shift R) (Syn.shift e) := by
        have a := h.shift
        rw [Fm.shift, subst_CellDn] at a
        exact a.wk.wk
      have hc' : Δ ⊢[PRAAx] lt (Syn.shift c) (Syn.shift N) := by
        have a := hc.shift
        simp only [Fm.shift, subst_lt] at a
        exact a.wk.wk
      have hR' : Δ ⊢[PRAAx] Syn.shift R ≐ succ (pred (Syn.shift R)) := by
        have a := hR.shift
        simp only [Fm.shift, Fm.subst_eq] at a
        simpa [Syn.shift] using a.wk.wk
      have hj : Δ ⊢[PRAAx] lt (var 0) (Syn.shift R) := hk
      have s := dn_at h' (fine_lt hc' hj)
      have q := natEq (congrInst2 C (Prf.andE₁ (qr_block (i := Syn.shift c) hR' hj)) (.eqRefl (Syn.shift x)))
      have eS := natEq (sum_succ' (Γ := Δ) (offB F) (var 0) (pairT (Syn.shift c * Syn.shift R) (Syn.shift x)))
      have eO := natEq (off_at (Γ := Δ) F (Syn.shift c) (Syn.shift R) (var 0) (Syn.shift x))
      ipra_le sl ih + sl s using rw [eS, eO]; linear_combination q
  have h2 := Prf.allE R hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, subst_pairT, subst_inst2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact .impE h2 (le_refl R)

/-! ## All cells -/

/-- `∑_{i < k R} F(i) ≤ R ∑_{c<k} C(c) + k R e`. -/
abbrev UpInv (F C : PTm 2) (x R e k : PTm n) : Fm PTm n :=
  le (ap2 (sumF F) (k * R) x) (R * ap2 (sumF C) k x + k * R * e)

/-- `R ∑_{c<k} C(c) ≤ ∑_{i < k R} F(i) + k R e`. -/
abbrev LoInv (F C : PTm 2) (x R e k : PTm n) : Fm PTm n :=
  le (R * ap2 (sumF C) k x) (ap2 (sumF F) (k * R) x + k * R * e)

/-- `thm:integral` (`d = 1`), upper half: `∑_{i<NR} F(i) ≤ R ∑_{c<N} C(c) + N R e`. -/
theorem grid_upper {F C : PTm 2} {x N R e : PTm n} (h : Γ ⊢[PRAAx] CellUp F C x N R e)
    (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) : Γ ⊢[PRAAx] UpInv F C x R e N := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      UpInv F C (Syn.shift x) (Syn.shift R) (Syn.shift e) (var 0)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
    · refine .impI ?_
      have z1 := natEq (fine_zero (Γ := le zero N :: Γ) F R x)
      have z2 := natEq (sum_zero (Γ := le zero N :: Γ) C x)
      ipra_le 0 using rw [z1, z2]; ring
    · refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ UpInv F C (Syn.shift x) (Syn.shift R) (Syn.shift e) (var 0)) ::
          Γ.map Fm.shift
      have hk : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] UpInv F C (Syn.shift x) (Syn.shift R) (Syn.shift e) (var 0) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have h' : Δ ⊢[PRAAx] CellUp F C (Syn.shift x) (Syn.shift N) (Syn.shift R) (Syn.shift e) := by
        have a := h.shift
        rw [Fm.shift, subst_CellUp] at a
        exact a.wk.wk
      have hR' : Δ ⊢[PRAAx] Syn.shift R ≐ succ (pred (Syn.shift R)) := by
        have a := hR.shift
        simp only [Fm.shift, Fm.subst_eq] at a
        simpa [Syn.shift] using a.wk.wk
      have c := cell_up h' hR' (c := var 0) hk
      have eS := natEq (fine_succ (Γ := Δ) F (var 0) (Syn.shift R) (Syn.shift x))
      have eC := natEq (sum_succ' (Γ := Δ) C (var 0) (Syn.shift x))
      ipra_le sl ih + sl c using rw [eS, eC]; ring
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact .impE h2 (le_refl N)

/-- `thm:integral` (`d = 1`), lower half: `R ∑_{c<N} C(c) ≤ ∑_{i<NR} F(i) + N R e`. -/
theorem grid_lower {F C : PTm 2} {x N R e : PTm n} (h : Γ ⊢[PRAAx] CellDn F C x N R e)
    (hR : Γ ⊢[PRAAx] R ≐ succ (pred R)) : Γ ⊢[PRAAx] LoInv F C x R e N := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      LoInv F C (Syn.shift x) (Syn.shift R) (Syn.shift e) (var 0)) := by
    ipra_qfind (⟨le_QF _ _, le_QF _ _⟩) [subst_le, subst_ap2]
    · refine .impI ?_
      have z1 := natEq (fine_zero (Γ := le zero N :: Γ) F R x)
      have z2 := natEq (sum_zero (Γ := le zero N :: Γ) C x)
      ipra_le 0 using rw [z1, z2]; ring
    · refine .impI ?_
      let Δ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
          (le (var 0) (Syn.shift N) ⟶ LoInv F C (Syn.shift x) (Syn.shift R) (Syn.shift e) (var 0)) ::
          Γ.map Fm.shift
      have hk : Δ ⊢[PRAAx] le (succ (var 0)) (Syn.shift N) := Prf.hyp0
      have ih : Δ ⊢[PRAAx] LoInv F C (Syn.shift x) (Syn.shift R) (Syn.shift e) (var 0) :=
        Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk)
      have h' : Δ ⊢[PRAAx] CellDn F C (Syn.shift x) (Syn.shift N) (Syn.shift R) (Syn.shift e) := by
        have a := h.shift
        rw [Fm.shift, subst_CellDn] at a
        exact a.wk.wk
      have hR' : Δ ⊢[PRAAx] Syn.shift R ≐ succ (pred (Syn.shift R)) := by
        have a := hR.shift
        simp only [Fm.shift, Fm.subst_eq] at a
        simpa [Syn.shift] using a.wk.wk
      have c := cell_dn h' hR' (c := var 0) hk
      have eS := natEq (fine_succ (Γ := Δ) F (var 0) (Syn.shift R) (Syn.shift x))
      have eC := natEq (sum_succ' (Γ := Δ) C (var 0) (Syn.shift x))
      ipra_le sl ih + sl c using rw [eS, eC]; ring
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, PTm.subst_add, PTm.subst_mul, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at h2
  exact .impE h2 (le_refl N)

end LeanProofs.IPRA.Analysis.GridIntegral
