import IPRADerivations.AnalyticNumberTheory.PhiUpper

/-!
# Bell numbers by course-of-values recursion

Packet: `combinatorics/bell_numbers_ipra`, Theorem `thm:spivey`, equation `eq:bell-binomial`:
`B_{n+1} = ∑_{k=0}^{n} C(n, k) B_k`, `B_0 = 1`.

The Bell numbers are defined by primitive recursion on the coded list
`L_n = ⟨B_n, ⟨B_{n−1}, … ⟨B_0, 0⟩⟩⟩` (Cantor pairs): `L_{n+1} = ⟨∑_{k≤n} C(n,k) · nth(L_n, n − k), L_n⟩`,
with `nth(L, j) = fst(snd^j L)`.

* `nth_pair_zero`, `nth_pair_succ`: reading a consed list;
* `nth_BL`: `nth(L_n, j) = B_{n−j}` for `j ≤ n`, by induction on `n` of the quantifier-free
  statement that the violation count over `j ≤ n` vanishes (`BoundedSums`/`sum_shift`);
* `bell_rec`: the recurrence.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Bell

open_ipra
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrBinom)
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Lists of pairs -/

/-- `snd^j L`, by recursion on `j` with parameter `L`. -/
abbrev iS : PR 2 := rec2 (var 0) (sndT (var 1))

theorem iS_zero (L : PTm n) : Γ ⊢[PRAAx] ap2 iS zero L ≐ L := by
  have h := rec2_zero (Γ := Γ) (var 0) (sndT (var 1)) L
  simpa using h

theorem iS_succ (j L : PTm n) : Γ ⊢[PRAAx] ap2 iS (succ j) L ≐ sndT (ap2 iS j L) := by
  have h := rec2_succ (Γ := Γ) (var 0) (sndT (var 1)) j L
  simpa using h

/-- `nth(L, j) = fst(snd^j L)`. -/
abbrev nth (L j : PTm n) : PTm n := fstT (ap2 iS j L)

/-- Variables: `0 = j`, `1 = a`, `2 = L`. -/
private abbrev iSPairF : Fm PTm 3 := ap2 iS (succ (var 0)) (pairT (var 1) (var 2)) ≐ ap2 iS (var 0) (var 2)

private theorem iS_pair₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] iSPairF := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact (iS_succ _ _).eqTrans ((congrSnd (iS_zero _)).eqTrans ((snd_pair _ _).eqTrans (iS_zero _).eqSymm))
  · exact (iS_succ _ _).eqTrans ((congrSnd Prf.hyp0).eqTrans (iS_succ _ _).eqSymm)

theorem iS_pair (j a L : PTm n) : Γ ⊢[PRAAx] ap2 iS (succ j) (pairT a L) ≐ ap2 iS j L := by
  have h := inst (Γ := Γ) iS_pair₀ (![j, a, L] : Fin 3 → PTm n)
  simpa using h

theorem nth_pair_zero (a L : PTm n) : Γ ⊢[PRAAx] nth (pairT a L) zero ≐ a :=
  (iS_zero _).fstE

theorem nth_pair_succ (a L j : PTm n) : Γ ⊢[PRAAx] nth (pairT a L) (succ j) ≐ nth L j :=
  congrFst (iS_pair _ _ _)

/-! ## The Bell list -/

/-- `C(n, k) · nth(L, n − k)`, over `0 = k`, `1 = ⟨n, L⟩`. -/
abbrev bB : PTm 2 := binom (fstT (var 1)) (var 0) * nth (sndT (var 1)) (monus (fstT (var 1)) (var 0))

/-- The step `⟨n, L⟩ ↦ ⟨∑_{k≤n} C(n,k) nth(L, n − k), L⟩`, over `0 = n`, `1 = L`. -/
abbrev stepB : PTm 2 := pairT (ap2 (sumF bB) (succ (var 0)) (pairT (var 0) (var 1))) (var 1)

abbrev BL : PR 1 := rec1 (pairT one zero) stepB

/-- The Bell number `B_n`. -/
abbrev bell (N : PTm n) : PTm n := fstT (ap1 BL N)

theorem BL_zero : Γ ⊢[PRAAx] ap1 BL (zero : PTm n) ≐ pairT one zero := by
  have h := rec1_zero (Γ := Γ) (pairT one zero) stepB
  simpa using h

theorem BL_succ (N : PTm n) :
    Γ ⊢[PRAAx] ap1 BL (succ N) ≐ pairT (ap2 (sumF bB) (succ N) (pairT N (ap1 BL N))) (ap1 BL N) := by
  have h := rec1_succ (Γ := Γ) (pairT one zero) stepB N
  simpa using h

theorem bell_zero : Γ ⊢[PRAAx] bell (zero : PTm n) ≐ one := BL_zero.fstE

/-! ## Reading the list: `nth(L_n, j) = B_{n−j}` -/

/-- `1 ∸ [nth(L_n, j) = B_{n−j}]`, over `0 = j`, `1 = n`. -/
abbrev violB : PTm 2 := monus one (eqb (nth (ap1 BL (var 1)) (var 0)) (bell (monus (var 1) (var 0))))

theorem inst2_viol (j N : PTm n) :
    inst2 violB j N = monus one (eqb (nth (ap1 BL N) j) (bell (monus N j))) := by simp [inst2]

theorem viol_zero_term (N : PTm n) : Γ ⊢[PRAAx] inst2 violB zero N ≐ zero := by
  rw [inst2_viol]
  exact viol_of_eq ((congrFst (iS_zero _)).eqTrans (congrFst (congrAp1 BL (monus_zero _))).eqSymm)

theorem viol_shift (j N : PTm n) : Γ ⊢[PRAAx] inst2 violB (succ j) (succ N) ≐ inst2 violB j N := by
  rw [inst2_viol, inst2_viol]
  refine congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb ?_ ?_)
  · exact (congrFst (congrAp2 iS (.eqRefl _) (BL_succ N))).eqTrans (nth_pair_succ _ _ _)
  · exact congrFst (congrAp1 BL (succ_monus_succ _ _))

private abbrev violF : Fm PTm 1 := ap2 (sumF violB) (succ (var 0)) (var 0) ≐ zero

private theorem viol₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] violF := by
  ipra_ind [subst_ap2]
  · exact (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (viol_zero_term _)).eqTrans (add_zero _))
  · refine (sum_shift _ _ _).eqTrans ((congrAdd (viol_zero_term _) ?_).eqTrans (zero_add _))
    refine (sum_congr_bounded (shiftBody violB) violB (succ (var 0)) (var 0) (succ (var 0)) (.allI (.impI ?_))).eqTrans
      Prf.hyp0
    rw [inst2_shiftBody]
    have e : Syn.shift (succ (var 0 : PTm 1)) = succ (Syn.shift (var 0)) := by simp [Syn.shift]
    rw [e]
    exact viol_shift _ _

alias monus_monus := Common.monus_monus_of_le

theorem monus_le' {v N : PTm n} (h : Γ ⊢[PRAAx] le v N) : Γ ⊢[PRAAx] le (monus N v) N :=
  le_of_eq_add (d := v) ((eq_add_of_le h).eqTrans (add_comm _ _))

/-- `nth(L_n, j) = B_{n−j}` for `j ≤ n`. -/
theorem nth_BL {j N : PTm n} (h : Γ ⊢[PRAAx] le j N) : Γ ⊢[PRAAx] nth (ap1 BL N) j ≐ bell (monus N j) := by
  have v := inst (Γ := Γ) viol₀ (![N] : Fin 1 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at v
  have z := sum_zero_elim violB v ((succ_monus_succ _ _).eqTrans h)
  rw [inst2_viol] at z
  exact eq_of_viol z

/-! ## The recurrence -/

/-- `C(n, k) B_k`, over `0 = k`, `1 = n`. -/
abbrev recB : PTm 2 := binom (var 1) (var 0) * bell (var 0)

theorem inst2_rec (k N : PTm n) : inst2 recB k N = binom N k * bell k := by simp [inst2]

theorem inst2_bB (k x : PTm n) : inst2 bB k x = binom (fstT x) k * nth (sndT x) (monus (fstT x) k) := by
  simp [inst2]

/-- `eq:bell-binomial` at an arbitrary `n`: `B_{n+1} = ∑_{k ≤ n} C(n, k) B_k`. -/
theorem bell_succ (N : PTm n) : Γ ⊢[PRAAx] bell (succ N) ≐ ap2 (sumF recB) (succ N) N := by
  refine (congrFst (BL_succ N)).eqTrans ((fst_pair _ _).eqTrans ?_)
  refine sum_congr_bounded bB recB (pairT N (ap1 BL N)) N (succ N) (.allI (.impI ?_))
  have e₁ : Syn.shift (pairT N (ap1 BL N)) = pairT (Syn.shift N) (ap1 BL (Syn.shift N)) := by simp [Syn.shift]
  have e₂ : Syn.shift (succ N) = succ (Syn.shift N) := by simp [Syn.shift]
  rw [inst2_bB, inst2_rec, e₁]
  rw [e₂] at *
  have hv : (lt (var 0) (succ (Syn.shift N)) :: Γ.map Fm.shift) ⊢[PRAAx] le (var 0) (Syn.shift N) :=
    (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
  refine congrMul (congrBinom (fst_pair _ _) (.eqRefl _)) ?_
  refine (congrFst (congrAp2 iS (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _))).eqTrans ?_
  exact (nth_BL (monus_le' hv)).eqTrans (congrFst (congrAp1 BL (monus_monus hv)))

/-- `eq:bell-binomial`: `B_{n+1} = ∑_{k=0}^{n} C(n, k) B_k`. -/
abbrev bellRecFormula : Fm PTm 1 := bell (succ (var 0)) ≐ ap2 (sumF recB) (succ (var 0)) (var 0)

theorem bell_rec : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 1 bellRecFormula :=
  closeUniv 1 (bell_succ (var 0))

end LeanProofs.IPRA.Combinatorics.Bell
