import IPRADerivations.AnalyticNumberTheory.PowerResidueBackward

/-!
# The progression-row growth equivalence (`riemann_ipra_prime_criteria_2026-11-20`, `thm:powerdivisor`)

Packet: `analytic-number-theory/riemann_ipra_prime_criteria_2026-11-20`, `new-growth.tex`, Theorem `thm:powerdivisor`:
"For each of the four families the growth statement is equivalent to the statement for `B_h` … This includes
uniformity over all reduced progressions when that row is used." The progression constant precedes `q, b`.

A residue pair is a code `p` with `p = ⟨fst p, snd p⟩`, `q = fst p ≥ 2`, `b = snd p < q` and `gcd(b, q) = 1` (`OkI`).
The progression growth sentence for signed sequence bodies `s^±` and parameter `z` is
`∀k ∃c ∀p (p reduced → ∀N |S_p(N)|^{2(k+1)} ≤ c N^{k+2})` (`GrowthP`, built from the matrix `AF`), where `S_p(N)` is
evaluated at `⟨p, z⟩`:

* `GrowthP (AB (mask a⁺)) (AB (mask a⁻)) y` is the residue-uniform growth of `A_{q,b}(N) = Σ_{m≤N, m≡b} a(m)`;
* `GrowthP (AB (mask (bvB a⁺))) (AB (mask (bvB a⁻))) ⟨h, y⟩` is that of `B_{h;q,b}(N) = Σ_{m≤N, m≡b} b_h(m)`;
* `growth_res_iff`: the two are equivalent in object iPRA for every `h ≥ 2`, with the packet's witness
  `C_r(c) = (c+1)(8r)^{2r}` in both directions (`PowerResidueForward.forward_res_core`,
  `PowerResidueBackward.backward_res_core`).
-/

namespace LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueGrowth

open_ipra exports
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueForward (InR subst_InA forward_res_core)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueBackward (backward_res_core)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueRows (mask bvB Xp MB)
open LeanProofs.IPRA.AnalyticNumberTheory.PowerDivisorGrowth (InA Mat subst_Mat AB inst2_AB Cout exps allE_shift
  subst_cons_shift two_le_shift subst_sh all_ex_imp_at)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Residue codes and the sentences -/

/-- `p` codes a reduced residue pair: `p = ⟨q, b⟩`, `q ≥ 2`, `b < q`, `gcd(b, q) = 1`. -/
abbrev OkI (p : PTm n) (φ : Fm PTm n) : Fm PTm n :=
  (p ≐ pairT (fstT p) (sndT p)) ⟶ le two (fstT p) ⟶ lt (sndT p) (fstT p) ⟶ (gcd (sndT p) (fstT p) ≐ one) ⟶ φ

theorem subst_OkI {m : ℕ} (σ : Fin n → PTm m) (p : PTm n) (φ : Fm PTm n) :
    (OkI p φ).subst σ = OkI (Syn.subst σ p) (φ.subst σ) := by
  simp only [OkI, Fm.subst_imp, lt, subst_le, Fm.subst_eq, subst_ex2, subst_fstT, subst_sndT, subst_pairT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem up2_v0' {m k : ℕ} (σ : Fin m → PTm k) : Syn.subst (up (up σ)) (var 0 : PTm (m + 2)) = var 0 := rfl
theorem up2_v1' {m k : ℕ} (σ : Fin m → PTm k) : Syn.subst (up (up σ)) (var 1 : PTm (m + 2)) = var 1 := rfl
theorem up1_v0' {m k : ℕ} (σ : Fin m → PTm k) : Syn.subst (up σ) (var 0 : PTm (m + 1)) = var 0 := rfl
theorem up1_v1' {m k : ℕ} (σ : Fin (m + 1) → PTm k) : Syn.subst (up σ) (var 1 : PTm (m + 2)) = Syn.shift (σ 0) := rfl

/-- The matrix `∀p (p reduced → ∀N |S_p(N)|^{2(K+1)} ≤ C N^{K+2})` at the parameter `⟨p, X⟩`. -/
def AF (sP sN : PTm 2) (X K C : PTm n) : Fm PTm n :=
  Fm.all (OkI (var 0) (Fm.all (Mat sP sN (pairT (var 1) (Syn.shift (Syn.shift X))) (Syn.shift (Syn.shift K))
    (Syn.shift (Syn.shift C)) (var 0))))

theorem subst_AF {m : ℕ} (σ : Fin n → PTm m) (sP sN : PTm 2) (X K C : PTm n) :
    (AF sP sN X K C).subst σ = AF sP sN (Syn.subst σ X) (Syn.subst σ K) (Syn.subst σ C) := by
  simp only [AF, Fm.subst_all, subst_OkI, subst_Mat, subst_pairT, up2_v1', up1_v0', up2_v0', subst_up_shift_pal]

theorem shift_AF (sP sN : PTm 2) (X K C : PTm n) :
    Fm.shift (AF sP sN X K C) = AF sP sN (Syn.shift X) (Syn.shift K) (Syn.shift C) := by
  simp only [Fm.shift, subst_AF, subst_sh]

/-- The progression growth sentence `∀k ∃c ∀p (p reduced → ∀N |S_p(N)|^{2(k+1)} ≤ c N^{k+2})`. -/
abbrev GrowthP (sP sN : PTm 2) (z : PTm n) : Fm PTm n :=
  Fm.all (Fm.ex (AF sP sN (Syn.shift (Syn.shift z)) (var 1) (var 0)))

variable (aP aN : PTm 2)

/-! ## From the matrix to the residue-uniform input bound -/

/-- `∀N |S(N)|^{2(K+1)} ≤ C N^{K+2}` at `K = 2k + 1` is the input bound `InA` at `r = k + 1`. -/
theorem mat_inA {y k c : PTm n}
    (hA : Γ ⊢[PRAAx] Fm.all (Mat (AB aP) (AB aN) (Syn.shift y) (Syn.shift (succ (two * k))) (Syn.shift c) (var 0))) :
    Γ ⊢[PRAAx] InA aP aN y (succ k) c := by
  refine .allI ?_
  have b := hA.allOpen
  simp only [Mat, inst2_AB] at b
  rw [show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
  rw [show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
  have ex := exps (Γ := Γ.map Fm.shift) (Syn.shift k)
  exact le_congr (congrPw (.eqRefl _) ex.1) (congrMul (.eqRefl _) (congrPw (.eqRefl _) ex.2)) b

/-- The matrix at `K = 2k + 1` gives the bound uniform over the reduced residues modulo `q ≥ 2`. -/
theorem toInR {y k c q : PTm n} (hq : Γ ⊢[PRAAx] le two q)
    (H : Γ ⊢[PRAAx] AF (AB (mask aP)) (AB (mask aN)) y (succ (two * k)) c) :
    Γ ⊢[PRAAx] InR aP aN q y (succ k) c := by
  have hq' : (Γ.map Fm.shift) ⊢[PRAAx] le two (Syn.shift q) := two_le_shift hq
  have b := allE_shift H (pairT (Syn.shift q) (var 0))
  simp only [subst_OkI, Fm.subst_all, subst_Mat, subst_pairT, Syn.subst_var, Fin.cases_zero, subst_cons_shift,
    subst_up_shift_pal, up1_v0', up1_v1'] at b
  refine .allI (.impI (.impI ?_))
  let Δ : List (Fm PTm (n + 1)) := (gcd (var 0) (Syn.shift q) ≐ one) :: lt (var 0) (Syn.shift q) :: Γ.map Fm.shift
  have e0 : Δ ⊢[PRAAx] pairT (Syn.shift q) (var 0) ≐
      pairT (fstT (pairT (Syn.shift q) (var 0))) (sndT (pairT (Syn.shift q) (var 0))) :=
    (congrPairT (fst_pair _ _) (snd_pair _ _)).eqSymm
  have e1 : Δ ⊢[PRAAx] le two (fstT (pairT (Syn.shift q) (var 0))) :=
    le_congr (.eqRefl _) (fst_pair _ _).eqSymm hq'.wk.wk
  have e2 : Δ ⊢[PRAAx] lt (sndT (pairT (Syn.shift q) (var 0))) (fstT (pairT (Syn.shift q) (var 0))) :=
    lt_congr (snd_pair _ _).eqSymm (fst_pair _ _).eqSymm Prf.hyp1
  have e3 : Δ ⊢[PRAAx] gcd (sndT (pairT (Syn.shift q) (var 0))) (fstT (pairT (Syn.shift q) (var 0))) ≐ one :=
    (congrGcd (snd_pair _ _) (fst_pair _ _)).eqTrans Prf.hyp0
  have bN := Prf.impE (Prf.impE (Prf.impE (Prf.impE (b.wk.wk : Δ ⊢[PRAAx] _) e0) e1) e2) e3
  have m := mat_inA (mask aP) (mask aN) (Γ := Δ) (y := pairT (pairT (Syn.shift q) (var 0)) (Syn.shift y))
    (k := Syn.shift k) (c := Syn.shift c)
    (by
      rw [show Syn.shift (pairT (pairT (Syn.shift q) (var 0)) (Syn.shift y)) =
          pairT (Syn.shift (pairT (Syn.shift q) (var 0))) (Syn.shift (Syn.shift y)) from shift_pairT _ _,
        show Syn.shift (succ (two * Syn.shift k)) = Syn.shift (Syn.shift (succ (two * k))) by simp [Syn.shift]]
      exact bN)
  rw [show Syn.shift (succ k) = succ (Syn.shift k) by simp [Syn.shift]]
  exact m

/-! ## The matrices of the two directions -/

/-- Forward, one `N`: the residue-uniform bound gives the `B` row at the residue code `p`. -/
theorem fwd_mat {y h k c p : PTm n} (hh : Γ ⊢[PRAAx] le two h) (hR : Γ ⊢[PRAAx] InR aP aN (fstT p) y (succ k) c)
    (h0 : Γ ⊢[PRAAx] p ≐ pairT (fstT p) (sndT p)) (h1 : Γ ⊢[PRAAx] le two (fstT p))
    (h2 : Γ ⊢[PRAAx] lt (sndT p) (fstT p)) (h3 : Γ ⊢[PRAAx] gcd (sndT p) (fstT p) ≐ one) (N : PTm n) :
    Γ ⊢[PRAAx] Mat (AB (mask (bvB aP))) (AB (mask (bvB aN))) (pairT p (pairT h y)) k (Cout k c) N := by
  have core := forward_res_core aP aN h1 h2 h3 hh (by ipra_le 𝔞 k : Γ ⊢[PRAAx] le one (succ k)) y hR N
  simp only [Mat, inst2_AB]
  have eP : Γ ⊢[PRAAx] MB aP N (fstT p) (sndT p) h y ≐ Apre (mask (bvB aP)) N (pairT p (pairT h y)) :=
    congrAp2 _ (.eqRefl _) (congrPairT h0.eqSymm (.eqRefl _))
  have eN : Γ ⊢[PRAAx] MB aN N (fstT p) (sndT p) h y ≐ Apre (mask (bvB aN)) N (pairT p (pairT h y)) :=
    congrAp2 _ (.eqRefl _) (congrPairT h0.eqSymm (.eqRefl _))
  exact le_congr (congrPw (congrAdd (congrMonus eP eN) (congrMonus eN eP)) (.eqRefl _)) (.eqRefl _) core

/-- Backward, one `N`: the residue-uniform `B` bound gives the `A` row at the residue code `p`. -/
theorem bwd_mat {y h k c p : PTm n} (hh : Γ ⊢[PRAAx] le two h)
    (hR : Γ ⊢[PRAAx] InR (bvB aP) (bvB aN) (fstT p) (pairT h y) (succ k) c)
    (h0 : Γ ⊢[PRAAx] p ≐ pairT (fstT p) (sndT p)) (h1 : Γ ⊢[PRAAx] le two (fstT p))
    (h2 : Γ ⊢[PRAAx] lt (sndT p) (fstT p)) (h3 : Γ ⊢[PRAAx] gcd (sndT p) (fstT p) ≐ one) (N : PTm n) :
    Γ ⊢[PRAAx] Mat (AB (mask aP)) (AB (mask aN)) (pairT p y) k (Cout k c) N := by
  have core := backward_res_core aP aN h1 h2 h3 hh (by ipra_le 𝔞 k : Γ ⊢[PRAAx] le one (succ k)) y hR N
  simp only [Mat, inst2_AB]
  have eP : Γ ⊢[PRAAx] Apre (mask aP) N (pairT (pairT (fstT p) (sndT p)) y) ≐ Apre (mask aP) N (pairT p y) :=
    congrAp2 _ (.eqRefl _) (congrPairT h0.eqSymm (.eqRefl _))
  have eN : Γ ⊢[PRAAx] Apre (mask aN) N (pairT (pairT (fstT p) (sndT p)) y) ≐ Apre (mask aN) N (pairT p y) :=
    congrAp2 _ (.eqRefl _) (congrPairT h0.eqSymm (.eqRefl _))
  exact le_congr (congrPw (congrAdd (congrMonus eP eN) (congrMonus eN eP)) (.eqRefl _)) (.eqRefl _) core

/-! ## The matrices under `∀p` and `∀N` -/

/-- The four residue facts about `var 0`, shifted under the `∀N` binder. -/
theorem ok_shift {Θ : List (Fm PTm (n + 1))}
    (h0 : Θ ⊢[PRAAx] var 0 ≐ pairT (fstT (var 0)) (sndT (var 0))) (h1 : Θ ⊢[PRAAx] le two (fstT (var 0)))
    (h2 : Θ ⊢[PRAAx] lt (sndT (var 0)) (fstT (var 0))) (h3 : Θ ⊢[PRAAx] gcd (sndT (var 0)) (fstT (var 0)) ≐ one) :
    (Θ.map Fm.shift ⊢[PRAAx] var 1 ≐ pairT (fstT (var 1)) (sndT (var 1))) ∧
      (Θ.map Fm.shift ⊢[PRAAx] le two (fstT (var 1))) ∧ (Θ.map Fm.shift ⊢[PRAAx] lt (sndT (var 1)) (fstT (var 1))) ∧
      (Θ.map Fm.shift ⊢[PRAAx] gcd (sndT (var 1)) (fstT (var 1)) ≐ one) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e := h0.shift
    simp only [Fm.shift, Fm.subst_eq, subst_pairT, subst_fstT, subst_sndT, Syn.subst_var] at e
    exact e
  · have e := h1.shift
    simp only [Fm.shift, subst_le, subst_fstT, Syn.subst_var, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] at e
    exact e
  · have e := h2.shift
    simp only [Fm.shift, lt, subst_le, subst_fstT, subst_sndT, Syn.subst_var, ConciseIPRA.PTm.subst_succ] at e
    exact e
  · have e := h3.shift
    simp only [Fm.shift, Fm.subst_eq, subst_ex2, subst_fstT, subst_sndT, Syn.subst_var, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero] at e
    exact e

theorem subst_InR {m : ℕ} (σ : Fin n → PTm m) (q y r c : PTm n) :
    (InR aP aN q y r c).subst σ = InR aP aN (Syn.subst σ q) (Syn.subst σ y) (Syn.subst σ r) (Syn.subst σ c) := by
  rw [show InR aP aN q y r c = Fm.all (lt (var 0) (Syn.shift q) ⟶ (gcd (var 0) (Syn.shift q) ≐ one) ⟶
      InA (mask aP) (mask aN) (pairT (pairT (Syn.shift q) (var 0)) (Syn.shift y)) (Syn.shift r) (Syn.shift c)) from rfl,
    Fm.subst_all, Fm.subst_imp, Fm.subst_imp, subst_InA]
  simp only [lt, subst_le, Fm.subst_eq, subst_ex2, subst_pairT, Syn.subst_var, Syn.up_zero, up1_v0',
    subst_up_shift_pal, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
  try rfl

/-- Forward: the `A` matrix at `2k + 1` gives the `B` matrix at `k` with the witness `C_r(c)`. -/
theorem fwd_AF {y h k c : PTm n} (hh : Γ ⊢[PRAAx] le two h)
    (H : Γ ⊢[PRAAx] AF (AB (mask aP)) (AB (mask aN)) y (succ (two * k)) c) :
    Γ ⊢[PRAAx] AF (AB (mask (bvB aP))) (AB (mask (bvB aN))) (pairT h y) k (Cout k c) := by
  refine .allI (.impI (.impI (.impI (.impI ?_))))
  let Θ : List (Fm PTm (n + 1)) := (gcd (sndT (var 0)) (fstT (var 0)) ≐ one) :: lt (sndT (var 0)) (fstT (var 0)) ::
    le two (fstT (var 0)) :: (var 0 ≐ pairT (fstT (var 0)) (sndT (var 0))) :: Γ.map Fm.shift
  have H1 : Θ ⊢[PRAAx] AF (AB (mask aP)) (AB (mask aN)) (Syn.shift y) (succ (two * Syn.shift k)) (Syn.shift c) := by
    have b := H.shift
    rw [shift_AF, show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
    exact b.wk.wk.wk.wk
  have hR := toInR aP aN (Prf.hyp1.wk : Θ ⊢[PRAAx] le two (fstT (var 0))) H1
  obtain ⟨o0, o1, o2, o3⟩ := ok_shift (Θ := Θ) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0
  refine .allI ?_
  have hR' : Θ.map Fm.shift ⊢[PRAAx] InR aP aN (fstT (var 1)) (Syn.shift (Syn.shift y)) (succ (Syn.shift (Syn.shift k)))
      (Syn.shift (Syn.shift c)) := by
    have b := hR.shift
    simp only [Fm.shift, subst_InR, subst_fstT, Syn.subst_var, ConciseIPRA.PTm.subst_succ, subst_sh] at b
    exact b
  have hh2 : Θ.map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift h)) := by
    have b : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift h)) := two_le_shift (two_le_shift hh)
    exact b.wk.wk.wk.wk
  have f := fwd_mat aP aN hh2 hR' o0 o1 o2 o3 (var 0)
  rw [show Syn.shift (Syn.shift (pairT h y)) = pairT (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift y)) by
      simp only [shift_pairT],
    show Syn.shift (Syn.shift (Cout k c)) = Cout (Syn.shift (Syn.shift k)) (Syn.shift (Syn.shift c)) by simp [Syn.shift]]
  exact f

/-- Backward: the `B` matrix at `2k + 1` gives the `A` matrix at `k` with the witness `C_r(c)`. -/
theorem bwd_AF {y h k c : PTm n} (hh : Γ ⊢[PRAAx] le two h)
    (H : Γ ⊢[PRAAx] AF (AB (mask (bvB aP))) (AB (mask (bvB aN))) (pairT h y) (succ (two * k)) c) :
    Γ ⊢[PRAAx] AF (AB (mask aP)) (AB (mask aN)) y k (Cout k c) := by
  refine .allI (.impI (.impI (.impI (.impI ?_))))
  let Θ : List (Fm PTm (n + 1)) := (gcd (sndT (var 0)) (fstT (var 0)) ≐ one) :: lt (sndT (var 0)) (fstT (var 0)) ::
    le two (fstT (var 0)) :: (var 0 ≐ pairT (fstT (var 0)) (sndT (var 0))) :: Γ.map Fm.shift
  have H1 : Θ ⊢[PRAAx] AF (AB (mask (bvB aP))) (AB (mask (bvB aN))) (Syn.shift (pairT h y)) (succ (two * Syn.shift k))
      (Syn.shift c) := by
    have b := H.shift
    rw [shift_AF, show Syn.shift (succ (two * k)) = succ (two * Syn.shift k) by simp [Syn.shift]] at b
    exact b.wk.wk.wk.wk
  have hR := toInR (bvB aP) (bvB aN) (Prf.hyp1.wk : Θ ⊢[PRAAx] le two (fstT (var 0))) H1
  obtain ⟨o0, o1, o2, o3⟩ := ok_shift (Θ := Θ) Prf.hyp1.wk.wk Prf.hyp1.wk Prf.hyp1 Prf.hyp0
  refine .allI ?_
  have hR' : Θ.map Fm.shift ⊢[PRAAx] InR (bvB aP) (bvB aN) (fstT (var 1))
      (pairT (Syn.shift (Syn.shift h)) (Syn.shift (Syn.shift y))) (succ (Syn.shift (Syn.shift k)))
      (Syn.shift (Syn.shift c)) := by
    have b := hR.shift
    simp only [Fm.shift, subst_InR, subst_fstT, subst_pairT, Syn.subst_var, ConciseIPRA.PTm.subst_succ, subst_sh,
      shift_pairT] at b
    exact b
  have hh2 : Θ.map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift h)) := by
    have b : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le two (Syn.shift (Syn.shift h)) := two_le_shift (two_le_shift hh)
    exact b.wk.wk.wk.wk
  have f := bwd_mat aP aN hh2 hR' o0 o1 o2 o3 (var 0)
  rw [show Syn.shift (Syn.shift (Cout k c)) = Cout (Syn.shift (Syn.shift k)) (Syn.shift (Syn.shift c)) by simp [Syn.shift]]
  exact f


/-! ## The sentences -/


/-- `fwd_AF` with the binder forms as equations. -/
theorem fwd_AF_eq {y h k c X K C X' K' C' : PTm n} (hX : X = y) (hK : K = succ (two * k)) (hC : C = c)
    (hX' : X' = pairT h y) (hK' : K' = k) (hC' : C' = Cout k c) (hh : Γ ⊢[PRAAx] le two h)
    (H : Γ ⊢[PRAAx] AF (AB (mask aP)) (AB (mask aN)) X K C) :
    Γ ⊢[PRAAx] AF (AB (mask (bvB aP))) (AB (mask (bvB aN))) X' K' C' := by
  subst hX hK hC hX' hK' hC'
  exact fwd_AF aP aN hh H

/-- `bwd_AF` with the binder forms as equations. -/
theorem bwd_AF_eq {y h k c X K C X' K' C' : PTm n} (hX : X = pairT h y) (hK : K = succ (two * k)) (hC : C = c)
    (hX' : X' = y) (hK' : K' = k) (hC' : C' = Cout k c) (hh : Γ ⊢[PRAAx] le two h)
    (H : Γ ⊢[PRAAx] AF (AB (mask (bvB aP))) (AB (mask (bvB aN))) X K C) :
    Γ ⊢[PRAAx] AF (AB (mask aP)) (AB (mask aN)) X' K' C' := by
  subst hX hK hC hX' hK' hC'
  exact bwd_AF aP aN hh H

/-- `thm:powerdivisor`, progression rows, `A ⇒ B_h`. -/
theorem growth_res_forward {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n) :
    Γ ⊢[PRAAx] GrowthP (AB (mask aP)) (AB (mask aN)) y ⟶
      GrowthP (AB (mask (bvB aP))) (AB (mask (bvB aN))) (pairT h y) := by
  refine all_ex_imp_at (succ (two * var 0)) (Cout (var 1) (var 0)) ?_
  simp only [GrowthP, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_AF, subst_up_shift_pal, Syn.subst_inst_shift, up1_v0',
    up1_v1', up2_v0', up2_v1', Syn.subst_var, subst_sh, Syn.up_zero, Syn.inst_zero, Syn.shift_var, Syn.inst_succ]
  exact fwd_AF_eq aP aN (y := Syn.shift (Syn.shift y)) (h := Syn.shift (Syn.shift h)) (k := var 1) (c := var 0)
    (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
    (by simp [Syn.shift]) (two_le_shift (two_le_shift hh)).wk Prf.hyp0

/-- `thm:powerdivisor`, progression rows, `B_h ⇒ A`. -/
theorem growth_res_backward {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n) :
    Γ ⊢[PRAAx] GrowthP (AB (mask (bvB aP))) (AB (mask (bvB aN))) (pairT h y) ⟶
      GrowthP (AB (mask aP)) (AB (mask aN)) y := by
  refine all_ex_imp_at (succ (two * var 0)) (Cout (var 1) (var 0)) ?_
  simp only [GrowthP, Fm.shift, Fm.subst_all, Fm.subst_ex, subst_AF, subst_up_shift_pal, Syn.subst_inst_shift, up1_v0',
    up1_v1', up2_v0', up2_v1', Syn.subst_var, subst_sh, Syn.up_zero, Syn.inst_zero, Syn.shift_var, Syn.inst_succ]
  exact bwd_AF_eq aP aN (y := Syn.shift (Syn.shift y)) (h := Syn.shift (Syn.shift h)) (k := var 1) (c := var 0)
    (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift]) (by simp [Syn.shift])
    (by simp [Syn.shift]) (two_le_shift (two_le_shift hh)).wk Prf.hyp0

/-- `thm:powerdivisor`, progression rows (exponent `h ≥ 2`, signed coefficients `a = a⁺ − a⁻`): in object iPRA,
`(∀k ∃c ∀⟨q,b⟩ reduced ∀N |A_{q,b}(N)|^{2(k+1)} ≤ cN^{k+2}) ↔ (∀k ∃c ∀⟨q,b⟩ reduced ∀N |B_{h;q,b}(N)|^{2(k+1)} ≤ cN^{k+2})`,
with the witness `C_r(c) = (c+1)(8r)^{2r}` in both directions; the constant precedes the residue choice. -/
theorem growth_res_iff {h : PTm n} (hh : Γ ⊢[PRAAx] le two h) (y : PTm n) :
    Γ ⊢[PRAAx] Fm.iff (GrowthP (AB (mask aP)) (AB (mask aN)) y)
      (GrowthP (AB (mask (bvB aP))) (AB (mask (bvB aN))) (pairT h y)) :=
  .andI (growth_res_forward aP aN hh y) (growth_res_backward aP aN hh y)

end LeanProofs.IPRA.AnalyticNumberTheory.PowerResidueGrowth
