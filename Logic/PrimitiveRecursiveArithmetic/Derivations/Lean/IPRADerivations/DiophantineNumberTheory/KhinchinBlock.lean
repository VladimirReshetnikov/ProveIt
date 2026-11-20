import IPRADerivations.DiophantineNumberTheory.KhinchinBlockScales
import IPRADerivations.DiophantineNumberTheory.KhinchinBlockArith
import IPRADerivations.DiophantineNumberTheory.KhinchinScaleCount
import IPRADerivations.AnalyticNumberTheory.Primes

/-!
# A finite Khinchin block covers a fixed fraction (`hurwitz_khinchin_ipra`, (K11))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, §"A finite block covers a fixed
fraction of every interval", (K11): "if `S ≥ 1`, `|⋃_{k=K}^B E_k(J)| ≥ L/16384`."

For the scales `k < B` of `KhinchinBlockScales` (`Q_k = 2^{K₀+k}`, common grid `T = R! G`, cells
`c < T M`, widths `w_k = wb(k, X)`), under

* `2^{K₀+B} ≤ M`, `2^{K₀+B} ≤ R`, `R² ≤ G`, `G ≥ 1`, (K4) `256β ≤ D K₀`, `α ≤ γ ≤ β = b₀ + 1`,
  `D = γ − α ≥ 1`, `M ≥ 1`;
* `t_k ≤ 1` for every scale: `4 Q_k² w_k ≤ T` (`hW`, one closed `∀`-formula);
* `S ≥ 1`: `T ≤ 4 Σ_k Q_k² w_k`;

the union `V = |⋃_k E_k|` (in cells) satisfies `D T ≤ 8192 β V`, i.e. `|⋃_k E_k| / T ≥ L/16384`
(`block_cover`). The proof feeds `KhinchinBlockArith.block_arith` with

* (K8) per scale (`k_bounds`, from `KhinchinScaleCount.k8_bounds`), summed by `sum_le_lin1`;
* (K9) per ordered pair (`pair_bound`: `KhinchinOverlap.overlap_bound`, `scale_count`, `k3_bounds`,
  `KhinchinBlockGeo.pair_arith`), summed over `k < ℓ` with `geo2` (`low_bound`), then over `ℓ` (`sum_le_lin`);
* `KhinchinMoment.cross_le`;
* Cauchy–Schwarz with the ordered moment (`Foundations/SecondMoment.cs_moment`, `ord_moment`, Fubini).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (shift_inst2')
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Foundations.IntervalCover (covB measure)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB acB)
open LeanProofs.IPRA.Foundations.IntervalOverlap (inter)
open LeanProofs.IPRA.Foundations.SecondMoment (ppB lowB inst2_lowB cs_moment ord_moment)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale (tup AK actK)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScaleCount (scale_count k8_bounds)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinReduced (k3_bounds)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinOverlap (overlap_bound)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockGeo (s_facts w_le_s pair_arith q2B inst2_q2B geo2)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockScales (Xt Qk Kk yk bB uB b_bit scale_E scale_inter
  u_at pw_mono2)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlockArith (block_arith)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Summing scaled pointwise inequalities -/

/-- `a f_i ≤ c₁ g_i + c₂ h_i` for `i < N` gives `a Σf ≤ c₁ Σg + c₂ Σh`. -/
theorem sum_le_lin (f g1 g2 : PTm 2) (a c1 c2 x y1 y2 N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * inst2 f (var 0) (Syn.shift x))
        (Syn.shift c1 * inst2 g1 (var 0) (Syn.shift y1) + Syn.shift c2 * inst2 g2 (var 0) (Syn.shift y2)))) :
    Γ ⊢[PRAAx] le (a * ap2 (sumF f) N x) (c1 * ap2 (sumF g1) N y1 + c2 * ap2 (sumF g2) N y2) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * ap2 (sumF f) (var 0) (Syn.shift x))
        (Syn.shift c1 * ap2 (sumF g1) (var 0) (Syn.shift y1) + Syn.shift c2 * ap2 (sumF g2) (var 0) (Syn.shift y2))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, le_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        PTm.subst_mul, PTm.subst_add, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      have e1 := natEq (sum_zero (Γ := le zero N :: Γ) f x)
      have e2 := natEq (sum_zero (Γ := le zero N :: Γ) g1 y1)
      have e3 := natEq (sum_zero (Γ := le zero N :: Γ) g2 y2)
      ipra_le 0 with 𝔞 c1 * e2 + 𝔞 c2 * e3 - 𝔞 a * e1
    · simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        PTm.subst_mul, PTm.subst_add, ConciseIPRA.PTm.subst_zero]
      refine .impI ?_
      let Θ : List (Fm PTm (n + 1)) := le (succ (var 0)) (Syn.shift N) ::
        (le (var 0) (Syn.shift N) ⟶ le (Syn.shift a * ap2 (sumF f) (var 0) (Syn.shift x))
          (Syn.shift c1 * ap2 (sumF g1) (var 0) (Syn.shift y1) + Syn.shift c2 * ap2 (sumF g2) (var 0) (Syn.shift y2))) ::
        Γ.map Fm.shift
      have hle : Θ ⊢[PRAAx] le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
      have ih : Θ ⊢[PRAAx] le (Syn.shift a * ap2 (sumF f) (var 0) (Syn.shift x))
          (Syn.shift c1 * ap2 (sumF g1) (var 0) (Syn.shift y1) + Syn.shift c2 * ap2 (sumF g2) (var 0) (Syn.shift y2)) :=
        Prf.impE Prf.hyp1 hle
      have pt : Θ ⊢[PRAAx] le (Syn.shift a * inst2 f (var 0) (Syn.shift x))
          (Syn.shift c1 * inst2 g1 (var 0) (Syn.shift y1) + Syn.shift c2 * inst2 g2 (var 0) (Syn.shift y2)) :=
        Prf.impE h.allOpen.wk.wk Prf.hyp0
      have e1 := natEq (sum_succ' (Γ := Θ) f (var 0) (Syn.shift x))
      have e2 := natEq (sum_succ' (Γ := Θ) g1 (var 0) (Syn.shift y1))
      have e3 := natEq (sum_succ' (Γ := Θ) g2 (var 0) (Syn.shift y2))
      ipra_le sl ih + sl pt with 𝔞 (Syn.shift c1) * e2 + 𝔞 (Syn.shift c2) * e3 - 𝔞 (Syn.shift a) * e1
  have h2 := Prf.allE N hall
  simp only [Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    PTm.subst_mul, PTm.subst_add, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl N)

/-- `a f_i ≤ c g_i` for `i < N` gives `a Σf ≤ c Σg`. -/
theorem sum_le_lin1 (f g : PTm 2) (a c x y N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * inst2 f (var 0) (Syn.shift x)) (Syn.shift c * inst2 g (var 0) (Syn.shift y)))) :
    Γ ⊢[PRAAx] le (a * ap2 (sumF f) N x) (c * ap2 (sumF g) N y) := by
  have h' : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (Syn.shift a * inst2 f (var 0) (Syn.shift x))
        (Syn.shift c * inst2 g (var 0) (Syn.shift y) + Syn.shift zero * inst2 g (var 0) (Syn.shift y))) := by
    refine .allI (.impI ?_)
    have p := Prf.impE (h.allOpen.wk (ψ := lt (var 0) (Syn.shift N))) Prf.hyp0
    rw [show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
    exact le_congr (.eqRefl _) ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)).eqSymm p
  have s := sum_le_lin f g g a c zero x y y N h'
  exact le_congr (.eqRefl _) ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)) s

/-! ## One scale -/

/-- (K8) for the scale `k < B`, in body form: `D u_k ≤ 16β|E_k|` and `β|E_k| ≤ 2D u_k`. -/
theorem k_bounds (wb : PTm 2) {k B K0 M R G α γ b0 : PTm n} (hk : Γ ⊢[PRAAx] lt k B)
    (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0)) (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hQM : Γ ⊢[PRAAx] le (pw two (K0 + B)) M) (hQR : Γ ⊢[PRAAx] le (pw two (K0 + B)) R)
    (hK4 : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * K0))
    (hW : Γ ⊢[PRAAx] le (num 4 * (Qk K0 k * Qk K0 k) * inst2 wb k (Xt K0 M R G α γ b0)) (fact R * G)) :
    Γ ⊢[PRAAx] le (monus γ α * inst2 (uB wb) k (Xt K0 M R G α γ b0))
        (num 16 * succ b0 * inst2 (pB (bB wb)) k (pairT (fact R * G * M) (Xt K0 M R G α γ b0))) ⋏
      le (succ b0 * inst2 (pB (bB wb)) k (pairT (fact R * G * M) (Xt K0 M R G α γ b0)))
        (num 2 * monus γ α * inst2 (uB wb) k (Xt K0 M R G α γ b0)) := by
  have hkB : Γ ⊢[PRAAx] le k B := le_of_lt hk
  have hQMk := le_trans (pw_mono2 (K0 := K0) hkB) hQM
  have hQRk := le_trans (pw_mono2 (K0 := K0) hkB) hQR
  have hKk : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * (K0 + k)) := by
    ipra_le sl hK4 + 𝔞 (monus γ α) * 𝔞 k
  have hwk : Γ ⊢[PRAAx] le (Qk K0 k * Qk K0 k * inst2 wb k (Xt K0 M R G α γ b0)) (fact R * G) := by
    ipra_le sl hW + 3 * 𝔞 (Qk K0 k) * 𝔞 (Qk K0 k) * 𝔞 (inst2 wb k (Xt K0 M R G α γ b0))
  have k8 := k8_bounds (α := α) (γ := γ) (b0 := b0) (G := G) (w := inst2 wb k (Xt K0 M R G α γ b0))
    hαγ hγ hQMk hKk hM hQRk hwk
  have eE := natEq (scale_E (Γ := Γ) wb k (fact R * G * M) K0 M R G α γ b0)
  have eU := natEq (u_at (Γ := Γ) wb k K0 M R G α γ b0)
  have l1 := Prf.andE₁ k8
  have l2 := Prf.andE₂ k8
  exact .andI (by ipra_le sl l1 with 𝔞 (monus γ α) * eU - (16 * 𝔞 b0 + 16) * eE)
    (by ipra_le sl l2 with (𝔞 b0 + 1) * eE - 2 * 𝔞 (monus γ α) * eU)

/-! ## One ordered pair of scales -/

theorem pw2_pos (j : PTm n) : Γ ⊢[PRAAx] pw two j ≐ succ (pred (pw two j)) :=
  DiophantineNumberTheory.FLTMultiples.pw_pos one j

/-- `Q_ℓ² ≤ T` for `Q_ℓ ≤ R`, `R² ≤ G`. -/
theorem q2_le_T {Q R G : PTm n} (hQR : Γ ⊢[PRAAx] le Q R) (hRG : Γ ⊢[PRAAx] le (R * R) G) :
    Γ ⊢[PRAAx] le (Q * Q) (fact R * G) := by
  have ef := natEq (fact_pos (Γ := Γ) R)
  ipra_le 𝔞 R * sl hQR + 𝔞 Q * sl hQR + sl hRG + 𝔞 G * 𝔞 (pred (fact R)) with 𝔞 G * ef

/-- (K9) for the ordered pair `k < ℓ < B`, in body form:
`3βT |E_k ∩ E_ℓ| ≤ 12D u_k u_ℓ + 15D u_ℓ Q_k² s_ℓ` with `s_ℓ = ⌊T/Q_ℓ²⌋`. -/
theorem pair_bound (wb : PTm 2) {k l B K0 M R G α γ b0 : PTm n} (hkl : Γ ⊢[PRAAx] lt k l)
    (hl : Γ ⊢[PRAAx] lt l B) (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQM : Γ ⊢[PRAAx] le (pw two (K0 + B)) M)
    (hQR : Γ ⊢[PRAAx] le (pw two (K0 + B)) R) (hK4 : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * K0))
    (hRG : Γ ⊢[PRAAx] le (R * R) G)
    (hWl : Γ ⊢[PRAAx] le (num 4 * (Qk K0 l * Qk K0 l) * inst2 wb l (Xt K0 M R G α γ b0)) (fact R * G)) :
    Γ ⊢[PRAAx] le (num 3 * succ b0 * (fact R * G) *
        inst3 (ppB (bB wb)) l k (pairT (fact R * G * M) (Xt K0 M R G α γ b0)))
      (num 12 * monus γ α * inst2 (uB wb) k (Xt K0 M R G α γ b0) * inst2 (uB wb) l (Xt K0 M R G α γ b0) +
        num 15 * monus γ α * inst2 (uB wb) l (Xt K0 M R G α γ b0) * (Qk K0 k * Qk K0 k) *
          quo (fact R * G) (Qk K0 l * Qk K0 l)) := by
  have hkB : Γ ⊢[PRAAx] le k B := le_of_lt (le_trans hkl (le_of_lt hl))
  have hlB : Γ ⊢[PRAAx] le l B := le_of_lt hl
  have hQMk := le_trans (pw_mono2 (K0 := K0) hkB) hQM
  have hQRl := le_trans (pw_mono2 (K0 := K0) hlB) hQR
  have hKk : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * (K0 + k)) := by
    ipra_le sl hK4 + 𝔞 (monus γ α) * 𝔞 k
  have hQpos : Γ ⊢[PRAAx] Qk K0 l * Qk K0 l ≐ succ (pred (Qk K0 l * Qk K0 l)) := pos_mul' (pw2_pos _) (pw2_pos _)
  have sf := s_facts hQpos (q2_le_T hQRl hRG)
  have hws := w_le_s hQpos hWl
  have hQl : Γ ⊢[PRAAx] le (quo (Qk K0 l) (num 4)) (Qk K0 l) :=
    LeanProofs.IPRA.AnalyticNumberTheory.DivisorHyperbola.quo_le_self _ _
  have ov := overlap_bound (Γ := Γ) (M := M) (Qk := Qk K0 k) (Q'k := quo (Qk K0 k) (num 4)) (Ql := Qk K0 l)
    (Q'l := quo (Qk K0 l) (num 4)) (R := R) (G := G) (wk := inst2 wb k (Xt K0 M R G α γ b0))
    (wl := inst2 wb l (Xt K0 M R G α γ b0)) (α := α) (γ := γ) (β := succ b0)
    (s := quo (fact R * G) (Qk K0 l * Qk K0 l)) (T' := fact R * G * M)
    hM hQl hQRl (Prf.andE₂ (Prf.andE₂ sf)) (Prf.andE₁ sf)
  have eN := scale_count (Γ := Γ) (T := fact R * G) (α := α) (γ := γ) (β := succ b0) (Q := Qk K0 k) hM
  have k3 := Prf.andE₂ (k3_bounds hαγ hγ hQMk hKk)
  have hN : Γ ⊢[PRAAx] le (succ b0 * ap2 (sumF (acB actK)) (monus (Qk K0 k) (quo (Qk K0 k) (num 4)) * M)
      (tup M (quo (Qk K0 k) (num 4)) (fact R * G) α γ (succ b0))) (num 2 * monus γ α * (Qk K0 k * Qk K0 k)) :=
    le_congr (congrMul (.eqRefl _) eN).eqSymm (.eqRefl _) k3
  have dm := div_mod_at (Γ := Γ) (x := inst2 wb k (Xt K0 M R G α γ b0) + inst2 wb l (Xt K0 M R G α γ b0))
    (Prf.andE₂ (Prf.andE₂ sf))
  have edm := natEq (Prf.andE₁ dm)
  have hfl : Γ ⊢[PRAAx] le (quo (fact R * G) (Qk K0 l * Qk K0 l) *
      quo (inst2 wb k (Xt K0 M R G α γ b0) + inst2 wb l (Xt K0 M R G α γ b0)) (quo (fact R * G) (Qk K0 l * Qk K0 l)))
      (inst2 wb k (Xt K0 M R G α γ b0) + inst2 wb l (Xt K0 M R G α γ b0)) := by
    ipra_le 𝔞 (rem (inst2 wb k (Xt K0 M R G α γ b0) + inst2 wb l (Xt K0 M R G α γ b0))
      (quo (fact R * G) (Qk K0 l * Qk K0 l))) with edm
  have pa := pair_arith ov hfl hN hws (Prf.andE₁ (Prf.andE₂ sf))
  have eI := natEq (scale_inter (Γ := Γ) wb l k (fact R * G * M) K0 M R G α γ b0)
  have eUk := natEq (u_at (Γ := Γ) wb k K0 M R G α γ b0)
  have eUl := natEq (u_at (Γ := Γ) wb l K0 M R G α γ b0)
  ipra_le sl pa with 12 * 𝔞 (monus γ α) * 𝔞 (inst2 (uB wb) l (Xt K0 M R G α γ b0)) * eUk +
    12 * 𝔞 (monus γ α) * 𝔞 (Qk K0 k) * 𝔞 (Qk K0 k) * 𝔞 (inst2 wb k (Xt K0 M R G α γ b0)) * eUl +
    15 * 𝔞 (monus γ α) * 𝔞 (Qk K0 k) * 𝔞 (Qk K0 k) * 𝔞 (quo (fact R * G) (Qk K0 l * Qk K0 l)) * eUl -
    3 * (𝔞 b0 + 1) * 𝔞 (fact R) * 𝔞 G * eI

/-- `pair_bound` read through the row body of the lower sum. -/
theorem low_pt (wb : PTm 2) {k l B K0 M R G α γ b0 : PTm n} (hkl : Γ ⊢[PRAAx] lt k l)
    (hl : Γ ⊢[PRAAx] lt l B) (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQM : Γ ⊢[PRAAx] le (pw two (K0 + B)) M)
    (hQR : Γ ⊢[PRAAx] le (pw two (K0 + B)) R) (hK4 : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * K0))
    (hRG : Γ ⊢[PRAAx] le (R * R) G)
    (hWl : Γ ⊢[PRAAx] le (num 4 * (Qk K0 l * Qk K0 l) * inst2 wb l (Xt K0 M R G α γ b0)) (fact R * G)) :
    Γ ⊢[PRAAx] le (num 3 * succ b0 * (fact R * G) *
        inst2 (rowB (ppB (bB wb))) k (pairT l (pairT (fact R * G * M) (Xt K0 M R G α γ b0))))
      (num 12 * monus γ α * inst2 (uB wb) l (Xt K0 M R G α γ b0) * inst2 (uB wb) k (Xt K0 M R G α γ b0) +
        num 15 * monus γ α * inst2 (uB wb) l (Xt K0 M R G α γ b0) * quo (fact R * G) (Qk K0 l * Qk K0 l) *
          inst2 q2B k K0) := by
  rw [inst2_rowB, inst2_q2B]
  have p := pair_bound wb hkl hl hαγ hγ hM hQM hQR hK4 hRG hWl
  have e1 := natEq (congrInst3 (Γ := Γ) (ppB (bB wb)) (fst_pair l (pairT (fact R * G * M) (Xt K0 M R G α γ b0)))
    (.eqRefl k) (snd_pair l (pairT (fact R * G * M) (Xt K0 M R G α γ b0))))
  ipra_le sl p with 3 * (𝔞 b0 + 1) * 𝔞 (fact R) * 𝔞 G * e1

/-- (K9) summed over `k < ℓ`: `3βT L_ℓ ≤ 12D u_ℓ Σ_{k<ℓ} u_k + 5DT u_ℓ`. -/
theorem low_bound (wb : PTm 2) {l B K0 M R G α γ b0 : PTm n}
    (hl : Γ ⊢[PRAAx] lt l B) (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0))
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQM : Γ ⊢[PRAAx] le (pw two (K0 + B)) M)
    (hQR : Γ ⊢[PRAAx] le (pw two (K0 + B)) R) (hK4 : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * K0))
    (hRG : Γ ⊢[PRAAx] le (R * R) G)
    (hWl : Γ ⊢[PRAAx] le (num 4 * (Qk K0 l * Qk K0 l) * inst2 wb l (Xt K0 M R G α γ b0)) (fact R * G)) :
    Γ ⊢[PRAAx] le (num 3 * succ b0 * (fact R * G) * inst2 (lowB (bB wb)) l (pairT (fact R * G * M) (Xt K0 M R G α γ b0)))
      (num 12 * monus γ α * inst2 (DiophantineNumberTheory.KhinchinMoment.crB (uB wb)) l (Xt K0 M R G α γ b0) +
        num 5 * monus γ α * (fact R * G) * inst2 (uB wb) l (Xt K0 M R G α γ b0)) := by
  have S := sum_le_lin (Γ := Γ) (rowB (ppB (bB wb))) (uB wb) q2B (num 3 * succ b0 * (fact R * G))
    (num 12 * monus γ α * inst2 (uB wb) l (Xt K0 M R G α γ b0))
    (num 15 * monus γ α * inst2 (uB wb) l (Xt K0 M R G α γ b0) * quo (fact R * G) (Qk K0 l * Qk K0 l))
    (pairT l (pairT (fact R * G * M) (Xt K0 M R G α γ b0))) (Xt K0 M R G α γ b0) K0 l ?_
  · have hQpos : Γ ⊢[PRAAx] Qk K0 l * Qk K0 l ≐ succ (pred (Qk K0 l * Qk K0 l)) := pos_mul' (pw2_pos _) (pw2_pos _)
    have hQRl := le_trans (pw_mono2 (K0 := K0) (le_of_lt hl)) hQR
    have sf1 := Prf.andE₁ (s_facts hQpos (q2_le_T hQRl hRG))
    have eL := natEq ((show inst2 (lowB (bB wb)) l (pairT (fact R * G * M) (Xt K0 M R G α γ b0)) =
      inst2 (oB (ppB (bB wb))) l (pairT l (pairT (fact R * G * M) (Xt K0 M R G α γ b0))) from inst2_lowB _ _ _) ▸
        oB_at (Γ := Γ) (ppB (bB wb)) l l (pairT (fact R * G * M) (Xt K0 M R G α γ b0)))
    have ecr : inst2 (DiophantineNumberTheory.KhinchinMoment.crB (uB wb)) l (Xt K0 M R G α γ b0) =
        inst2 (uB wb) l (Xt K0 M R G α γ b0) * ap2 (sumF (uB wb)) l (Xt K0 M R G α γ b0) :=
      DiophantineNumberTheory.KhinchinMoment.inst2_crB _ _ _
    rw [ecr]
    have eg := natEq (geo2 (Γ := Γ) l K0)
    ipra_le sl S + 5 * 𝔞 (monus γ α) * 𝔞 (inst2 (uB wb) l (Xt K0 M R G α γ b0)) * sl sf1 +
      5 * 𝔞 (monus γ α) * 𝔞 (inst2 (uB wb) l (Xt K0 M R G α γ b0)) * 𝔞 (quo (fact R * G) (Qk K0 l * Qk K0 l)) *
        𝔞 (pw two K0) * 𝔞 (pw two K0)
      with -5 * 𝔞 (monus γ α) * 𝔞 (inst2 (uB wb) l (Xt K0 M R G α γ b0)) *
        𝔞 (quo (fact R * G) (Qk K0 l * Qk K0 l)) * eg - 3 * (𝔞 b0 + 1) * 𝔞 (fact R) * 𝔞 G * eL
  · refine .allI (.impI ?_)
    let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift l) :: Γ.map Fm.shift
    have sh : ∀ {φ : Fm PTm n}, (Γ ⊢[PRAAx] φ) → (Θ ⊢[PRAAx] Fm.shift φ) := fun h => h.shift.wk
    have p := low_pt (Γ := Θ) wb (k := var 0) (l := Syn.shift l) (B := Syn.shift B) (K0 := Syn.shift K0)
      (M := Syn.shift M) (R := Syn.shift R) (G := Syn.shift G) (α := Syn.shift α) (γ := Syn.shift γ)
      (b0 := Syn.shift b0) Prf.hyp0
      (by simpa [Fm.shift, Syn.shift] using sh hl) (by simpa [Fm.shift, Syn.shift] using sh hαγ)
      (by simpa [Fm.shift, Syn.shift] using sh hγ) (by simpa [Fm.shift, Syn.shift] using sh hM)
      (by simpa [Fm.shift, Syn.shift] using sh hQM) (by simpa [Fm.shift, Syn.shift] using sh hQR)
      (by simpa [Fm.shift, Syn.shift] using sh hK4) (by simpa [Fm.shift, Syn.shift] using sh hRG)
      (by simpa [Fm.shift, Syn.shift, shift_inst2'] using sh hWl)
    convert p using 2 <;> simp [Syn.shift, shift_inst2']

/-! ## The block -/

/-- (K11): `D T ≤ 8192 β |⋃_k E_k|`, i.e. `|⋃_{k<B} E_k| ≥ L T/16384`, for a block with `S ≥ 1`. -/
theorem block_cover (wb : PTm 2) {B K0 M R G α γ b0 : PTm n}
    (hαγ : Γ ⊢[PRAAx] le α γ) (hγ : Γ ⊢[PRAAx] le γ (succ b0)) (hD : Γ ⊢[PRAAx] monus γ α ≐ succ (pred (monus γ α)))
    (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hG : Γ ⊢[PRAAx] G ≐ succ (pred G))
    (hQM : Γ ⊢[PRAAx] le (pw two (K0 + B)) M) (hQR : Γ ⊢[PRAAx] le (pw two (K0 + B)) R)
    (hK4 : Γ ⊢[PRAAx] le (num 256 * succ b0) (monus γ α * K0)) (hRG : Γ ⊢[PRAAx] le (R * R) G)
    (hW : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift B) ⟶
      le (num 4 * (Qk (Syn.shift K0) (var 0) * Qk (Syn.shift K0) (var 0)) *
          inst2 wb (var 0) (Syn.shift (Xt K0 M R G α γ b0))) (Syn.shift (fact R * G))))
    (hS : Γ ⊢[PRAAx] le (fact R * G) (num 4 * ap2 (sumF (uB wb)) B (Xt K0 M R G α γ b0))) :
    Γ ⊢[PRAAx] le (monus γ α * (fact R * G))
      (num 8192 * succ b0 * ap2 (sumF (sg (oB (bB wb)))) (fact R * G * M) (pairT B (Xt K0 M R G α γ b0))) := by
  let X := Xt K0 M R G α γ b0
  let T' := fact R * G * M
  -- per-scale facts under one binder
  let Θ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift B) :: Γ.map Fm.shift
  have sh : ∀ {φ : Fm PTm n}, (Γ ⊢[PRAAx] φ) → (Θ ⊢[PRAAx] Fm.shift φ) := fun h => h.shift.wk
  have hW0 : Θ ⊢[PRAAx] le (num 4 * (Qk (Syn.shift K0) (var 0) * Qk (Syn.shift K0) (var 0)) *
      inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
        (Syn.shift b0))) (fact (Syn.shift R) * Syn.shift G) := by
    have hWb : Γ.map Fm.shift ⊢[PRAAx] (lt (var 0) (Syn.shift B) ⟶
        le (num 4 * (Qk (Syn.shift K0) (var 0) * Qk (Syn.shift K0) (var 0)) *
          inst2 wb (var 0) (Xt (Syn.shift K0) (Syn.shift M) (Syn.shift R) (Syn.shift G) (Syn.shift α) (Syn.shift γ)
            (Syn.shift b0))) (fact (Syn.shift R) * Syn.shift G)) := by
      simpa [Fm.shift, Syn.shift] using hW.allOpen
    exact Prf.impE hWb.wk Prf.hyp0
  have kb := k_bounds (Γ := Θ) wb (k := var 0) (B := Syn.shift B) (K0 := Syn.shift K0) (M := Syn.shift M)
    (R := Syn.shift R) (G := Syn.shift G) (α := Syn.shift α) (γ := Syn.shift γ) (b0 := Syn.shift b0) Prf.hyp0
    (by simpa [Fm.shift, Syn.shift] using sh hαγ) (by simpa [Fm.shift, Syn.shift] using sh hγ)
    (by simpa [Fm.shift, Syn.shift] using sh hM) (by simpa [Fm.shift, Syn.shift] using sh hQM)
    (by simpa [Fm.shift, Syn.shift] using sh hQR) (by simpa [Fm.shift, Syn.shift] using sh hK4) hW0
  have lb := low_bound (Γ := Θ) wb (l := var 0) (B := Syn.shift B) (K0 := Syn.shift K0) (M := Syn.shift M)
    (R := Syn.shift R) (G := Syn.shift G) (α := Syn.shift α) (γ := Syn.shift γ) (b0 := Syn.shift b0) Prf.hyp0
    (by simpa [Fm.shift, Syn.shift] using sh hαγ) (by simpa [Fm.shift, Syn.shift] using sh hγ)
    (by simpa [Fm.shift, Syn.shift] using sh hM) (by simpa [Fm.shift, Syn.shift] using sh hQM)
    (by simpa [Fm.shift, Syn.shift] using sh hQR) (by simpa [Fm.shift, Syn.shift] using sh hK4)
    (by simpa [Fm.shift, Syn.shift] using sh hRG) hW0
  -- the five summed estimates
  have h1 := sum_le_lin1 (Γ := Γ) (uB wb) (pB (bB wb)) (monus γ α) (num 16 * succ b0) X (pairT T' X) B
    (.allI (.impI (by convert Prf.andE₁ kb using 2 <;> simp [X, T', Syn.shift, shift_inst2'])))
  have h2 := sum_le_lin1 (Γ := Γ) (pB (bB wb)) (uB wb) (succ b0) (num 2 * monus γ α) (pairT T' X) X B
    (.allI (.impI (by convert Prf.andE₂ kb using 2 <;> simp [X, T', Syn.shift, shift_inst2'])))
  have h3 := sum_le_lin (Γ := Γ) (lowB (bB wb)) (DiophantineNumberTheory.KhinchinMoment.crB (uB wb)) (uB wb)
    (num 3 * succ b0 * (fact R * G)) (num 12 * monus γ α) (num 5 * monus γ α * (fact R * G)) (pairT T' X) X X B
    (.allI (.impI (by convert lb using 2 <;> simp [X, T', Syn.shift, shift_inst2'])))
  have h4 := DiophantineNumberTheory.KhinchinMoment.cross_le (Γ := Γ) (uB wb) B X
  have cs := cs_moment (Γ := Γ) (bB wb) T' B X
  have fu := fubini (Γ := Γ) (bB wb) T' B X
  have om := ord_moment (Γ := Γ) (bB wb) T' B X (fun Δ c k y => b_bit wb Δ c k y)
  have hcs : Γ ⊢[PRAAx] le (ap2 (sumF (pB (bB wb))) B (pairT T' X) * ap2 (sumF (pB (bB wb))) B (pairT T' X))
      (ap2 (sumF (sg (oB (bB wb)))) T' (pairT B X) *
        (ap2 (sumF (pB (bB wb))) B (pairT T' X) + two * ap2 (sumF (lowB (bB wb))) B (pairT T' X))) :=
    le_congr (congrMul fu fu) (congrMul (.eqRefl _) om) cs
  have hT1 : Γ ⊢[PRAAx] fact R * G ≐ succ (pred (fact R * G)) := pos_mul' (fact_pos R) hG
  have hβ : Γ ⊢[PRAAx] succ b0 ≐ succ (pred (succ b0)) := congrSucc (pred_succ _).eqSymm
  have h3' : Γ ⊢[PRAAx] le (num 3 * succ b0 * (fact R * G) * ap2 (sumF (lowB (bB wb))) B (pairT T' X))
      (num 12 * monus γ α * ap2 (sumF (DiophantineNumberTheory.KhinchinMoment.crB (uB wb))) B X +
        num 5 * monus γ α * (fact R * G) * ap2 (sumF (uB wb)) B X) := h3
  exact block_arith hD hβ hT1 h1 h2 h3' h4 hcs hS

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock
