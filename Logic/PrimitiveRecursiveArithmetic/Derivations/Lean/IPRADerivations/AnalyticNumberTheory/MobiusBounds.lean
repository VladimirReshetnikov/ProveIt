import IPRADerivations.AnalyticNumberTheory.Mobius

/-!
# Möbius sums with arbitrary bounds

Infrastructure for Möbius inversion (`analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`,
`lem:mobius-cancel` and its consequences). `AnalyticNumberTheory/Mobius` uses the prime bound
`N = m + 1` and the summation range `d ≤ m`; here both are freed.

* `sum_ext`: a sum whose terms vanish above `B` may be cut at `B + 1`;
* `val_big`: `v_q(d) = 0` for `q > d ≥ 1`; hence `ω_N(d)`, `s_N(d)` and `μ^±_N(d)` do not depend on the
  bound `N` once `N > d` (`mu_bound`);
* `cancel_gen`: for `k ≥ 1`, any prime bound `N > k` and any range `K > k`,
  `∑_{d<K} [d ≥ 1][d ∣ k] μ⁺_N(d) = ∑_{d<K} [d ≥ 1][d ∣ k] μ⁻_N(d) + [k = 1]`,
  i.e. `∑_{d ∣ k} μ(d) = [k = 1]`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (val isP)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (eq_succ_pred)
open LeanProofs.IPRA.AnalyticNumberTheory.ValuationMul (val_unique)
open LeanProofs.IPRA.AnalyticNumberTheory.Multiplicative (rem_eq')
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (dvd_le' one_le_of_pos)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Cutting a sum -/

/-- Terms vanishing above `B` may be dropped: `∑_{i<N} g(i, x) = ∑_{i<B+1} g(i, x)` for `N ≥ B + 1`. -/
theorem sum_ext (g : PTm 2) {B N x : PTm n}
    (hz : ∀ (Δ : List (Fm PTm (n + 1))) (a : PTm (n + 1)), Γ.map Fm.shift ⊆ Δ →
      (Δ ⊢[PRAAx] lt (Syn.shift B) a) → (Δ ⊢[PRAAx] inst2 g a (Syn.shift x) ≐ zero))
    (hN : Γ ⊢[PRAAx] le (succ B) N) : Γ ⊢[PRAAx] ap2 (sumF g) N x ≐ ap2 (sumF g) (succ B) x := by
  refine (congrAp2 (sumF g) (eq_add_of_le hN) (.eqRefl x)).eqTrans ?_
  refine (sum_split g (succ B) (monus N (succ B)) x).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _))
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [inst2_offB, shift_pairT]
  have hs : Syn.shift (succ B) = succ (Syn.shift B) := by simp [Syn.shift]
  rw [hs]
  let Δ : List (Fm PTm (n + 1)) := lt (var 0) (Syn.shift (monus N (succ B))) :: Γ.map Fm.shift
  have hl : Δ ⊢[PRAAx] lt (Syn.shift B) (succ (Syn.shift B) + var 0) :=
    le_of_eq_add (d := var 0) (by apply deriveNat; ipra_simps; try ring)
  exact (congrInst2 g (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
    (hz Δ _ (List.subset_cons_of_subset _ (List.Subset.refl _)) hl)

/-! ## Bound independence of `μ` -/

/-- `v_q(d) = 0` for `q > d ≥ 1`. -/
theorem val_big {q d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] lt d q) :
    Γ ⊢[PRAAx] val q d ≐ zero := by
  have hq2 : Γ ⊢[PRAAx] le two q := le_trans ((succ_monus_succ _ _).eqTrans (one_le_of_pos hd)) h
  have hq1 : Γ ⊢[PRAAx] q ≐ succ (pred q) := pos_of_two hq2
  refine val_unique hq2 hd (c := d) ((one_mul _).eqSymm.eqTrans (congrMul (pw_zero _).eqSymm (.eqRefl d))) ?_
  exact .impI (le_lt_absurd _ (dvd_le' hq1.wk Prf.hyp0 hd.wk) h.wk)

theorem om_tail {q d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] lt d q) :
    Γ ⊢[PRAAx] inst2 omB q d ≐ zero := by
  rw [inst2_om]
  exact (congrMul (.eqRefl _) ((congrSg (val_big hd h)).eqTrans sg_zero)).eqTrans
    (by ipra_ring)

theorem sq_tail {q d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (h : Γ ⊢[PRAAx] lt d q) :
    Γ ⊢[PRAAx] inst2 sqB q d ≐ zero := by
  rw [inst2_sq]
  exact (congrMul (.eqRefl _) ((congrSg ((congrMonus (val_big hd h) (.eqRefl _)).eqTrans (zero_monus _))).eqTrans
    sg_zero)).eqTrans (by ipra_ring)

theorem shift_pos {d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) :
    (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift d ≐ succ (pred (Syn.shift d)) := by
  simpa [Fm.shift, Syn.shift] using hd.shift

/-- `μ^±_N(d) = μ^±_{d+1}(d)` for `d ≥ 1` and `N ≥ d + 1`. -/
theorem mu_bound {N d : PTm n} (hd : Γ ⊢[PRAAx] d ≐ succ (pred d)) (hN : Γ ⊢[PRAAx] le (succ d) N) :
    Γ ⊢[PRAAx] (muP N d ≐ muP (succ d) d) ⋏ (muN N d ≐ muN (succ d) d) := by
  have hd' := shift_pos hd
  have o : Γ ⊢[PRAAx] om N d ≐ om (succ d) d :=
    sum_ext omB (fun Δ a hs hl => om_tail (hd'.weaken hs) hl) hN
  have s : Γ ⊢[PRAAx] sq N d ≐ sq (succ d) d :=
    sum_ext sqB (fun Δ a hs hl => sq_tail (hd'.weaken hs) hl) hN
  have es := congrEqb' s (.eqRefl zero)
  have ro := congrAp2 remF o (.eqRefl two)
  exact .andI (congrMul es (congrEqb' ro (.eqRefl _))) (congrMul es (congrEqb' ro (.eqRefl _)))

/-! ## Cancellation with free bounds -/

/-- `[d ≥ 1][d ∣ k] μ⁺_N(d)` with the pair parameter `⟨N, k⟩`. -/
abbrev GP : PTm 2 := (sg (var 0) * eqb (rem (sndT (var 1)) (var 0)) zero) * muP (fstT (var 1)) (var 0)
/-- `[d ≥ 1][d ∣ k] μ⁻_N(d)`. -/
abbrev GN : PTm 2 := (sg (var 0) * eqb (rem (sndT (var 1)) (var 0)) zero) * muN (fstT (var 1)) (var 0)

theorem inst2_GP (d y : PTm n) :
    inst2 GP d y = (sg d * eqb (rem (sndT y) d) zero) * muP (fstT y) d := by simp [inst2]
theorem inst2_GN (d y : PTm n) :
    inst2 GN d y = (sg d * eqb (rem (sndT y) d) zero) * muN (fstT y) d := by simp [inst2]

theorem congrMu {N N' d : PTm n} (h : Γ ⊢[PRAAx] N ≐ N') :
    Γ ⊢[PRAAx] (muP N d ≐ muP N' d) ⋏ (muN N d ≐ muN N' d) := by
  have es := congrEqb' (congrAp2 (sumF sqB) h (.eqRefl d)) (.eqRefl zero)
  have ro := congrAp2 remF (congrAp2 (sumF omB) h (.eqRefl d)) (.eqRefl two)
  exact .andI (congrMul es (congrEqb' ro (.eqRefl _))) (congrMul es (congrEqb' ro (.eqRefl _)))

theorem G_at (d N k : PTm n) :
    Γ ⊢[PRAAx] (inst2 GP d (pairT N k) ≐ (sg d * eqb (rem k d) zero) * muP N d) ⋏
      (inst2 GN d (pairT N k) ≐ (sg d * eqb (rem k d) zero) * muN N d) := by
  rw [inst2_GP, inst2_GN]
  have c := congrMu (Γ := Γ) (d := d) (fst_pair N k)
  have e : Γ ⊢[PRAAx] sg d * eqb (rem (sndT (pairT N k)) d) zero ≐ sg d * eqb (rem k d) zero :=
    congrMul (.eqRefl (sg d)) (congrEqb' (congrAp2 remF (snd_pair N k) (.eqRefl d)) (.eqRefl zero))
  exact .andI (congrMul e (Prf.andE₁ c)) (congrMul e (Prf.andE₂ c))

/-- Beyond `k`, no divisor of `k ≥ 1`. -/
theorem G_tail {d N k : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (h : Γ ⊢[PRAAx] lt k d) :
    Γ ⊢[PRAAx] (inst2 GP d (pairT N k) ≐ zero) ⋏ (inst2 GN d (pairT N k) ≐ zero) := by
  have w := natEq (eq_add_of_le h)
  have hd : Γ ⊢[PRAAx] d ≐ succ (pred d) :=
    eq_succ_pred (y := k + monus d (succ k)) (by apply deriveNat; ipra_simps; linear_combination w)
  have r : Γ ⊢[PRAAx] rem k d ≐ k := rem_eq' hd (q := zero) (by ipra_ring) h
  have z : Γ ⊢[PRAAx] eqb (rem k d) zero ≐ zero :=
    (congrEqb' r (.eqRefl _)).eqTrans (eqb_of_ne (.impI (succ_ne_zero' _ (hk.wk.eqSymm.eqTrans Prf.hyp0))))
  have zz : ∀ {X : PTm n}, Γ ⊢[PRAAx] (sg d * eqb (rem k d) zero) * X ≐ zero := fun {X} =>
    zero_mul_l ((congrMul (.eqRefl _) z).eqTrans (by ipra_ring)) X
  have g := G_at (Γ := Γ) d N k
  exact .andI ((Prf.andE₁ g).eqTrans zz) ((Prf.andE₂ g).eqTrans zz)

/-- Converting to the fixed bound `k + 1` below `k + 1`. -/
theorem G_fix {d N k : PTm n} (hN : Γ ⊢[PRAAx] le (succ k) N) (h : Γ ⊢[PRAAx] lt d (succ k)) :
    Γ ⊢[PRAAx] (inst2 GP d (pairT N k) ≐ inst2 PB d k) ⋏ (inst2 GN d (pairT N k) ≐ inst2 NB d k) := by
  rw [inst2_PB, inst2_NB]
  have g := G_at (Γ := Γ) d N k
  refine .orE (zero_or_succ d) ?_ ?_
  · have h0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] d ≐ zero := Prf.hyp0
    have s0 : ((d ≐ zero) :: Γ) ⊢[PRAAx] sg d ≐ zero := (congrSg h0).eqTrans sg_zero
    have zz : ∀ {X Y : PTm n}, ((d ≐ zero) :: Γ) ⊢[PRAAx] (sg d * Y) * X ≐ zero := fun {X Y} =>
      zero_mul_l (zero_mul_l s0 Y) X
    exact .andI ((Prf.andE₁ g).wk.eqTrans (zz.eqTrans zz.eqSymm)) ((Prf.andE₂ g).wk.eqTrans (zz.eqTrans zz.eqSymm))
  · let C : List (Fm PTm n) := (d ≐ succ (pred d)) :: Γ
    have hd : C ⊢[PRAAx] d ≐ succ (pred d) := Prf.hyp0
    have hdk : C ⊢[PRAAx] le (succ d) (succ k) := (succ_monus_succ _ _).eqTrans
      ((succ_monus_succ _ _).eqSymm.eqTrans h.wk)
    have b₁ := mu_bound hd (le_trans hdk hN.wk)
    have b₂ := mu_bound hd hdk
    exact .andI ((Prf.andE₁ g).wk.eqTrans (congrMul (.eqRefl _) ((Prf.andE₁ b₁).eqTrans (Prf.andE₁ b₂).eqSymm)))
      ((Prf.andE₂ g).wk.eqTrans (congrMul (.eqRefl _) ((Prf.andE₂ b₁).eqTrans (Prf.andE₂ b₂).eqSymm)))

/-- `∑_{d ∣ k} μ(d) = [k = 1]` with any prime bound `N > k` and any range `K > k`. -/
theorem cancel_gen {k N K : PTm n} (hk : Γ ⊢[PRAAx] k ≐ succ (pred k)) (hN : Γ ⊢[PRAAx] le (succ k) N)
    (hK : Γ ⊢[PRAAx] le (succ k) K) :
    Γ ⊢[PRAAx] ap2 (sumF GP) K (pairT N k) ≐ ap2 (sumF GN) K (pairT N k) + eqb k one := by
  have hk' := shift_pos hk
  have cP : Γ ⊢[PRAAx] ap2 (sumF GP) K (pairT N k) ≐ ap2 (sumF GP) (succ k) (pairT N k) :=
    sum_ext GP (fun Δ a hs hl => by rw [shift_pairT]; exact Prf.andE₁ (G_tail (hk'.weaken hs) hl)) hK
  have cN : Γ ⊢[PRAAx] ap2 (sumF GN) K (pairT N k) ≐ ap2 (sumF GN) (succ k) (pairT N k) :=
    sum_ext GN (fun Δ a hs hl => by rw [shift_pairT]; exact Prf.andE₂ (G_tail (hk'.weaken hs) hl)) hK
  have hN' : (Γ.map Fm.shift) ⊢[PRAAx] le (succ (Syn.shift k)) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using hN.shift
  have fP : Γ ⊢[PRAAx] ap2 (sumF GP) (succ k) (pairT N k) ≐ ap2 (sumF PB) (succ k) k := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    have hs : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
    exact Prf.andE₁ (G_fix hN'.wk (by rw [← hs]; exact Prf.hyp0))
  have fN : Γ ⊢[PRAAx] ap2 (sumF GN) (succ k) (pairT N k) ≐ ap2 (sumF NB) (succ k) k := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_pairT]
    have hs : Syn.shift (succ k) = succ (Syn.shift k) := by simp [Syn.shift]
    exact Prf.andE₂ (G_fix hN'.wk (by rw [← hs]; exact Prf.hyp0))
  have core : Γ ⊢[PRAAx] ap2 (sumF PB) (succ k) k ≐ ap2 (sumF NB) (succ k) k + eqb k one := by
    refine .orE (lt_or_le one k) ?_ ?_
    · have h2 : (lt one k :: Γ) ⊢[PRAAx] le two k := Prf.hyp0
      have ne : (lt one k :: Γ) ⊢[PRAAx] eqb k one ≐ zero :=
        eqb_of_ne (.impI (not_succ_le_self one _ (le_congr (.eqRefl _) Prf.hyp0 h2.wk)))
      exact (mobius_cancel h2).eqTrans ((add_zero _).eqSymm.eqTrans (congrAdd (.eqRefl _) ne.eqSymm))
    · let C : List (Fm PTm n) := le k one :: Γ
      have e1 : C ⊢[PRAAx] k ≐ one := le_antisymm Prf.hyp0 (one_le_of_pos hk.wk)
      have m1 := mobius_one (Γ := C)
      have aP : C ⊢[PRAAx] ap2 (sumF PB) (succ k) k ≐ ap2 (sumF PB) (succ one) one :=
        congrAp2 (sumF PB) (congrSucc e1) e1
      have aN : C ⊢[PRAAx] ap2 (sumF NB) (succ k) k ≐ ap2 (sumF NB) (succ one) one :=
        congrAp2 (sumF NB) (congrSucc e1) e1
      exact aP.eqTrans ((Prf.andE₁ m1).eqTrans ((zero_add _).eqSymm.eqTrans
        (congrAdd (aN.eqTrans (Prf.andE₂ m1)).eqSymm (eqb_of_eq e1).eqSymm)))
  exact cP.eqTrans (fP.eqTrans (core.eqTrans (congrAdd (fN.eqSymm.eqTrans cN.eqSymm) (.eqRefl _))))

end LeanProofs.IPRA.AnalyticNumberTheory.MobiusBounds
