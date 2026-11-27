import IPRADerivations.Foundations.CrtCoprime
import IPRADerivations.AnalyticNumberTheory.CoprimeModulus

/-!
# Finite continued fractions of rationals

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, `dio:cf-rational`:

  "Every nonnegative rational has a unique finite simple continued fraction whose last coefficient is at least `2`,
  unless there is just one coefficient. For `a/b`, `a ≥ 0, b > 0`, it can be computed in at most `b + 1` Euclidean
  stages, with every coefficient at most `a + b`." Proof: "Divide `a = a_0 b + r`. If `r = 0`, stop; otherwise
  replace `(a, b)` by `(b, r)` and repeat … Substitution backwards gives the continued fraction."

* `EA j`, `EB j`: the Euclidean pairs, `(EA 0, EB 0) = (a, b)`, `(EA (j+1), EB (j+1)) = (EB j, EA j mod EB j)`
  (simultaneous recursion, `Core/Pairing`); `cf j = ⌊EA j / EB j⌋` is the `j`-th coefficient;
* `Pc`, `Pc'`, `Qc`, `Qc'`: the continuants of the coefficients, `Pc j = p_{j−1}`, `Pc' j = p_{j−2}` with
  `p_k = cf k · p_{k−1} + p_{k−2}`, `p_{−1} = 1`, `p_{−2} = 0`, and `q` with `q_{−1} = 0`, `q_{−2} = 1`;
* `Z j = ∑_{i<j} [EB i = 0]`; **`invariant`**: while `Z j = 0`,
  `a = p_{j−1} EA j + p_{j−2} EB j`, `b = q_{j−1} EA j + q_{j−2} EB j` and `EB j + j ≤ b`
  (the packet's backward substitution, and the strict decrease of the remainders);
* **`cf_rational`**: for `b ≥ 1` the first stage `m` with `EB m = 0` satisfies `1 ≤ m ≤ b + 1`,
  `a = p_{m−1} g` and `b = q_{m−1} g` with `g = EA m ≥ 1`, so `a/b = p_{m−1}/q_{m−1}`, the continued fraction
  `[cf 0; cf 1, …, cf (m−1)]`;
* **`cf_le`**: every coefficient is at most `a + b`; **`cf_pos`**: `cf j ≥ 1` for `1 ≤ j < m` (`EB j < EA j`);
  **`cf_last`**: the last coefficient `cf (m − 1)` is at least `2` when `m ≥ 2`.

The uniqueness of the canonical expansion is not derived here.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.CfRational

open_ipra exports
open LeanProofs.IPRA.Foundations.CrtCoprime (left_zero right_zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem vec2 {m : ℕ} (σ : Fin m → PTm n) (u v : PTm m) :
    (fun k => Syn.subst σ ((![u, v] : Fin 2 → PTm m) k)) = ![Syn.subst σ u, Syn.subst σ v] := by
  funext k; fin_cases k <;> rfl

theorem congrE3 (t : PTm 3) {j j' a a' b b' : PTm n} (hj : Γ ⊢[PRAAx] j ≐ j') (ha : Γ ⊢[PRAAx] a ≐ a')
    (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx] Syn.subst ![j, a, b] t ≐ Syn.subst ![j', a', b'] t :=
  Prf.eqCongr t fun i => by
    fin_cases i
    · simpa using hj
    · simpa using ha
    · simpa using hb

/-! ## The Euclidean pairs -/

/-- Step variables: `0 = j`, `1 = A`, `2 = B`, `3 = a`, `4 = b`. -/
abbrev sA : PTm 5 := var 2
abbrev sB : PTm 5 := rem (var 1) (var 2)

abbrev EA (j a b : PTm n) : PTm n := sim₁ (var 0 : PTm 2) (var 1) sA sB j ![a, b]
abbrev EB (j a b : PTm n) : PTm n := sim₂ (var 0 : PTm 2) (var 1) sA sB j ![a, b]

theorem EA_zero (a b : PTm n) : Γ ⊢[PRAAx] EA zero a b ≐ a := by
  have h := sim₁_zero (Γ := Γ) (var 0 : PTm 2) (var 1) sA sB ![a, b]
  simpa [vec2] using h

theorem EB_zero (a b : PTm n) : Γ ⊢[PRAAx] EB zero a b ≐ b := by
  have h := sim₂_zero (Γ := Γ) (var 0 : PTm 2) (var 1) sA sB ![a, b]
  simpa [vec2] using h

theorem EA_succ (j a b : PTm n) : Γ ⊢[PRAAx] EA (succ j) a b ≐ EB j a b := by
  have h := sim₁_succ (Γ := Γ) (var 0 : PTm 2) (var 1) sA sB ![a, b] j
  simpa [vec2] using h

theorem EB_succ (j a b : PTm n) : Γ ⊢[PRAAx] EB (succ j) a b ≐ rem (EA j a b) (EB j a b) := by
  have h := sim₂_succ (Γ := Γ) (var 0 : PTm 2) (var 1) sA sB ![a, b] j
  simpa [vec2] using h

theorem congrEA_j {j j' a b : PTm n} (h : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] EA j a b ≐ EA j' a b := by
  have h' := congrE3 (EA (var 0) (var 1) (var 2) : PTm 3) h (.eqRefl a) (.eqRefl b)
  simpa [vec2] using h'

theorem congrEB_j {j j' a b : PTm n} (h : Γ ⊢[PRAAx] j ≐ j') : Γ ⊢[PRAAx] EB j a b ≐ EB j' a b := by
  have h' := congrE3 (EB (var 0) (var 1) (var 2) : PTm 3) h (.eqRefl a) (.eqRefl b)
  simpa [vec2] using h'

/-- The `j`-th coefficient `⌊EA j / EB j⌋`. -/
abbrev cf (j a b : PTm n) : PTm n := quo (EA j a b) (EB j a b)

/-! ## The continuants -/

/-- Step variables: `0 = j`, `1 = current`, `2 = previous`, `3 = a`, `4 = b`. -/
abbrev cS : PTm 5 := quo (EA (var 0) (var 3) (var 4)) (EB (var 0) (var 3) (var 4)) * var 1 + var 2
abbrev cS' : PTm 5 := var 1

abbrev Pc (j a b : PTm n) : PTm n := sim₁ (one : PTm 2) zero cS cS' j ![a, b]
abbrev Pc' (j a b : PTm n) : PTm n := sim₂ (one : PTm 2) zero cS cS' j ![a, b]
abbrev Qc (j a b : PTm n) : PTm n := sim₁ (zero : PTm 2) one cS cS' j ![a, b]
abbrev Qc' (j a b : PTm n) : PTm n := sim₂ (zero : PTm 2) one cS cS' j ![a, b]

theorem Pc_zero (a b : PTm n) : Γ ⊢[PRAAx] Pc zero a b ≐ one := by
  have h := sim₁_zero (Γ := Γ) (one : PTm 2) zero cS cS' ![a, b]
  simpa [vec2] using h

theorem Pc'_zero (a b : PTm n) : Γ ⊢[PRAAx] Pc' zero a b ≐ zero := by
  have h := sim₂_zero (Γ := Γ) (one : PTm 2) zero cS cS' ![a, b]
  simpa [vec2] using h

theorem Qc_zero (a b : PTm n) : Γ ⊢[PRAAx] Qc zero a b ≐ zero := by
  have h := sim₁_zero (Γ := Γ) (zero : PTm 2) one cS cS' ![a, b]
  simpa [vec2] using h

theorem Qc'_zero (a b : PTm n) : Γ ⊢[PRAAx] Qc' zero a b ≐ one := by
  have h := sim₂_zero (Γ := Γ) (zero : PTm 2) one cS cS' ![a, b]
  simpa [vec2] using h

theorem Pc_succ (j a b : PTm n) : Γ ⊢[PRAAx] Pc (succ j) a b ≐ cf j a b * Pc j a b + Pc' j a b := by
  have h := sim₁_succ (Γ := Γ) (one : PTm 2) zero cS cS' ![a, b] j
  simpa [vec2] using h

theorem Pc'_succ (j a b : PTm n) : Γ ⊢[PRAAx] Pc' (succ j) a b ≐ Pc j a b := by
  have h := sim₂_succ (Γ := Γ) (one : PTm 2) zero cS cS' ![a, b] j
  simpa [vec2] using h

theorem Qc_succ (j a b : PTm n) : Γ ⊢[PRAAx] Qc (succ j) a b ≐ cf j a b * Qc j a b + Qc' j a b := by
  have h := sim₁_succ (Γ := Γ) (zero : PTm 2) one cS cS' ![a, b] j
  simpa [vec2] using h

theorem Qc'_succ (j a b : PTm n) : Γ ⊢[PRAAx] Qc' (succ j) a b ≐ Qc j a b := by
  have h := sim₂_succ (Γ := Γ) (zero : PTm 2) one cS cS' ![a, b] j
  simpa [vec2] using h

/-! ## The invariant -/

/-- `[EB i = 0]`, over `0 = i`, `1 = ⟨a, b⟩`. -/
abbrev zB : PTm 2 := eqb (EB (var 0) (fstT (var 1)) (sndT (var 1))) zero

theorem inst2_z (i z : PTm n) : inst2 zB i z = eqb (EB i (fstT z) (sndT z)) zero := by
  simp [inst2, vec2]

theorem congrEB {a a' b b' : PTm n} (j : PTm n) (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] EB j a b ≐ EB j a' b' := by
  have h := congrE3 (EB (var 0) (var 1) (var 2) : PTm 3) (.eqRefl j) ha hb
  simpa [vec2] using h

theorem z_at (i a b : PTm n) : Γ ⊢[PRAAx] inst2 zB i (pairT a b) ≐ eqb (EB i a b) zero := by
  rw [inst2_z]
  exact AnalyticNumberTheory.Euler.congrEqb (congrEB i (fst_pair _ _) (snd_pair _ _)) (.eqRefl _)

/-- `Z j = ∑_{i<j} [EB i = 0]`. -/
abbrev Z (j a b : PTm n) : PTm n := ap2 (sumF zB) j (pairT a b)

/-- The invariant at `j`. -/
abbrev Inv (j a b : PTm n) : Fm PTm n :=
  (a ≐ Pc j a b * EA j a b + Pc' j a b * EB j a b) ⋏
    ((b ≐ Qc j a b * EA j a b + Qc' j a b * EB j a b) ⋏ le (EB j a b + j) b)

theorem inv_zero (a b : PTm n) : Γ ⊢[PRAAx] Inv zero a b := by
  have e1 := natEq (Pc_zero (Γ := Γ) a b); have e2 := natEq (Pc'_zero (Γ := Γ) a b)
  have e3 := natEq (Qc_zero (Γ := Γ) a b); have e4 := natEq (Qc'_zero (Γ := Γ) a b)
  have e5 := natEq (EA_zero (Γ := Γ) a b); have e6 := natEq (EB_zero (Γ := Γ) a b)
  refine .andI ?_ (.andI ?_ ?_)
  · ipra_lc -(𝔞 (EA zero a b)) * e1 - 𝔞 (EB zero a b) * e2 - e5
  · ipra_lc -(𝔞 (EA zero a b)) * e3 - 𝔞 (EB zero a b) * e4 - e6
  · exact le_congr (.eqRefl _) ((congrAdd (EB_zero a b) (.eqRefl _)).eqTrans (add_zero _)) (le_refl _)

theorem inv_alg {a P P' E E' A B Q R c : PTm n} (h : Γ ⊢[PRAAx] a ≐ P * A + P' * B)
    (hP : Γ ⊢[PRAAx] Q ≐ c * P + P') (hP' : Γ ⊢[PRAAx] R ≐ P) (hE : Γ ⊢[PRAAx] E ≐ B)
    (hE' : Γ ⊢[PRAAx] E' ≐ rem A B) (hd : Γ ⊢[PRAAx] A ≐ B * c + rem A B) :
    Γ ⊢[PRAAx] a ≐ Q * E + R * E' := by
  ipra_lc natEq h - 𝔞 E * natEq hP - 𝔞 E' * natEq hP' - (𝔞 c * 𝔞 P + 𝔞 P') * natEq hE - 𝔞 P * natEq hE' +
    𝔞 P * natEq hd

theorem dec_alg {E B j b r : PTm n} (h : Γ ⊢[PRAAx] le (B + j) b) (hr : Γ ⊢[PRAAx] lt r B)
    (hE : Γ ⊢[PRAAx] E ≐ r) : Γ ⊢[PRAAx] le (E + succ j) b := by
  have x := natEq hE
  ipra_le sl h + sl hr with x

/-- The step of the invariant at a positive divisor `EB j`. -/
theorem inv_step {j a b : PTm n} (hI : Γ ⊢[PRAAx] Inv j a b)
    (hB : Γ ⊢[PRAAx] EB j a b ≐ succ (pred (EB j a b))) : Γ ⊢[PRAAx] Inv (succ j) a b := by
  have hd : Γ ⊢[PRAAx] EA j a b ≐ EB j a b * cf j a b + rem (EA j a b) (EB j a b) := div_eq hB
  refine .andI (inv_alg (Prf.andE₁ hI) (Pc_succ j a b) (Pc'_succ j a b) (EA_succ j a b) (EB_succ j a b) hd)
    (.andI (inv_alg (Prf.andE₁ (Prf.andE₂ hI)) (Qc_succ j a b) (Qc'_succ j a b) (EA_succ j a b) (EB_succ j a b) hd)
      (dec_alg (Prf.andE₂ (Prf.andE₂ hI)) (rem_lt' hB _) (EB_succ j a b)))

theorem pos_of_eqb {x : PTm n} (h : Γ ⊢[PRAAx] eqb x zero ≐ zero) : Γ ⊢[PRAAx] x ≐ succ (pred x) := by
  refine .orE (zero_or_succ x) ?_ Prf.hyp0
  exact .botE _ (succ_ne_zero (a := zero) ((eqb_of_eq Prf.hyp0).eqSymm.eqTrans h.wk))

theorem inv_succ {j a b : PTm n} (ih : Γ ⊢[PRAAx] (Z j a b ≐ zero) ⟶ Inv j a b)
    (h : Γ ⊢[PRAAx] Z (succ j) a b ≐ zero) : Γ ⊢[PRAAx] Inv (succ j) a b := by
  have hs := (sum_succ' zB j (pairT a b)).eqSymm.eqTrans h
  have hz := (z_at j a b).eqSymm.eqTrans (right_zero hs)
  exact inv_step (Prf.impE ih (left_zero hs)) (pos_of_eqb hz)

/-- **The invariant**: while no remainder has vanished (`Z j = 0`), the backward substitution and the decrease of
the remainders hold. -/
theorem invariant (a b j : PTm n) : Γ ⊢[PRAAx] (Z j a b ≐ zero) ⟶ Inv j a b := by
  have hall : Γ ⊢[PRAAx] Fm.all ((Z (var 0) (Syn.shift a) (Syn.shift b) ≐ zero) ⟶
      Inv (var 0) (Syn.shift a) (Syn.shift b)) := by
    ipra_qfind (⟨trivial, trivial, trivial, le_QF _ _⟩) [subst_le, subst_ap2, subst_pairT, subst_sim₁, subst_sim₂, vec2]
    · exact .impI (by simpa using inv_zero (Γ := (Z zero a b ≐ zero) :: Γ) a b)
    · exact .impI (inv_succ Prf.hyp1 Prf.hyp0)
  have h2 := Prf.allE j hall
  simp only [Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_le, subst_ap2, subst_pairT, PTm.subst_add, PTm.subst_mul,
    subst_sim₁, subst_sim₂, vec2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-! ## The expansion -/

/-- The search body `EB i`, over `0 = i`, `1 = ⟨a, b⟩`. -/
abbrev fB : PTm 2 := EB (var 0) (fstT (var 1)) (sndT (var 1))

theorem f_at (i a b : PTm n) : Γ ⊢[PRAAx] inst2 fB i (pairT a b) ≐ EB i a b := by
  have e : inst2 fB i (pairT a b) = EB i (fstT (pairT a b)) (sndT (pairT a b)) := by simp [inst2, vec2]
  rw [e]; exact congrEB i (fst_pair _ _) (snd_pair _ _)

/-- The first stage with a vanishing remainder, searched below `b + 2`. -/
abbrev M (a b : PTm n) : PTm n := Search.mu fB (succ (succ b)) (pairT a b)

/-- No remainder vanishes before the stage `M`. -/
theorem Z_M (a b : PTm n) : Γ ⊢[PRAAx] Z (M a b) a b ≐ zero := by
  refine sum_zero_of_bounded zB (pairT a b) (M a b) (.allI (.impI ?_))
  have sP : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by simp [Syn.shift]
  have sM : Syn.shift (M a b) = M (Syn.shift a) (Syn.shift b) := by simp [Syn.shift]
  rw [sP]
  have hlt : (lt (var 0) (Syn.shift (M a b)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (M (Syn.shift a) (Syn.shift b)) := by
    rw [← sM]; exact Prf.hyp0
  have ne := Search.search_minimal (f := fB) hlt
  have ne' : (lt (var 0) (Syn.shift (M a b)) :: Γ.map Fm.shift) ⊢[PRAAx] neg (EB (var 0) (Syn.shift a) (Syn.shift b) ≐ zero) :=
    .impI (.impE ne.wk ((f_at _ _ _).eqTrans Prf.hyp0))
  exact (z_at _ _ _).eqTrans (eqb_of_ne ne')

theorem le_zero_absurd' {x b : PTm n} (φ : Fm PTm n) (h : Γ ⊢[PRAAx] le (x + succ b) b) : Γ ⊢[PRAAx] φ := by
  have bad : Γ ⊢[PRAAx] le one zero := by ipra_le sl h + 𝔞 x
  exact lt_zero_absurd _ bad

/-- The search succeeds: `M < b + 2` and `EB M = 0`. -/
theorem M_found (a b : PTm n) : Γ ⊢[PRAAx] lt (M a b) (succ (succ b)) ⋏ (EB (M a b) a b ≐ zero) := by
  have s := Search.search_spec (Γ := Γ) (f := fB) (succ (succ b)) zero (pairT a b)
  refine .orE (lt_or_eq_of_le (Prf.andE₁ s)) ?_ ?_
  · have hlt : (lt (M a b) (succ (succ b)) :: Γ) ⊢[PRAAx] lt (M a b) (succ (succ b)) := Prf.hyp0
    exact .andI hlt ((f_at _ _ _).eqSymm.eqTrans (.impE (Prf.andE₁ (Prf.andE₂ s)).wk hlt))
  · -- `M = b + 2`: then no remainder vanished up to `b + 1`, contradicting the decrease
    have e : ((M a b ≐ succ (succ b)) :: Γ) ⊢[PRAAx] M a b ≐ succ (succ b) := Prf.hyp0
    have Zb : ((M a b ≐ succ (succ b)) :: Γ) ⊢[PRAAx] Z (succ (succ b)) a b ≐ zero :=
      (congrAp2 (sumF zB) e.eqSymm (.eqRefl _)).eqTrans (Z_M a b)
    have hs := (sum_succ' zB (succ b) (pairT a b)).eqSymm.eqTrans Zb
    have I := Prf.impE (invariant (Γ := (M a b ≐ succ (succ b)) :: Γ) a b (succ b)) (left_zero hs)
    exact le_zero_absurd' _ (Prf.andE₂ (Prf.andE₂ I))

/-- `M ≥ 1` for `b ≥ 1`: the first remainder is `b`. -/
theorem M_pos {a b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) : Γ ⊢[PRAAx] M a b ≐ succ (pred (M a b)) := by
  refine .orE (zero_or_succ (M a b)) ?_ Prf.hyp0
  have e : ((M a b ≐ zero) :: Γ) ⊢[PRAAx] M a b ≐ zero := Prf.hyp0
  have z := Prf.andE₂ (M_found (Γ := (M a b ≐ zero) :: Γ) a b)
  exact .botE _ (succ_ne_zero (a := pred b) (hb.wk.eqSymm.eqTrans ((EB_zero a b).eqSymm.eqTrans
    ((congrEB_j e.eqSymm).eqTrans z))))
theorem val_alg {a P P' A B : PTm n} (h : Γ ⊢[PRAAx] a ≐ P * A + P' * B) (hB : Γ ⊢[PRAAx] B ≐ zero) :
    Γ ⊢[PRAAx] a ≐ P * A := by
  ipra_lc natEq h + 𝔞 P' * natEq hB

/-- **`dio:cf-rational`, existence**: for `b ≥ 1`, the Euclidean stages stop at `m = M a b` with `1 ≤ m ≤ b + 1`,
and `a = p_{m−1} g`, `b = q_{m−1} g` with `g = EA m ≥ 1`: `a/b = p_{m−1}/q_{m−1} = [cf 0; cf 1, …, cf (m−1)]`. -/
theorem cf_rational {a b : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] (le (M a b) (succ b) ⋏ (M a b ≐ succ (pred (M a b)))) ⋏
      ((a ≐ Pc (M a b) a b * EA (M a b) a b) ⋏ (b ≐ Qc (M a b) a b * EA (M a b) a b)) := by
  have F := M_found (Γ := Γ) a b
  have I := Prf.impE (invariant (Γ := Γ) a b (M a b)) (Z_M a b)
  have hlt : Γ ⊢[PRAAx] le (M a b) (succ b) := (succ_monus_succ _ _).eqSymm.eqTrans (Prf.andE₁ F)
  exact .andI (.andI hlt (M_pos hb))
    (.andI (val_alg (Prf.andE₁ I) (Prf.andE₂ F)) (val_alg (Prf.andE₁ (Prf.andE₂ I)) (Prf.andE₂ F)))

/-! ## The coefficients -/

/-- The remainders below the stopping stage are positive. -/
theorem EB_pos {a b j : PTm n} (hj : Γ ⊢[PRAAx] lt j (M a b)) : Γ ⊢[PRAAx] EB j a b ≐ succ (pred (EB j a b)) := by
  have ne := Search.search_minimal (f := fB) hj
  refine .orE (zero_or_succ (EB j a b)) ?_ Prf.hyp0
  exact .botE _ (.impE ne.wk ((f_at _ _ _).eqTrans Prf.hyp0))

theorem Z_below {a b j : PTm n} (hj : Γ ⊢[PRAAx] le j (M a b)) : Γ ⊢[PRAAx] Z j a b ≐ zero := by
  have s := AnalyticNumberTheory.SumReindex.sum_le_bound (Γ := Γ) zB (x := pairT a b) hj
  exact (monus_zero _).eqSymm.eqTrans (le_congr (.eqRefl _) (Z_M a b) s)

theorem quo_le_self' {A B : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) : Γ ⊢[PRAAx] le (quo A B) A :=
  Division.quo_le_self hB

/-- **Every coefficient is at most `a + b`.** -/
theorem cf_le {a b j : PTm n} (hj : Γ ⊢[PRAAx] lt j (M a b)) : Γ ⊢[PRAAx] le (cf j a b) (a + b) := by
  have hB := EB_pos hj
  refine le_trans (quo_le_self' hB) ?_
  refine .orE (zero_or_succ j) ?_ ?_
  · have e : ((j ≐ zero) :: Γ) ⊢[PRAAx] EA j a b ≐ a := (congrEA_j Prf.hyp0).eqTrans (EA_zero a b)
    exact le_congr e.eqSymm (.eqRefl _) (le_add_right a b)
  · let C : List (Fm PTm n) := (j ≐ succ (pred j)) :: Γ
    have hj' : C ⊢[PRAAx] le (pred j) (M a b) :=
      le_trans (le_succ_self _) (le_congr ((Prf.hyp0 : C ⊢[PRAAx] j ≐ succ (pred j))) (.eqRefl _)
        (le_trans (le_succ_self _) hj.wk))
    have I := Prf.impE (invariant (Γ := C) a b (pred j)) (Z_below hj')
    have eA : C ⊢[PRAAx] EA j a b ≐ EB (pred j) a b := (congrEA_j Prf.hyp0).eqTrans (EA_succ _ a b)
    have l := Prf.andE₂ (Prf.andE₂ I)
    exact le_congr eA.eqSymm (.eqRefl _) (le_trans (le_trans (le_add_right _ _) l) (le_add_left b a))

/-! ## Later coefficients -/

/-- For `1 ≤ j < m`: `EB j < EA j`, since `EA j = EB (j − 1)` and `EB j` is a remainder modulo it. -/
theorem EB_lt_EA {a b j : PTm n} (hj : Γ ⊢[PRAAx] lt j (M a b)) (h1 : Γ ⊢[PRAAx] j ≐ succ (pred j)) :
    Γ ⊢[PRAAx] lt (EB j a b) (EA j a b) := by
  have hp : Γ ⊢[PRAAx] lt (pred j) (M a b) :=
    le_congr h1 (.eqRefl _) (le_trans (le_succ_self _) hj)
  have hB := EB_pos hp
  have eA : Γ ⊢[PRAAx] EA j a b ≐ EB (pred j) a b := (congrEA_j h1).eqTrans (EA_succ _ a b)
  have eB : Γ ⊢[PRAAx] EB j a b ≐ rem (EA (pred j) a b) (EB (pred j) a b) := (congrEB_j h1).eqTrans (EB_succ _ a b)
  exact lt_congr eB.eqSymm eA.eqSymm (rem_lt' hB _)

/-- `B ≤ A` with `B ≥ 1` gives `⌊A/B⌋ ≥ 1`. -/
theorem quo_pos {A B : PTm n} (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (h : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] le one (quo A B) :=
  Division.le_quo_of_mul_le hB (le_congr (Common.mul_one_right _).eqSymm (.eqRefl _) h)

/-- **The later coefficients are positive**: `cf j ≥ 1` for `1 ≤ j < m`. -/
theorem cf_pos {a b j : PTm n} (hj : Γ ⊢[PRAAx] lt j (M a b)) (h1 : Γ ⊢[PRAAx] j ≐ succ (pred j)) :
    Γ ⊢[PRAAx] le one (cf j a b) :=
  quo_pos (EB_pos hj) (le_trans (le_succ_self _) (EB_lt_EA hj h1))

/-- **The last coefficient is at least `2`** when there are at least two coefficients (`m ≥ 2`). -/
theorem cf_last {a b : PTm n} (h2 : Γ ⊢[PRAAx] le two (M a b)) :
    Γ ⊢[PRAAx] le two (cf (pred (M a b)) a b) := by
  have eM : Γ ⊢[PRAAx] M a b ≐ succ (pred (M a b)) :=
    AnalyticNumberTheory.Primes.eq_succ_pred (AnalyticNumberTheory.Smooth.K_eq h2)
  have hj : Γ ⊢[PRAAx] lt (pred (M a b)) (M a b) := le_congr (.eqRefl _) eM.eqSymm (le_refl _)
  have h1 : Γ ⊢[PRAAx] pred (M a b) ≐ succ (pred (pred (M a b))) := by
    have x := natEq (eq_add_of_le h2)
    refine AnalyticNumberTheory.Primes.eq_succ_pred (y := monus (M a b) two) ?_
    ipra_lc x - natEq eM
  have hB := EB_pos hj
  have lt' := EB_lt_EA hj h1
  -- the last remainder vanishes: `EA j = EB j · cf j`
  have z : Γ ⊢[PRAAx] rem (EA (pred (M a b)) a b) (EB (pred (M a b)) a b) ≐ zero :=
    (EB_succ _ a b).eqSymm.eqTrans ((congrEB_j eM.eqSymm).eqTrans (Prf.andE₂ (M_found a b)))
  have d := Coprime.eq_of_dvd' hB z
  refine AnalyticNumberTheory.CoprimeModulus.two_le_of_ne (cf_pos hj h1) (.impI ?_)
  have e1 : ((cf (pred (M a b)) a b ≐ one) :: Γ) ⊢[PRAAx] EA (pred (M a b)) a b ≐ EB (pred (M a b)) a b :=
    d.wk.eqTrans ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (by ipra_ring))
  exact lt_irrefl _ _ (lt_congr (.eqRefl _) e1 lt'.wk)

end LeanProofs.IPRA.DiophantineNumberTheory.CfRational
