import IPRADerivations.DiophantineNumberTheory.FractionSeparation
import IPRADerivations.Foundations.InjectionCount
import IPRADerivations.DiophantineNumberTheory.QuarticStep

/-!
# Counting separated reduced fractions in an interval (`hurwitz_khinchin_ipra`, (K3), (K9))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`: "Distinct reduced fractions with
denominators at most `Q` are separated by at least `Q⁻²` … In an interval of length `L/2` this gives at
most `LQ²/2 + 1` fractions", and in (K9) "Separation at scale `ℓ` bounds the number of such centers by
`(|I| + 2r_ℓ)4^ℓ + 1`".

For `Q`, `P ≥ 1`, `W ≥ 1` and the closed interval `[u/W, v/W]`, index the pairs `(q, p)`, `q ≤ Q`, `p < P`,
by `i = qP + p < (Q + 1)P`. Then (`fraction_count`)

  `#{i : 1 ≤ q ≤ Q, gcd(p, q) = 1, u/W ≤ p/q ≤ v/W} ≤ ⌊Q²v/W⌋ − ⌊Q²u/W⌋ + 1`,

which is at most `(v − u)Q²/W + 1`: the interval of length `λ = (v − u)/W` contains at most `λQ² + 1`
reduced fractions with denominators at most `Q`. The proof applies `InjectionCount.injection_count` to
`i ↦ ⌊Q²p/q⌋ − ⌊Q²u/W⌋`: two different indices satisfying the conditions are different reduced pairs, so
their floors differ (`FractionSeparation.floor_inj`, `cl_zero`), and every floor lies in the range
(`floor_mono`, `vl_zero`). The conditions are packed into one violation sum `S(i)` with `c(i) = [S(i) = 0]`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.FractionCount

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Topology.StaggeredGrids (eqb01' eq_of_eqb congrEqb')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open LeanProofs.IPRA.AnalyticNumberTheory.SumReindex (le_quo_of_mul_le)
open LeanProofs.IPRA.DiophantineNumberTheory.FractionSeparation (floor_inj)
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.InjectionCount (coll viol rowCB clB vB sgB inst2_clB inst2_vB inst2_rowCB
  injection_count)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Arithmetic -/

theorem pos_of_le_one {q : PTm n} (h : Γ ⊢[PRAAx] le one q) : Γ ⊢[PRAAx] q ≐ succ (pred q) := by
  have e := natEq (eq_add_of_le h)
  have h1 : Γ ⊢[PRAAx] q ≐ succ (monus q one) := by apply deriveNat; ipra_simps; linear_combination e
  exact h1.eqTrans (congrSucc ((pred_succ _).eqSymm.eqTrans (congrPred h1.eqSymm)))

/-- `a/b ≤ c/d` (`a d ≤ c b`) gives `⌊Fa/b⌋ ≤ ⌊Fc/d⌋` for `b, d ≥ 1`. -/
theorem floor_mono {a b c d F : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) (hd : Γ ⊢[PRAAx] d ≐ succ (pred d))
    (h : Γ ⊢[PRAAx] le (a * d) (c * b)) : Γ ⊢[PRAAx] le (quo (F * a) b) (quo (F * c) d) := by
  have dm := div_mod_at (Γ := Γ) (x := F * a) hb
  have e := natEq (Prf.andE₁ dm)
  refine le_quo_of_mul_le hd (cancel_le hb ?_)
  ipra_le 𝔞 F * sl h + 𝔞 d * 𝔞 (rem (F * a) b) with 𝔞 d * e

theorem monus_mono {a b c : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (monus a c) (monus b c) := by
  refine .orE (lt_or_le a c) ?_ ?_
  · exact le_congr (le_trans (le_succ_self a) Prf.hyp0 : ((lt a c) :: Γ) ⊢[PRAAx] monus a c ≐ zero).eqSymm
      (.eqRefl _) (zero_le _)
  · let Δ : List (Fm PTm n) := le c a :: Γ
    have hca : Δ ⊢[PRAAx] le c a := Prf.hyp0
    have h' : Δ ⊢[PRAAx] le a b := h.wk
    have e1 := natEq (eq_add_of_le hca)
    have e2 := natEq (eq_add_of_le (le_trans hca h'))
    ipra_le sl h' with e2 - e1

theorem monus_cancel {a b c : PTm n} (ha : Γ ⊢[PRAAx] le c a) (hb : Γ ⊢[PRAAx] le c b)
    (h : Γ ⊢[PRAAx] monus a c ≐ monus b c) : Γ ⊢[PRAAx] a ≐ b := by
  have e1 := natEq (eq_add_of_le ha)
  have e2 := natEq (eq_add_of_le hb)
  have e3 := natEq h
  apply deriveNat; ipra_simps
  linear_combination e1 - e2 + e3

/-! ## The conditions -/

/-- The violation sum of `(q, p)`: zero iff `1 ≤ q ≤ Q`, `gcd(p, q) = 1`, `uq ≤ Wp ≤ vq`. -/
abbrev SV (q p Q u v W : PTm n) : PTm n :=
  monus one q + monus q Q + (monus (gcd p q) one + monus one (gcd p q)) + monus (u * q) (W * p) + monus (W * p) (v * q)

theorem facts {q p Q u v W : PTm n} (h : Γ ⊢[PRAAx] SV q p Q u v W ≐ zero) :
    Γ ⊢[PRAAx] le one q ⋏ (le q Q ⋏ ((gcd p q ≐ one) ⋏ (le (u * q) (W * p) ⋏ le (W * p) (v * q)))) := by
  have e := natEq h
  have z : ∀ {t : PTm n}, (Γ ⊢[PRAAx] le t (SV q p Q u v W)) → (Γ ⊢[PRAAx] t ≐ zero) := fun ht =>
    le_antisymm (le_congr (.eqRefl _) h ht) (zero_le _)
  have a1 : Γ ⊢[PRAAx] monus one q ≐ zero := z (by ipra_le 𝔞 (monus q Q) + 𝔞 (monus (gcd p q) one) +
    𝔞 (monus one (gcd p q)) + 𝔞 (monus (u * q) (W * p)) + 𝔞 (monus (W * p) (v * q)))
  have a2 : Γ ⊢[PRAAx] monus q Q ≐ zero := z (by ipra_le 𝔞 (monus one q) + 𝔞 (monus (gcd p q) one) +
    𝔞 (monus one (gcd p q)) + 𝔞 (monus (u * q) (W * p)) + 𝔞 (monus (W * p) (v * q)))
  have a3 : Γ ⊢[PRAAx] monus (gcd p q) one ≐ zero := z (by ipra_le 𝔞 (monus one q) + 𝔞 (monus q Q) +
    𝔞 (monus one (gcd p q)) + 𝔞 (monus (u * q) (W * p)) + 𝔞 (monus (W * p) (v * q)))
  have a4 : Γ ⊢[PRAAx] monus one (gcd p q) ≐ zero := z (by ipra_le 𝔞 (monus one q) + 𝔞 (monus q Q) +
    𝔞 (monus (gcd p q) one) + 𝔞 (monus (u * q) (W * p)) + 𝔞 (monus (W * p) (v * q)))
  have a5 : Γ ⊢[PRAAx] monus (u * q) (W * p) ≐ zero := z (by ipra_le 𝔞 (monus one q) + 𝔞 (monus q Q) +
    𝔞 (monus (gcd p q) one) + 𝔞 (monus one (gcd p q)) + 𝔞 (monus (W * p) (v * q)))
  have a6 : Γ ⊢[PRAAx] monus (W * p) (v * q) ≐ zero := z (by ipra_le 𝔞 (monus one q) + 𝔞 (monus q Q) +
    𝔞 (monus (gcd p q) one) + 𝔞 (monus one (gcd p q)) + 𝔞 (monus (u * q) (W * p)))
  exact .andI a1 (.andI a2 (.andI (le_antisymm a3 a4) (.andI a5 a6)))

/-! ## Bodies over `i` and `x = ⟨⟨Q, P⟩, ⟨⟨u, v⟩, W⟩⟩` -/

abbrev xQ (x : PTm n) : PTm n := fstT (fstT x)
abbrev xP (x : PTm n) : PTm n := sndT (fstT x)
abbrev xu (x : PTm n) : PTm n := fstT (fstT (sndT x))
abbrev xv (x : PTm n) : PTm n := sndT (fstT (sndT x))
abbrev xW (x : PTm n) : PTm n := sndT (sndT x)

/-- `c(i) = [S(i) = 0]`. -/
abbrev cB : PTm 2 :=
  eqb (SV (quo (var 0) (xP (var 1))) (rem (var 0) (xP (var 1))) (xQ (var 1)) (xu (var 1)) (xv (var 1)) (xW (var 1))) zero

/-- `g(i) = ⌊Q²p/q⌋ − ⌊Q²u/W⌋`. -/
abbrev gB : PTm 2 :=
  monus (quo (xQ (var 1) * xQ (var 1) * rem (var 0) (xP (var 1))) (quo (var 0) (xP (var 1))))
    (quo (xQ (var 1) * xQ (var 1) * xu (var 1)) (xW (var 1)))

/-- The parameter tuple. -/
abbrev tup (Q P u v W : PTm n) : PTm n := pairT (pairT Q P) (pairT (pairT u v) W)

theorem inst2_cB (i x : PTm n) : inst2 cB i x =
    eqb (SV (quo i (xP x)) (rem i (xP x)) (xQ x) (xu x) (xv x) (xW x)) zero := by
  simp only [inst2, cB, SV, PTm.subst_add, PTm.subst_monus, PTm.subst_mul, subst_ex2, subst_ap2, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, subst_eqb,
    subst_fstT, subst_sndT]

theorem inst2_gB (i x : PTm n) : inst2 gB i x =
    monus (quo (xQ x * xQ x * rem i (xP x)) (quo i (xP x))) (quo (xQ x * xQ x * xu x) (xW x)) := by
  simp [inst2, subst_ap2]

section Tup

variable {Q P u v W : PTm n}

theorem tQ : Γ ⊢[PRAAx] xQ (tup Q P u v W) ≐ Q := (congrFst (fst_pair _ _)).eqTrans (fst_pair _ _)
theorem tP : Γ ⊢[PRAAx] xP (tup Q P u v W) ≐ P := (congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _)
theorem tu : Γ ⊢[PRAAx] xu (tup Q P u v W) ≐ u :=
  (congrFst (congrFst (snd_pair _ _))).eqTrans ((congrFst (fst_pair _ _)).eqTrans (fst_pair _ _))
theorem tv : Γ ⊢[PRAAx] xv (tup Q P u v W) ≐ v :=
  (congrSnd (congrFst (snd_pair _ _))).eqTrans ((congrSnd (fst_pair _ _)).eqTrans (snd_pair _ _))
theorem tW : Γ ⊢[PRAAx] xW (tup Q P u v W) ≐ W := (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)

/-- `c(i)` at the tuple. -/
theorem cB_at (i : PTm n) : Γ ⊢[PRAAx] inst2 cB i (tup Q P u v W) ≐
    eqb (SV (quo i P) (rem i P) Q u v W) zero := by
  rw [inst2_cB]
  have hq : Γ ⊢[PRAAx] quo i (xP (tup Q P u v W)) ≐ quo i P := congrAp2 quoF (.eqRefl _) tP
  have hp : Γ ⊢[PRAAx] rem i (xP (tup Q P u v W)) ≐ rem i P := congrAp2 remF (.eqRefl _) tP
  refine congrEqb' ?_ (.eqRefl _)
  exact congrAdd (congrAdd (congrAdd (congrAdd (congrMonus (.eqRefl _) hq) (congrMonus hq tQ))
    (congrAdd (congrMonus (congrGcd hp hq) (.eqRefl _)) (congrMonus (.eqRefl _) (congrGcd hp hq))))
    (congrMonus (congrMul tu hq) (congrMul tW hp))) (congrMonus (congrMul tW hp) (congrMul tv hq))

/-- `g(i)` at the tuple. -/
theorem gB_at (i : PTm n) : Γ ⊢[PRAAx] inst2 gB i (tup Q P u v W) ≐
    monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W) := by
  rw [inst2_gB]
  have hq : Γ ⊢[PRAAx] quo i (xP (tup Q P u v W)) ≐ quo i P := congrAp2 quoF (.eqRefl _) tP
  have hp : Γ ⊢[PRAAx] rem i (xP (tup Q P u v W)) ≐ rem i P := congrAp2 remF (.eqRefl _) tP
  exact congrMonus (congrAp2 quoF (congrMul (congrMul tQ tQ) hp) hq)
    (congrAp2 quoF (congrMul (congrMul tQ tQ) tu) tW)

end Tup

/-! ## The two hypotheses of the injection count -/

/-- A collision term vanishes: two indices `i < M` satisfying the conditions have different floors. -/
theorem cl_zero {i M Q P u v W : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (hW : Γ ⊢[PRAAx] W ≐ succ (pred W))
    (hiM : Γ ⊢[PRAAx] lt i M) :
    Γ ⊢[PRAAx] sg (eqb (SV (quo i P) (rem i P) Q u v W) zero) * sg (eqb (SV (quo M P) (rem M P) Q u v W) zero) *
      eqb (monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W))
        (monus (quo (Q * Q * rem M P) (quo M P)) (quo (Q * Q * u) W)) ≐ zero := by
  refine .orE (eqb01' (Γ := Γ) (SV (quo i P) (rem i P) Q u v W) zero) ?_ ?_
  · have h0 : ((eqb (SV (quo i P) (rem i P) Q u v W) zero ≐ zero) :: Γ) ⊢[PRAAx]
        sg (eqb (SV (quo i P) (rem i P) Q u v W) zero) ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (congrMul ((congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans (zero_mul _)
  · let Δ : List (Fm PTm n) := (eqb (SV (quo i P) (rem i P) Q u v W) zero ≐ one) :: Γ
    have fi := facts (eq_of_eqb (Prf.hyp0 : Δ ⊢[PRAAx] _ ≐ one))
    refine .orE (eqb01' (Γ := Δ) (SV (quo M P) (rem M P) Q u v W) zero) ?_ ?_
    · have h0 : ((eqb (SV (quo M P) (rem M P) Q u v W) zero ≐ zero) :: Δ) ⊢[PRAAx]
          sg (eqb (SV (quo M P) (rem M P) Q u v W) zero) ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact (congrMul ((congrMul (.eqRefl _) h0).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans (zero_mul _)
    · let Δ' : List (Fm PTm n) := (eqb (SV (quo M P) (rem M P) Q u v W) zero ≐ one) :: Δ
      have fM := facts (eq_of_eqb (Prf.hyp0 : Δ' ⊢[PRAAx] _ ≐ one))
      refine .orE (eqb01' (Γ := Δ') (monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W))
        (monus (quo (Q * Q * rem M P) (quo M P)) (quo (Q * Q * u) W))) ?_ ?_
      · exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)
      · let Θ : List (Fm PTm n) := (eqb (monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W))
          (monus (quo (Q * Q * rem M P) (quo M P)) (quo (Q * Q * u) W)) ≐ one) :: Δ'
        have hg := eq_of_eqb (Prf.hyp0 : Θ ⊢[PRAAx] _ ≐ one)
        have fi' : Θ ⊢[PRAAx] _ := fi.wk.wk
        have fM' : Θ ⊢[PRAAx] _ := fM.wk
        have hqi := pos_of_le_one (Prf.andE₁ fi')
        have hqM := pos_of_le_one (Prf.andE₁ fM')
        have hQi := Prf.andE₁ (Prf.andE₂ fi')
        have hQM := Prf.andE₁ (Prf.andE₂ fM')
        have gi := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ fi'))
        have gM := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ fM'))
        have li := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ fi')))
        have lM := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ fM')))
        -- the base is below both floors
        have bi : Θ ⊢[PRAAx] le (quo (Q * Q * u) W) (quo (Q * Q * rem i P) (quo i P)) :=
          floor_mono hW.wk.wk.wk hqi (le_congr (.eqRefl _) (mul_comm _ _) li)
        have bM : Θ ⊢[PRAAx] le (quo (Q * Q * u) W) (quo (Q * Q * rem M P) (quo M P)) :=
          floor_mono hW.wk.wk.wk hqM (le_congr (.eqRefl _) (mul_comm _ _) lM)
        have hf := monus_cancel bi bM hg
        have inj := floor_inj hqi hqM hQi hQM gi gM hf
        -- so `i = M`
        have di := Prf.andE₁ (div_mod_at (Γ := Θ) (x := i) hP.wk.wk.wk)
        have dM := Prf.andE₁ (div_mod_at (Γ := Θ) (x := M) hP.wk.wk.wk)
        have hiM' : Θ ⊢[PRAAx] i ≐ M :=
          di.eqTrans ((congrAdd (congrMul (.eqRefl _) (Prf.andE₁ inj)) (Prf.andE₂ inj)).eqTrans dM.eqSymm)
        exact lt_irrefl _ _ (lt_congr hiM' (.eqRefl _) hiM.wk.wk.wk)

/-- A range term vanishes: a condition-satisfying index has `g(i) < R = ⌊Q²v/W⌋ − ⌊Q²u/W⌋ + 1`. -/
theorem vl_zero {i Q P u v W : PTm n} (hW : Γ ⊢[PRAAx] W ≐ succ (pred W)) :
    Γ ⊢[PRAAx] sg (eqb (SV (quo i P) (rem i P) Q u v W) zero) *
      monus one (monus (succ (monus (quo (Q * Q * v) W) (quo (Q * Q * u) W)))
        (monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W))) ≐ zero := by
  refine .orE (eqb01' (Γ := Γ) (SV (quo i P) (rem i P) Q u v W) zero) ?_ ?_
  · have h0 : ((eqb (SV (quo i P) (rem i P) Q u v W) zero ≐ zero) :: Γ) ⊢[PRAAx]
        sg (eqb (SV (quo i P) (rem i P) Q u v W) zero) ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (congrMul h0 (.eqRefl _)).eqTrans (zero_mul _)
  · let Δ : List (Fm PTm n) := (eqb (SV (quo i P) (rem i P) Q u v W) zero ≐ one) :: Γ
    have fi := facts (eq_of_eqb (Prf.hyp0 : Δ ⊢[PRAAx] _ ≐ one))
    have hq := pos_of_le_one (Prf.andE₁ fi)
    have lv := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ fi)))
    have m1 : Δ ⊢[PRAAx] le (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * v) W) :=
      floor_mono hq hW.wk (le_congr (mul_comm _ _) (.eqRefl _) lv)
    have m2 := monus_mono (c := quo (Q * Q * u) W) m1
    -- `R − g(i) ≥ 1`, so `1 − (R − g(i)) = 0`
    have e := natEq (eq_add_of_le m2)
    refine (congrMul (.eqRefl _) ?_).eqTrans (mul_zero _)
    show Δ ⊢[PRAAx] le one (monus (succ (monus (quo (Q * Q * v) W) (quo (Q * Q * u) W)))
      (monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W)))
    have m3 : Δ ⊢[PRAAx] le (monus (quo (Q * Q * rem i P) (quo i P)) (quo (Q * Q * u) W))
        (succ (monus (quo (Q * Q * v) W) (quo (Q * Q * u) W))) := le_trans m2 (le_succ_self _)
    have e2 := natEq (eq_add_of_le m3)
    ipra_le sl m2 with e2

/-! ## The count -/

/-- At most `⌊Q²v/W⌋ − ⌊Q²u/W⌋ + 1` reduced fractions `p/q ∈ [u/W, v/W]` with `1 ≤ q ≤ Q` (indexed by
`i = qP + p < (Q + 1)P`). -/
theorem fraction_count {Q P u v W : PTm n} (hP : Γ ⊢[PRAAx] P ≐ succ (pred P)) (hW : Γ ⊢[PRAAx] W ≐ succ (pred W)) :
    Γ ⊢[PRAAx] le (ap2 (sumF (sgB cB)) (succ Q * P) (tup Q P u v W))
      (succ (monus (quo (Q * Q * v) W) (quo (Q * Q * u) W))) := by
  refine injection_count cB gB ?_ ?_
  · -- no collisions
    refine (sum_congr_bounded _ (zero : PTm 2) _ (tup Q P u v W) _ (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift (tup Q P u v W)) = zero by simp [inst2],
      inst2_rowCB]
    refine (sum_congr_bounded _ (zero : PTm 2) _ (pairT (var 0) (Syn.shift (tup Q P u v W))) _
      (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1 + 1)) (Syn.shift (pairT (var 0) (Syn.shift (tup Q P u v W)))) =
        zero by simp [inst2], inst2_clB,
      show Syn.shift (pairT (var 0) (Syn.shift (tup Q P u v W))) =
        pairT (var 1) (tup (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift u))
          (Syn.shift (Syn.shift v)) (Syn.shift (Syn.shift W))) by simp [Syn.shift]]
    let Θ : List (Fm PTm (n + 1 + 1)) := lt (var 0) (Syn.shift (var 0)) ::
      (lt (var 0) (Syn.shift (succ Q * P)) :: Γ.map Fm.shift).map Fm.shift
    have hP2 : Θ ⊢[PRAAx] Syn.shift (Syn.shift P) ≐ succ (pred (Syn.shift (Syn.shift P))) := by
      have s : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift P) ≐ succ (pred (Syn.shift (Syn.shift P))) := by
        simpa [Fm.shift, Syn.shift] using hP.shift.shift
      exact (s.weaken (by intro φ hφ; simp only [List.mem_map] at hφ ⊢; aesop))
    have hW2 : Θ ⊢[PRAAx] Syn.shift (Syn.shift W) ≐ succ (pred (Syn.shift (Syn.shift W))) := by
      have s : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift W) ≐ succ (pred (Syn.shift (Syn.shift W))) := by
        simpa [Fm.shift, Syn.shift] using hW.shift.shift
      exact (s.weaken (by intro φ hφ; simp only [List.mem_map] at hφ ⊢; aesop))
    have hlt : Θ ⊢[PRAAx] lt (var 0) (var 1) := Prf.hyp0
    have s1 : Θ ⊢[PRAAx] sndT (pairT (var 1) (tup (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift P))
        (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift v)) (Syn.shift (Syn.shift W)))) ≐
        tup (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift v))
          (Syn.shift (Syn.shift W)) := snd_pair _ _
    have f1 : Θ ⊢[PRAAx] fstT (pairT (var 1) (tup (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift P))
        (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift v)) (Syn.shift (Syn.shift W)))) ≐ var 1 := fst_pair _ _
    refine (congrMul (congrMul (congrSg ((congrInst2 cB (.eqRefl _) s1).eqTrans (cB_at _)))
      (congrSg ((congrInst2 cB f1 s1).eqTrans (cB_at _))))
      (congrEqb' ((congrInst2 gB (.eqRefl _) s1).eqTrans (gB_at _)) ((congrInst2 gB f1 s1).eqTrans (gB_at _)))).eqTrans ?_
    exact cl_zero hP2 hW2 hlt
  · -- no escapes
    refine (sum_congr_bounded _ (zero : PTm 2) _ (pairT (succ (monus (quo (Q * Q * v) W) (quo (Q * Q * u) W)))
      (tup Q P u v W)) _ (.allI (.impI ?_))).eqTrans (sum_zeroB _ _)
    rw [show inst2 (zero : PTm 2) (var 0 : PTm (n + 1)) _ = zero by simp [inst2], inst2_vB,
      show Syn.shift (pairT (succ (monus (quo (Q * Q * v) W) (quo (Q * Q * u) W))) (tup Q P u v W)) =
        pairT (succ (monus (quo (Syn.shift Q * Syn.shift Q * Syn.shift v) (Syn.shift W))
          (quo (Syn.shift Q * Syn.shift Q * Syn.shift u) (Syn.shift W))))
          (tup (Syn.shift Q) (Syn.shift P) (Syn.shift u) (Syn.shift v) (Syn.shift W)) by simp [Syn.shift]]
    have hW1 : (lt (var 0) (Syn.shift (succ Q * P)) :: Γ.map Fm.shift) ⊢[PRAAx] Syn.shift W ≐ succ (pred (Syn.shift W)) := by
      have s : Γ.map Fm.shift ⊢[PRAAx] Syn.shift W ≐ succ (pred (Syn.shift W)) := by
        simpa [Fm.shift, Syn.shift] using hW.shift
      exact s.wk
    have s1 := snd_pair (Γ := lt (var 0) (Syn.shift (succ Q * P)) :: Γ.map Fm.shift)
      (succ (monus (quo (Syn.shift Q * Syn.shift Q * Syn.shift v) (Syn.shift W))
        (quo (Syn.shift Q * Syn.shift Q * Syn.shift u) (Syn.shift W))))
      (tup (Syn.shift Q) (Syn.shift P) (Syn.shift u) (Syn.shift v) (Syn.shift W))
    have f1 := fst_pair (Γ := lt (var 0) (Syn.shift (succ Q * P)) :: Γ.map Fm.shift)
      (succ (monus (quo (Syn.shift Q * Syn.shift Q * Syn.shift v) (Syn.shift W))
        (quo (Syn.shift Q * Syn.shift Q * Syn.shift u) (Syn.shift W))))
      (tup (Syn.shift Q) (Syn.shift P) (Syn.shift u) (Syn.shift v) (Syn.shift W))
    refine (congrMul (congrSg ((congrInst2 cB (.eqRefl _) s1).eqTrans (cB_at _)))
      (congrMonus (.eqRefl _) (congrMonus f1 ((congrInst2 gB (.eqRefl _) s1).eqTrans (gB_at _))))).eqTrans ?_
    exact vl_zero hW1

end LeanProofs.IPRA.DiophantineNumberTheory.FractionCount
