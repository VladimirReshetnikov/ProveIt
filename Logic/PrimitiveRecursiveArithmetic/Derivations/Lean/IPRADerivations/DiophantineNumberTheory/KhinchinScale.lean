import IPRADerivations.DiophantineNumberTheory.KhinchinSeparated
import IPRADerivations.Foundations.PackingPointwise
import IPRADerivations.AnalyticNumberTheory.DivisorHyperbola

/-!
# The measure of one Khinchin scale (`hurwitz_khinchin_ipra`, (K8))

Packet: `diophantine-number-theory/hurwitz_khinchin_ipra`, `khinchin.tex`, (K8): `E_k(J)` is "the union
of the intervals of radius `r_k` centered at the fractions in `𝓡_k(J)` … pairwise disjoint at each fixed
scale", so `|E_k(J)| = 2r_k · #𝓡_k(J)`.

The pairs `(p, q)` with `Q' < q ≤ Q`, `p < M` are flattened to `k < (Q − Q')M`
(`Foundations/SumFlatten`): `q = Q' + 1 + ⌊k/M⌋`, `p = k mod M`. On the grid `T = Q! · G`, which every
`q ≤ Q` divides, the fraction `p/q` sits at `A_k = Tp/q`, and the member `k` is the interval
`[A_k, A_k + [act_k] w)` with `act_k = [p/q ∈ J*][gcd(p, q) = 1]` (`J* = (α/β, γ/β)`). Centering the
intervals is a translation, which does not change the measure. For `Q²w ≤ T`:

* `q_le`, `grid_eq`: `q ≤ Q` and `qA_k = Tp` for every `k < (Q − Q')M`;
* `mem_pt`: every member lies in `[0, TM)`;
* `sep_pt`: two different active members are `w`-separated (`KhinchinSeparated.sep_pair`, the flattening
  being injective);
* `scale_measure`: `|E| = w Σ_{k<(Q−Q')M} [act_k]` (`Foundations/PackingPointwise.packing_pt`).

The members are bodies over `(k, y)` with `y = ⟨M, Q', T, α, γ, β⟩`; they are substitution instances
of 7-variable core terms, decoded by one `Prf.eqCongr` (`conv`).
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale

open_ipra exports
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.FiniteBijection (sg_bit)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Foundations.IntervalCover (measure)
open LeanProofs.IPRA.Foundations.IntervalPacking (loB hiB acB absurd_one_zero')
open LeanProofs.IPRA.Foundations.PackingPointwise (packing_pt)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinSeparated (actv sep_pair)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## The members, explicitly -/

/-- The denominator `q = Q' + 1 + ⌊k/M⌋`. -/
abbrev qE (Q' M k : PTm n) : PTm n := succ (Q' + quo k M)
/-- The grid point `A_k = ⌊Tp/q⌋` of `p/q`, `p = k mod M`. -/
abbrev AE (Q' T M k : PTm n) : PTm n := quo (T * rem k M) (qE Q' M k)
/-- `act_k = [p/q ∈ J*][gcd(p, q) = 1]`. -/
abbrev actE (Q' M α γ β k : PTm n) : PTm n := actv (rem k M) (qE Q' M k) α γ β

/-- `q ≤ Q` for `k < (Q − Q')M`. -/
theorem q_le {M Q Q' k : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQ' : Γ ⊢[PRAAx] le Q' Q)
    (hk : Γ ⊢[PRAAx] lt k (monus Q Q' * M)) : Γ ⊢[PRAAx] le (qE Q' M k) Q := by
  have dm := Prf.andE₁ (div_mod_at (Γ := Γ) (x := k) hM)
  have hQe := eq_add_of_le hQ'
  refine .orE (lt_or_le (quo k M) (monus Q Q')) ?_ ?_
  · let Θ : List (Fm PTm n) := lt (quo k M) (monus Q Q') :: Γ
    have h : Θ ⊢[PRAAx] lt (quo k M) (monus Q Q') := Prf.hyp0
    have eQ := natEq (hQe.wk : Θ ⊢[PRAAx] Q ≐ Q' + monus Q Q')
    ipra_le sl h with eQ
  · let Θ : List (Fm PTm n) := le (monus Q Q') (quo k M) :: Γ
    have h : Θ ⊢[PRAAx] le (monus Q Q') (quo k M) := Prf.hyp0
    have hk' : Θ ⊢[PRAAx] lt k (monus Q Q' * M) := hk.wk
    have e := natEq (dm.wk : Θ ⊢[PRAAx] k ≐ M * quo k M + rem k M)
    have hz : Θ ⊢[PRAAx] le one zero := by ipra_le sl hk' + 𝔞 M * sl h + 𝔞 (rem k M) with e
    exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)

/-- The grid equation `qA_k = Tp` on `T = R! G`, `Q ≤ R`. -/
theorem grid_eq {M Q Q' R G k : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQ' : Γ ⊢[PRAAx] le Q' Q)
    (hQR : Γ ⊢[PRAAx] le Q R) (hk : Γ ⊢[PRAAx] lt k (monus Q Q' * M)) :
    Γ ⊢[PRAAx] qE Q' M k * AE Q' (fact R * G) M k ≐ fact R * G * rem k M := by
  have hq := q_le hM hQ' hk
  have dv : Γ ⊢[PRAAx] dvd (qE Q' M k) (fact R * G * rem k M) := dvd_mul _ (dvd_mul _ (dvd_fact (le_trans hq hQR)))
  have dm := Prf.andE₁ (div_mod_at (Γ := Γ) (x := fact R * G * rem k M) (y := qE Q' M k) (c := Q' + quo k M)
    (.eqRefl _))
  exact (add_zero _).eqSymm.eqTrans ((congrAdd (.eqRefl _) dv).eqSymm.eqTrans dm.eqSymm)

/-- Every member lies in the grid `[0, TM)`. -/
theorem mem_pt {M Q Q' R G w α γ β k : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQ' : Γ ⊢[PRAAx] le Q' Q)
    (hw : Γ ⊢[PRAAx] le (Q * Q * w) (fact R * G)) (hk : Γ ⊢[PRAAx] lt k (monus Q Q' * M)) :
    Γ ⊢[PRAAx] le (AE Q' (fact R * G) M k + sg (actE Q' M α γ β k) * w) (fact R * G * M) := by
  have hq := q_le hM hQ' hk
  have hp : Γ ⊢[PRAAx] lt (rem k M) M := Prf.andE₂ (div_mod_at (x := k) hM)
  have hA : Γ ⊢[PRAAx] le (AE Q' (fact R * G) M k) (fact R * G * rem k M) := quo_le_self _ _
  refine .orE (sg_bit (Γ := Γ) (actE Q' M α γ β k)) ?_ ?_
  · let Θ : List (Fm PTm n) := (sg (actE Q' M α γ β k) ≐ zero) :: Γ
    have e := natEq (Prf.hyp0 : Θ ⊢[PRAAx] sg (actE Q' M α γ β k) ≐ zero)
    have hq' : Θ ⊢[PRAAx] le (qE Q' M k) Q := hq.wk
    have hp' : Θ ⊢[PRAAx] lt (rem k M) M := hp.wk
    have hA' : Θ ⊢[PRAAx] le (AE Q' (fact R * G) M k) (fact R * G * rem k M) := hA.wk
    have hw' : Θ ⊢[PRAAx] le (Q * Q * w) (fact R * G) := hw.wk
    ipra_le sl hA' + 𝔞 (fact R * G) * sl hp' + sl hw' + 𝔞 w * (𝔞 Q * (𝔞 Q' + 𝔞 (quo k M) + sl hq')) +
      𝔞 w * (𝔞 Q' + 𝔞 (quo k M) + sl hq') + 𝔞 w with 𝔞 w * e
  · let Θ : List (Fm PTm n) := (sg (actE Q' M α γ β k) ≐ one) :: Γ
    have e := natEq (Prf.hyp0 : Θ ⊢[PRAAx] sg (actE Q' M α γ β k) ≐ one)
    have hq' : Θ ⊢[PRAAx] le (qE Q' M k) Q := hq.wk
    have hp' : Θ ⊢[PRAAx] lt (rem k M) M := hp.wk
    have hA' : Θ ⊢[PRAAx] le (AE Q' (fact R * G) M k) (fact R * G * rem k M) := hA.wk
    have hw' : Θ ⊢[PRAAx] le (Q * Q * w) (fact R * G) := hw.wk
    ipra_le sl hA' + 𝔞 (fact R * G) * sl hp' + sl hw' + 𝔞 w * (𝔞 Q * (𝔞 Q' + 𝔞 (quo k M) + sl hq')) +
      𝔞 w * (𝔞 Q' + 𝔞 (quo k M) + sl hq') with 𝔞 w * e

/-- Two different active members `a < b` are `w`-separated: `A_a + w ≤ A_b` or `A_b + w ≤ A_a`. -/
theorem sep_or {M Q Q' R G w α γ β a b : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQ' : Γ ⊢[PRAAx] le Q' Q)
    (hQR : Γ ⊢[PRAAx] le Q R) (hw : Γ ⊢[PRAAx] le (Q * Q * w) (fact R * G)) (hab : Γ ⊢[PRAAx] lt a b)
    (hb : Γ ⊢[PRAAx] lt b (monus Q Q' * M)) (a1 : Γ ⊢[PRAAx] sg (actE Q' M α γ β a) ≐ one)
    (a2 : Γ ⊢[PRAAx] sg (actE Q' M α γ β b) ≐ one) :
    Γ ⊢[PRAAx] le (AE Q' (fact R * G) M a + w) (AE Q' (fact R * G) M b) ⋎
      le (AE Q' (fact R * G) M b + w) (AE Q' (fact R * G) M a) := by
  have ha : Γ ⊢[PRAAx] lt a (monus Q Q' * M) := le_trans hab (le_of_lt hb)
  -- the flattening is injective
  have hne : Γ ⊢[PRAAx] neg ((qE Q' M a ≐ qE Q' M b) ⋏ (rem a M ≐ rem b M)) := by
    refine .impI ?_
    let Θ : List (Fm PTm n) := ((qE Q' M a ≐ qE Q' M b) ⋏ (rem a M ≐ rem b M)) :: Γ
    have hc : Θ ⊢[PRAAx] (qE Q' M a ≐ qE Q' M b) ⋏ (rem a M ≐ rem b M) := Prf.hyp0
    have eab : Θ ⊢[PRAAx] a ≐ b := by
      ipra_lc natEq ((Prf.andE₁ (div_mod_at (Γ := Γ) (x := a) hM)).wk : Θ ⊢[PRAAx] a ≐ M * quo a M + rem a M) -
        natEq ((Prf.andE₁ (div_mod_at (Γ := Γ) (x := b) hM)).wk : Θ ⊢[PRAAx] b ≐ M * quo b M + rem b M) +
        𝔞 M * natEq (Prf.andE₁ hc) + natEq (Prf.andE₂ hc)
    have e := natEq eab
    have hab' : Θ ⊢[PRAAx] lt a b := hab.wk
    have hz : Θ ⊢[PRAAx] le one zero := by ipra_le sl hab' with e
    exact absurd_one_zero' ((monus_zero _).eqSymm.eqTrans hz)
  have hqa : Γ ⊢[PRAAx] qE Q' M a ≐ succ (pred (qE Q' M a)) := congrSucc (pred_succ _).eqSymm
  have hqb : Γ ⊢[PRAAx] qE Q' M b ≐ succ (pred (qE Q' M b)) := congrSucc (pred_succ _).eqSymm
  exact sep_pair hqa hqb (q_le hM hQ' ha) (q_le hM hQ' hb) (grid_eq hM hQ' hQR ha) (grid_eq hM hQ' hQR hb) hw
    a1 a2 hne

/-- Two different active members `a < b` are `w`-separated: the separation term vanishes. -/
theorem sep_pt {M Q Q' R G w α γ β a b : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M)) (hQ' : Γ ⊢[PRAAx] le Q' Q)
    (hQR : Γ ⊢[PRAAx] le Q R) (hw : Γ ⊢[PRAAx] le (Q * Q * w) (fact R * G)) (hab : Γ ⊢[PRAAx] lt a b)
    (hb : Γ ⊢[PRAAx] lt b (monus Q Q' * M)) :
    Γ ⊢[PRAAx] sg (actE Q' M α γ β a) * sg (actE Q' M α γ β b) *
      sg (monus (AE Q' (fact R * G) M b + w) (AE Q' (fact R * G) M a)) *
      sg (monus (AE Q' (fact R * G) M a + w) (AE Q' (fact R * G) M b)) ≐ zero := by
  refine .orE (sg_bit (Γ := Γ) (actE Q' M α γ β a)) ?_ ?_
  · exact (congrMul (congrMul (congrMul Prf.hyp0 (.eqRefl _)) (.eqRefl _)) (.eqRefl _)).eqTrans
      ((congrMul (congrMul (zero_mul _) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _)))
  · let Δ1 : List (Fm PTm n) := (sg (actE Q' M α γ β a) ≐ one) :: Γ
    have a1 : Δ1 ⊢[PRAAx] sg (actE Q' M α γ β a) ≐ one := Prf.hyp0
    refine .orE (sg_bit (Γ := Δ1) (actE Q' M α γ β b)) ?_ ?_
    · exact (congrMul (congrMul (congrMul (.eqRefl _) Prf.hyp0) (.eqRefl _)) (.eqRefl _)).eqTrans
        ((congrMul (congrMul (mul_zero _) (.eqRefl _)) (.eqRefl _)).eqTrans
          ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _)))
    · let Δ2 : List (Fm PTm n) := (sg (actE Q' M α γ β b) ≐ one) :: Δ1
      have a2 : Δ2 ⊢[PRAAx] sg (actE Q' M α γ β b) ≐ one := Prf.hyp0
      refine .orE (sep_or hM.wk.wk hQ'.wk.wk hQR.wk.wk hw.wk.wk hab.wk.wk hb.wk.wk a1.wk a2) ?_ ?_
      · exact (congrMul (.eqRefl _) ((congrSg Prf.hyp0).eqTrans sg_zero)).eqTrans (mul_zero _)
      · exact (congrMul (congrMul (.eqRefl _) ((congrSg Prf.hyp0).eqTrans sg_zero)) (.eqRefl _)).eqTrans
          ((congrMul (mul_zero _) (.eqRefl _)).eqTrans (zero_mul _))

/-! ## The members as bodies -/

/-- `⟨M, Q', T, α, γ, β⟩`. -/
abbrev tup (M Q' T α γ β : PTm n) : PTm n := pairT M (pairT Q' (pairT T (pairT α (pairT γ β))))

/-- The decoding substitution `(k, y) ↦ (k, M, Q', T, α, γ, β)`. -/
def dec (a y : PTm n) : Fin 7 → PTm n :=
  ![a, fstT y, fstT (sndT y), fstT (sndT (sndT y)), fstT (sndT (sndT (sndT y))),
    fstT (sndT (sndT (sndT (sndT y)))), sndT (sndT (sndT (sndT (sndT y))))]

/-- `q` in the core variables `0 = k, 1 = M, 2 = Q', 3 = T, 4 = α, 5 = γ, 6 = β`. -/
def qC : PTm 7 := succ (var 2 + quo (var 0) (var 1))
/-- `A_k` in the core variables. -/
def AC : PTm 7 := quo (var 3 * rem (var 0) (var 1)) qC
/-- `act_k` in the core variables. -/
def actC : PTm 7 := actv (rem (var 0) (var 1)) qC (var 4) (var 5) (var 6)

/-- `A_k` over `(k, y)`. -/
def AK : PTm 2 := Syn.subst (dec (var 0) (var 1)) AC
/-- `act_k` over `(k, y)`. -/
def actK : PTm 2 := Syn.subst (dec (var 0) (var 1)) actC

theorem inst2_lift (C : PTm 7) (a y : PTm n) :
    inst2 (Syn.subst (dec (var 0) (var 1)) C) a y = Syn.subst (dec a y) C := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp [dec]

theorem dec_tup (a M Q' T α γ β : PTm n) (i : Fin 7) :
    Γ ⊢[PRAAx] dec a (tup M Q' T α γ β) i ≐ (![a, M, Q', T, α, γ, β] : Fin 7 → PTm n) i := by
  refine Fin.cases (.eqRefl _) (fun j => ?_) i
  simpa [dec, tup, pairVector, pairVectorField] using
    (pairVectorField_eq (Γ := Γ) 5 ![M, Q', T, α, γ, β] (.eqRefl _) j)

/-- Decoding a body at a tuple. -/
theorem conv (C : PTm 7) (a M Q' T α γ β : PTm n) :
    Γ ⊢[PRAAx] inst2 (Syn.subst (dec (var 0) (var 1)) C) a (tup M Q' T α γ β) ≐
      Syn.subst (![a, M, Q', T, α, γ, β] : Fin 7 → PTm n) C := by
  rw [inst2_lift]; exact Prf.eqCongr C (dec_tup a M Q' T α γ β)

theorem A_at (a M Q' T α γ β : PTm n) :
    Γ ⊢[PRAAx] inst2 AK a (tup M Q' T α γ β) ≐ AE Q' T M a := by
  have e := conv (Γ := Γ) AC a M Q' T α γ β
  simpa [AK, AC, qC, AE, qE, subst_ap2] using e

theorem act_at (a M Q' T α γ β : PTm n) :
    Γ ⊢[PRAAx] inst2 actK a (tup M Q' T α γ β) ≐ actE Q' M α γ β a := by
  have e := conv (Γ := Γ) actC a M Q' T α γ β
  have h : Syn.subst (![a, M, Q', T, α, γ, β] : Fin 7 → PTm n) actC = actE Q' M α γ β a := by
    simp only [actC, qC, actE, qE, actv, KhinchinBad.inJT, Signum.sg, gcd, PTm.subst_mul, PTm.subst_monus,
      PTm.subst_add, subst_ex2, subst_ap2, subst_eqb, Syn.subst_var, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
    try rfl
  rw [h] at e
  exact e

/-! ## The measure of the scale -/

/-- (K8), the exact form: on the grid `T = R! G` (`Q ≤ R`) with `Q²w ≤ T`, the active members (the reduced
fractions of `J*` with denominators `Q' < q ≤ Q` and numerators `< M`) have union length
`w Σ_{k<(Q−Q')M} [act_k]`. -/
theorem scale_measure {M Q Q' R G w α γ β : PTm n} (hM : Γ ⊢[PRAAx] M ≐ succ (pred M))
    (hQ' : Γ ⊢[PRAAx] le Q' Q) (hQR : Γ ⊢[PRAAx] le Q R) (hw : Γ ⊢[PRAAx] le (Q * Q * w) (fact R * G)) :
    Γ ⊢[PRAAx] measure (loB AK) (hiB AK actK) (fact R * G * M) (monus Q Q' * M)
        (pairT w (tup M Q' (fact R * G) α γ β)) ≐
      w * ap2 (sumF (acB actK)) (monus Q Q' * M) (tup M Q' (fact R * G) α γ β) := by
  have hM1 : Γ.map Fm.shift ⊢[PRAAx] Syn.shift M ≐ succ (pred (Syn.shift M)) := by
    simpa [Fm.shift, Syn.shift] using hM.shift
  have hQ1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Q') (Syn.shift Q) := by
    simpa [Fm.shift, Syn.shift] using hQ'.shift
  have hw1 : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift Q * Syn.shift Q * Syn.shift w)
      (fact (Syn.shift R) * Syn.shift G) := by
    simpa [Fm.shift, Syn.shift] using hw.shift
  have hQR1 := LeanProofs.IPRA.Order.shift_le hQR
  refine packing_pt AK actK ?_ ?_
  · intro Δ a hs ha
    rw [show Syn.shift (tup M Q' (fact R * G) α γ β) = tup (Syn.shift M) (Syn.shift Q')
        (fact (Syn.shift R) * Syn.shift G) (Syn.shift α) (Syn.shift γ) (Syn.shift β) by simp [Syn.shift],
      show Syn.shift (fact R * G * M) = fact (Syn.shift R) * Syn.shift G * Syn.shift M by simp [Syn.shift]]
    rw [show Syn.shift (monus Q Q' * M) = monus (Syn.shift Q) (Syn.shift Q') * Syn.shift M by
      simp [Syn.shift]] at ha
    refine le_congr ?_ (.eqRefl _) (mem_pt (α := Syn.shift α) (γ := Syn.shift γ) (β := Syn.shift β)
      (hM1.weaken hs) (hQ1.weaken hs) (hw1.weaken hs) ha)
    exact congrAdd (A_at _ _ _ _ _ _ _).eqSymm (congrMul (congrSg (act_at _ _ _ _ _ _ _).eqSymm) (.eqRefl _))
  · intro Δ a b hs hab hb
    have hM2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] Syn.shift (Syn.shift M) ≐
        succ (pred (Syn.shift (Syn.shift M))) := by
      simpa [Fm.shift, Syn.shift] using hM1.shift
    have hQ2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift Q')) (Syn.shift (Syn.shift Q)) := by
      simpa [Fm.shift, Syn.shift] using hQ1.shift
    have hw2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift Q) * Syn.shift (Syn.shift Q) *
        Syn.shift (Syn.shift w)) (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G)) := by
      simpa [Fm.shift, Syn.shift] using hw1.shift
    have hQR2 : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift R)) := by
      simpa [Fm.shift, Syn.shift] using hQR1.shift
    rw [show Syn.shift (Syn.shift (tup M Q' (fact R * G) α γ β)) = tup (Syn.shift (Syn.shift M))
        (Syn.shift (Syn.shift Q')) (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G))
        (Syn.shift (Syn.shift α)) (Syn.shift (Syn.shift γ)) (Syn.shift (Syn.shift β)) by simp [Syn.shift]]
    rw [show Syn.shift (Syn.shift (monus Q Q' * M)) = monus (Syn.shift (Syn.shift Q)) (Syn.shift (Syn.shift Q')) *
        Syn.shift (Syn.shift M) by simp [Syn.shift]] at hb
    refine .eqTrans ?_ (sep_pt (α := Syn.shift (Syn.shift α)) (γ := Syn.shift (Syn.shift γ))
      (β := Syn.shift (Syn.shift β)) (hM2.weaken hs) (hQ2.weaken hs) (hQR2.weaken hs) (hw2.weaken hs) hab hb)
    have Aa := A_at (Γ := Δ) a (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift Q'))
      (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G)) (Syn.shift (Syn.shift α)) (Syn.shift (Syn.shift γ))
      (Syn.shift (Syn.shift β))
    have Ab := A_at (Γ := Δ) b (Syn.shift (Syn.shift M)) (Syn.shift (Syn.shift Q'))
      (fact (Syn.shift (Syn.shift R)) * Syn.shift (Syn.shift G)) (Syn.shift (Syn.shift α)) (Syn.shift (Syn.shift γ))
      (Syn.shift (Syn.shift β))
    exact congrMul (congrMul (congrMul (congrSg (act_at _ _ _ _ _ _ _)) (congrSg (act_at _ _ _ _ _ _ _)))
        (congrSg (congrMonus (congrAdd Ab (.eqRefl _)) Aa)))
      (congrSg (congrMonus (congrAdd Aa (.eqRefl _)) Ab))

end LeanProofs.IPRA.DiophantineNumberTheory.KhinchinScale

export_ipra DiophantineNumberTheory.KhinchinScale (actK tup)
