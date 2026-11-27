import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.OrderCertificates
import IPRADerivations.Probability.Independence

/-!
# Mixed-radix codes

Packets: `foundations/FINER-iPRA-framework-2026-11-16` (`paper/sections/03_finite_data.tex`, "Mixed-radix
arrays", `eq:mixed-code` and the lemma "Mixed-radix correctness") and
`foundations/STRIVE-iPRA-framework-2026-11-16` (the theorems "Packed-code bound" and "Mixed-radix decoding"):
for radices `r_0, …, r_{m−1}` and digits `d_i < r_i`,
`code(d) = ∑_{i<m} d_i ∏_{j<i} r_j` is below `R = ∏_{i<m} r_i`, and the `i`-th digit is recovered by
quotienting by the place value `∏_{j<i} r_j` and taking the remainder modulo `r_i`.

For arbitrary radix and digit bodies `r(i, x)`, `d(i, x)`, with `Pl k = ∏_{j<k} r_j` and
`Cd k = ∑_{i<k} d_i · Pl i`:

* `prod_split`: `∏_{i<M+K} f = ∏_{i<M} f · ∏_{i<K} f(M + i)`;
* `code_split`: `Cd (a + t) = Cd a + Pl a · Tl a t`, where `Tl a t` is the code of the digits
  `d_a, …, d_{a+t−1}` with the radices `r_a, …`: a code is its prefix plus the place value times its suffix;
* `code_lt` ("Packed-code bound"): if `d_i < r_i` for `i < m`, then `Cd m < Pl m`;
* `suffix_step`: `Tl i (t + 1) = d_i + r_i · Tl (i + 1) t`, obtained from two instances of `code_split` by
  uniqueness of quotient and remainder;
* `decode` ("Mixed-radix decoding"): if `d_j < r_j` for `j < i + 1 + t`, then
  `((Cd (i + 1 + t)) div (Pl i)) mod r_i = d_i`.

The converse direction (re-encoding the decoded digits of a number below `R`) and the certificate
constructions of the packets are not derived here.
-/

namespace LeanProofs.IPRA.Foundations.MixedRadix

open_ipra exports
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Splitting a product -/

theorem prod_succ' (body : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF body) (succ N) x ≐ ap2 (prodF body) N x * inst2 body N x :=
  prod_succ body N x

theorem psplit_base (f : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF f) (M + zero) x ≐ ap2 (prodF f) M x * ap2 (prodF (offB f)) zero (pairT M x) := by
  have c := natEq (congrAp2 (prodF f) (add_zero (Γ := Γ) M) (.eqRefl x))
  have z := natEq (prod_zero (Γ := Γ) (offB f) (pairT M x))
  apply deriveNat; ipra_simps
  rw [c, z]; ring

theorem psplit_step (f : PTm 2) {M K x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (prodF f) (M + K) x ≐ ap2 (prodF f) M x * ap2 (prodF (offB f)) K (pairT M x)) :
    Γ ⊢[PRAAx] ap2 (prodF f) (M + succ K) x ≐
      ap2 (prodF f) M x * ap2 (prodF (offB f)) (succ K) (pairT M x) := by
  have c := natEq (congrAp2 (prodF f) (add_succ (Γ := Γ) M K) (.eqRefl x))
  have s := natEq (prod_succ' (Γ := Γ) f (M + K) x)
  have s' := prod_succ' (Γ := Γ) (offB f) K (pairT M x)
  rw [inst2_offB] at s'
  have a' := natEq s'
  have pt := natEq (congrInst2 f (congrAdd (fst_pair (Γ := Γ) M x) (.eqRefl K)) (snd_pair M x))
  have i := natEq ih
  apply deriveNat; ipra_simps
  rw [c, s, i, a', pt]; ring

/-- Variables: `0 = K` (induction), `1 = M`, `2 = x`. -/
private abbrev psplitF (f : PTm 2) : Fm PTm 3 :=
  ap2 (prodF f) (var 1 + var 0) (var 2) ≐
    ap2 (prodF f) (var 1) (var 2) * ap2 (prodF (offB f)) (var 0) (pairT (var 1) (var 2))

private theorem psplit₀ (f : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] psplitF f := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact psplit_base f _ _
  · exact psplit_step f Prf.hyp0

/-- `∏_{i<M+K} f(i, x) = ∏_{i<M} f(i, x) · ∏_{i<K} f(M + i, x)`. -/
theorem prod_split (f : PTm 2) (M K x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF f) (M + K) x ≐ ap2 (prodF f) M x * ap2 (prodF (offB f)) K (pairT M x) := by
  have h := inst (Γ := Γ) (psplit₀ f) (![K, M, x] : Fin 3 → PTm n)
  simpa using h

/-! ## Codes -/

/-- The place value `Pl k = ∏_{j<k} r_j`. -/
abbrev Pl (r : PTm 2) (k x : PTm n) : PTm n := ap2 (prodF r) k x

/-- `d_i · Pl i` as a body. -/
abbrev dP (r d : PTm 2) : PTm 2 := d * ap2 (prodF r) (var 0) (var 1)

/-- `eq:mixed-code`: `Cd k = ∑_{i<k} d_i ∏_{j<i} r_j`. -/
abbrev Cd (r d : PTm 2) (k x : PTm n) : PTm n := ap2 (sumF (dP r d)) k x

/-- The suffix digit times its place value relative to the offset, over `(s, ⟨a, x⟩)`. -/
abbrev eB (r d : PTm 2) : PTm 2 := offB d * ap2 (prodF (offB r)) (var 0) (var 1)

/-- The suffix code `Tl a t = ∑_{s<t} d_{a+s} ∏_{l<s} r_{a+l}`. -/
abbrev Tl (r d : PTm 2) (a t x : PTm n) : PTm n := ap2 (sumF (eB r d)) t (pairT a x)

theorem inst2_dP (r d : PTm 2) (i x : PTm n) : inst2 (dP r d) i x = inst2 d i x * ap2 (prodF r) i x := by
  simp [inst2]

theorem inst2_eB (r d : PTm 2) (s y : PTm n) :
    inst2 (eB r d) s y = inst2 (offB d) s y * ap2 (prodF (offB r)) s y := by
  simp [inst2]

/-- A code is its prefix plus the place value times its suffix: `Cd (a + t) = Cd a + Pl a · Tl a t`. -/
theorem code_split (r d : PTm 2) (a t x : PTm n) :
    Γ ⊢[PRAAx] Cd r d (a + t) x ≐ Cd r d a x + Pl r a x * Tl r d a t x := by
  have s := sum_split (Γ := Γ) (dP r d) a t x
  have sc := sum_scale (Γ := Γ) (offB (dP r d)) (eB r d) t (Pl r a x) (pairT a x) (pairT a x)
    (.allI (.impI (by
      have e : Syn.shift (Pl r a x) = ap2 (prodF r) (Syn.shift a) (Syn.shift x) := by simp [Syn.shift]
      rw [shift_pairT, e, inst2_offB, inst2_dP, inst2_eB, inst2_offB]
      have ps := natEq ((congrAp2 (prodF r) (congrAdd (fst_pair (Γ := lt (var 0) (Syn.shift t) :: Γ.map Fm.shift)
          (Syn.shift a) (Syn.shift x)) (.eqRefl (var 0))) (snd_pair (Syn.shift a) (Syn.shift x))).eqTrans
        (prod_split r (Syn.shift a) (var 0) (Syn.shift x)))
      apply deriveNat; ipra_simps
      rw [ps]; ring)))
  exact s.eqTrans (congrAdd (.eqRefl _) sc)

/-! ## The range of a code -/

theorem lt_base (r d : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] lt (Cd r d zero x) (Pl r zero x) := by
  have z := natEq (sum_zero (Γ := Γ) (dP r d) x); have p := natEq (prod_zero (Γ := Γ) r x)
  ipra_le 0 using rw [z, p]; ring

theorem lt_step {r d : PTm 2} {k x : PTm n} (hd : Γ ⊢[PRAAx] lt (inst2 d k x) (inst2 r k x))
    (ih : Γ ⊢[PRAAx] lt (Cd r d k x) (Pl r k x)) : Γ ⊢[PRAAx] lt (Cd r d (succ k) x) (Pl r (succ k) x) := by
  have es' := sum_succ' (Γ := Γ) (dP r d) k x
  rw [inst2_dP] at es'
  have es := natEq es'
  have ep := natEq (prod_succ' (Γ := Γ) r k x)
  have hd' : Γ ⊢[PRAAx] le (succ (inst2 d k x)) (inst2 r k x) := hd
  have ih' : Γ ⊢[PRAAx] le (succ (Cd r d k x)) (Pl r k x) := ih
  show Γ ⊢[PRAAx] le (succ (Cd r d (succ k) x)) (Pl r (succ k) x)
  ipra_le sl ih' + sl hd' * 𝔟 (Pl r k x) using rw [es, ep]; ring

/-- "Packed-code bound": if `d_i < r_i` for `i < m`, then `Cd m < Pl m`. -/
theorem code_lt (r d : PTm 2) (x m : PTm n)
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift m) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] lt (Cd r d m x) (Pl r m x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (le (var 0) (Syn.shift m) ⟶
      lt (Cd r d (var 0) (Syn.shift x)) (Pl r (var 0) (Syn.shift x))) := by
    refine PRA.qfInd _ ⟨le_QF _ _, lt_QF _ _⟩ ?_ ?_
    · simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact .impI (lt_base r d x)
    · simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      have hf := hb.allOpen
      refine .impI ?_
      have hk : (le (succ (var 0)) (Syn.shift m) ::
          (le (var 0) (Syn.shift m) ⟶ lt (Cd r d (var 0) (Syn.shift x)) (Pl r (var 0) (Syn.shift x))) ::
          Γ.map Fm.shift) ⊢[PRAAx] le (succ (var 0)) (Syn.shift m) := Prf.hyp0
      exact lt_step (Prf.impE hf.wk.wk hk) (Prf.impE Prf.hyp1 (le_trans (le_succ_self _) hk))
  have h2 := Prf.allE m hall
  simp only [Fm.subst_imp, subst_le, subst_lt, subst_ap2, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 (le_refl m)

/-! ## Decoding -/

theorem shift_le' {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) :
    Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_le h

/-- `a < b` gives `b = succ (pred b)`. -/
theorem pos_of_lt {a b : PTm n} (h : Γ ⊢[PRAAx] lt a b) : Γ ⊢[PRAAx] b ≐ succ (pred b) := by
  refine eq_succ_pred (y := a + monus b (succ a)) ?_
  ipra_lc natEq (eq_add_of_le h)

section decode

variable {r d : PTm 2} {x i t : PTm n}

/-- The digit bound restricted to the prefix of length `i`, and at the index `i`. -/
theorem digits_prefix
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ i + t)) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift i) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x))) := by
  have hit : Γ ⊢[PRAAx] le i (succ i + t) := by ipra_le 1 + 𝔟 t
  refine .allI (.impI ?_)
  exact Prf.impE hb.allOpen.wk (lt_of_lt_of_le Prf.hyp0 (shift_le' hit).wk)

theorem digit_at
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ i + t)) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] lt (inst2 d i x) (inst2 r i x) := by
  have a := Prf.allE i hb
  simp only [Fm.subst_imp, subst_lt, subst_inst2, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift] at a
  refine Prf.impE a ?_
  show Γ ⊢[PRAAx] le (succ i) (succ i + t)
  ipra_le 𝔟 t

/-- `Tl i (t + 1) = d_i + r_i · Tl (i + 1) t`, and `Cd (i + 1 + t) = Pl i · Tl i (t + 1) + Cd i`. -/
theorem suffix_step
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ i + t)) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] (Tl r d i (succ t) x ≐ inst2 d i x + inst2 r i x * Tl r d (succ i) t x) ⋏
      (Cd r d (succ i + t) x ≐ Pl r i x * Tl r d i (succ t) x + Cd r d i x) := by
  have hlt := code_lt r d x i (digits_prefix hb)
  have ci : Γ ⊢[PRAAx] i + succ t ≐ succ i + t := by ipra_ring
  have eC' := sum_succ' (Γ := Γ) (dP r d) i x
  rw [inst2_dP] at eC'
  have eC := natEq eC'
  have hE : Γ ⊢[PRAAx] Pl r i x * Tl r d i (succ t) x + Cd r d i x ≐
      Pl r i x * (inst2 d i x + inst2 r i x * Tl r d (succ i) t x) + Cd r d i x := by
    ipra_lc -natEq (code_split r d i (succ t) x) + natEq (congrAp2 (sumF (dP r d)) ci (.eqRefl x)) +
      natEq (code_split r d (succ i) t x) + eC + 𝔟 (Tl r d (succ i) t x) * natEq (prod_succ' r i x)
  have hC : Γ ⊢[PRAAx] Cd r d (succ i + t) x ≐ Pl r i x * Tl r d i (succ t) x + Cd r d i x := by
    ipra_lc natEq (code_split r d i (succ t) x) - natEq (congrAp2 (sumF (dP r d)) ci (.eqRefl x))
  exact .andI (Prf.andE₁ (euclid_unique hE hlt hlt)) hC

/-- "Mixed-radix decoding": if `d_j < r_j` for `j < i + 1 + t`, the digit at `i` of the code of length
`i + 1 + t` is `((Cd (i + 1 + t)) div (Pl i)) mod r_i = d_i`. -/
theorem decode
    (hb : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ i + t)) ⟶
      lt (inst2 d (var 0) (Syn.shift x)) (inst2 r (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] rem (quo (Cd r d (succ i + t) x) (Pl r i x)) (inst2 r i x) ≐ inst2 d i x := by
  have hlt := code_lt r d x i (digits_prefix hb)
  have hdi := digit_at hb
  have ss := suffix_step hb
  have hPp := pos_of_lt hlt
  have hRp := pos_of_lt hdi
  have hz : Γ ⊢[PRAAx] Cd r d (succ i + t) x ≐ succ (pred (Pl r i x)) * Tl r d i (succ t) x + Cd r d i x :=
    (Prf.andE₂ ss).eqTrans (congrAdd (congrMul hPp (.eqRefl _)) (.eqRefl _))
  have q1 := Prf.andE₁ (div_mod_unique hz (le_congr (.eqRefl _) hPp hlt))
  have q1' : Γ ⊢[PRAAx] quo (Cd r d (succ i + t) x) (Pl r i x) ≐ Tl r d i (succ t) x :=
    (congrAp2 quoF (.eqRefl _) hPp).eqTrans q1
  have hz' : Γ ⊢[PRAAx] Tl r d i (succ t) x ≐
      succ (pred (inst2 r i x)) * Tl r d (succ i) t x + inst2 d i x :=
    (Prf.andE₁ ss).eqTrans ((add_comm _ _).eqTrans (congrAdd (congrMul hRp (.eqRefl _)) (.eqRefl _)))
  have q2 := Prf.andE₂ (div_mod_unique hz' (le_congr (.eqRefl _) hRp hdi))
  exact (congrAp2 remF q1' hRp).eqTrans q2

end decode

end LeanProofs.IPRA.Foundations.MixedRadix

export_ipra Foundations.MixedRadix (prod_succ')
