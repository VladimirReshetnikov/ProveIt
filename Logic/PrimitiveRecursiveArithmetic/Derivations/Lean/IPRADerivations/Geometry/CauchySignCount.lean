import IPRADerivations.Foundations.ProductSumDomination
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Combinatorics.CoefficientLogConcave
import IPRADerivations.Probability.Variance

/-!
# The sign count of Cauchy's rigidity argument

Packet: `geometry/platonic_solids_ipra`, Section "Finite geometric rigidity":

* `lem:four`, first sentence of its proof: "A cyclic sign sequence has an even number of
  changes."
* `lem:signcount` ("No everywhere-four-change labeling"): "A face walk of length three has at
  most two sign changes. For `d ≥ 4`, it has at most `d ≤ 2d − 4`. Count changes at the
  corners, either by vertices or by face walks. Since the total face-walk length is `2E`, the
  resulting count `S` satisfies `4V ≤ S ≤ Σ_f (2 d_f − 4) = 4E − 4F = 4V − 8`, a contradiction."

Derived here. A cyclic sequence of two signs is the sequence of bits `s_i = sg f(i, x)`,
`i = 0, …, e`, of a term-defined body `f` (the two signs are "zero" and "nonzero"), with the
change bits `c_i = [s_i ≠ s_{i+1}]`:

* `bit_cases`, `xor_bit`: a term with `a² = a` is `0` or `1`, and `[a ≠ b] + 2ab = a + b`;
* `path_changes`: along a walk, `Σ_{i<k} c_i + s_0 + s_k + 2 Σ_{i<k} s_i s_{i+1} = 2 Σ_{i≤k} s_i`;
* `cyclic_changes_even`: the number `C` of cyclic changes satisfies `C + 2 M = 2 T`, where `T` is
  the number of ones and `M` the number of cyclically adjacent pairs of ones; so `C` is even
  (`C = 2 (T − M)`, twice the number of blocks of ones);
* `face_bound`: a face walk of length `d ≥ 3` with `c ≤ d` changes and `c + 2M = 2T` has
  `c + 4 ≤ 2d`;
* `sign_count`: for families `d_f`, `c_f` (`f < F`) and `w_v` (`v < V`) with `c_f + 4 ≤ 2 d_f`,
  `Σ_f d_f = 2E`, `4 ≤ w_v`, `Σ_v w_v = Σ_f c_f` (the corners counted by vertices and by face
  walks) and Euler's relation `V + F = E + 2`: a contradiction.

Hypotheses of `sign_count`, not derived: the face walks of a rotation graph and the corner
bijection behind `Σ_v w_v = Σ_f c_f`, and Euler's relation for a component (`lem:rotation`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.CauchySignCount

open_ipra
open LeanProofs.IPRA.Combinatorics.Stirling (sg)
open LeanProofs.IPRA.Combinatorics.CoefficientLogConcave (inst2_mul inst2_monus)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open LeanProofs.IPRA.Foundations.BoundedReflection (sgB inst2_sgB sg_cases)
open LeanProofs.IPRA.Foundations.ProductSumDomination (sum_lin_le)
open LeanProofs.IPRA.Probability.Variance (sum_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

abbrev three : PTm n := succ two
abbrev four : PTm n := succ three

/-! ## Bits -/

/-- A term with `a² = a` is `0` or `1`. -/
theorem bit_cases {a : PTm n} (h : Γ ⊢[PRAAx] a * a ≐ a) : Γ ⊢[PRAAx] (a ≐ zero) ⋎ (a ≐ one) := by
  refine .orE (zero_or_succ a) (.orI₁ Prf.hyp0) (.orI₂ ?_)
  have z : ((a ≐ succ (pred a)) :: Γ) ⊢[PRAAx] pred a * a ≐ zero := by
    ipra_lc natEq (h.wk (ψ := a ≐ succ (pred a))) - 𝔞 a * natEq (Prf.hyp0 (Γ := Γ) (φ := a ≐ succ (pred a)))
  refine .orE (zero_or_zero_of_mul z) ?_ ?_
  · exact Prf.hyp1.eqTrans (congrSucc Prf.hyp0)
  · exact .botE _ (succ_ne_zero (Prf.hyp1.eqSymm.eqTrans Prf.hyp0))

/-- The value of `[a ≠ b] + 2ab` from the values of `a` and `b`. -/
theorem xor_val {a b α β v : PTm n} (ha : Γ ⊢[PRAAx] a ≐ α) (hb : Γ ⊢[PRAAx] b ≐ β)
    (hv : Γ ⊢[PRAAx] monus one (eqb α β) ≐ v) (he : Γ ⊢[PRAAx] v + two * (α * β) ≐ α + β) :
    Γ ⊢[PRAAx] monus one (eqb a b) + two * (a * b) ≐ a + b :=
  (congrAdd ((congrMonus (.eqRefl _) (congrEqb ha hb)).eqTrans hv)
    (congrMul (.eqRefl _) (congrMul ha hb))).eqTrans (he.eqTrans (congrAdd ha hb).eqSymm)

theorem xor_same (x : PTm n) : Γ ⊢[PRAAx] monus one (eqb x x) ≐ zero :=
  (congrMonus (.eqRefl _) (eqb_of_eq (.eqRefl x))).eqTrans (monus_self one)

/-- For bits, `[a ≠ b] + 2ab = a + b`. -/
theorem xor_bit {a b : PTm n} (ha : Γ ⊢[PRAAx] (a ≐ zero) ⋎ (a ≐ one))
    (hb : Γ ⊢[PRAAx] (b ≐ zero) ⋎ (b ≐ one)) :
    Γ ⊢[PRAAx] monus one (eqb a b) + two * (a * b) ≐ a + b := by
  refine .orE ha ?_ ?_
  · refine .orE hb.wk ?_ ?_
    · exact xor_val Prf.hyp1 Prf.hyp0 (xor_same zero) (by ipra_ring)
    · exact xor_val (v := one) Prf.hyp1 Prf.hyp0
        ((congrMonus (.eqRefl _) (eqb_zero_of_lt (zero_lt_succ zero))).eqTrans (monus_zero one))
        (by ipra_ring)
  · refine .orE hb.wk ?_ ?_
    · exact xor_val (v := one) Prf.hyp1 Prf.hyp0
        ((congrMonus (.eqRefl _) (eqb_zero_of_gt (zero_lt_succ zero))).eqTrans (monus_zero one))
        (by ipra_ring)
    · exact xor_val Prf.hyp1 Prf.hyp0 (xor_same one) (by ipra_ring)

/-! ## Changes along a walk -/

section Walk

variable (f : PTm 2)

/-- The change bit `[s_i ≠ s_{i+1}]` of the signs `s_i = sg f(i, x)`. -/
def cB : PTm 2 := monus one (eqb (sgB f) (shiftBody (sgB f)))
/-- `s_i s_{i+1}`. -/
def mB : PTm 2 := sgB f * shiftBody (sgB f)

/-- The sign `s_i`. -/
abbrev sgn (i x : PTm n) : PTm n := inst2 (sgB f) i x

theorem inst2_cB (i x : PTm n) :
    inst2 (cB f) i x = monus one (eqb (sgn f i x) (sgn f (succ i) x)) := by
  have e : inst2 (eqb (sgB f) (shiftBody (sgB f))) i x =
      eqb (inst2 (sgB f) i x) (inst2 (shiftBody (sgB f)) i x) := by simp [inst2]
  have o : inst2 (one : PTm 2) i x = one := by simp [inst2]
  rw [cB, inst2_monus, e, o, inst2_shiftBody]

theorem inst2_mB (i x : PTm n) : inst2 (mB f) i x = sgn f i x * sgn f (succ i) x := by
  rw [mB, inst2_mul, inst2_shiftBody]

theorem sgn_bit (i x : PTm n) : Γ ⊢[PRAAx] (sgn f i x ≐ zero) ⋎ (sgn f i x ≐ one) := by
  have h := sg_cases (Γ := Γ) (inst2 f i x)
  rw [← inst2_sgB] at h
  exact h

/-- The step of `path_changes`. -/
theorem path_step {x k : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF (cB f)) k x + sgn f zero x + sgn f k x +
      two * ap2 (sumF (mB f)) k x ≐ two * ap2 (sumF (sgB f)) (succ k) x) :
    Γ ⊢[PRAAx] ap2 (sumF (cB f)) (succ k) x + sgn f zero x + sgn f (succ k) x +
      two * ap2 (sumF (mB f)) (succ k) x ≐ two * ap2 (sumF (sgB f)) (succ (succ k)) x := by
  have c₁ := sum_succ' (Γ := Γ) (cB f) k x
  rw [inst2_cB] at c₁
  have m₁ := sum_succ' (Γ := Γ) (mB f) k x
  rw [inst2_mB] at m₁
  ipra_lc natEq c₁ + 2 * natEq m₁ - 2 * natEq (sum_succ' (Γ := Γ) (sgB f) (succ k) x) + natEq ih +
    natEq (xor_bit (sgn_bit (Γ := Γ) f k x) (sgn_bit f (succ k) x))

/-- The induction formula of `path_changes`; variable `0 = k`. -/
abbrev pathF (x : PTm n) : Fm PTm (n + 1) :=
  ap2 (sumF (cB f)) (var 0) (Syn.shift x) + sgn f zero (Syn.shift x) +
      sgn f (var 0) (Syn.shift x) + two * ap2 (sumF (mB f)) (var 0) (Syn.shift x) ≐
    two * ap2 (sumF (sgB f)) (succ (var 0)) (Syn.shift x)

/-- `Σ_{i<k} c_i + s_0 + s_k + 2 Σ_{i<k} s_i s_{i+1} = 2 Σ_{i≤k} s_i`. -/
theorem path_changes (k x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cB f)) k x + sgn f zero x + sgn f k x +
      two * ap2 (sumF (mB f)) k x ≐ two * ap2 (sumF (sgB f)) (succ k) x := by
  have hall : Γ ⊢[PRAAx] Fm.all (pathF f x) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] ap2 (sumF (cB f)) zero x + sgn f zero x + sgn f zero x +
          two * ap2 (sumF (mB f)) zero x ≐ two * ap2 (sumF (sgB f)) (succ zero) x := by
        ipra_lc natEq (sum_zero (Γ := Γ) (cB f) x) + 2 * natEq (sum_zero (Γ := Γ) (mB f) x) -
          2 * natEq ((sum_succ' (Γ := Γ) (sgB f) zero x).eqTrans (congrAdd (sum_zero _ _) (.eqRefl _)))
      simpa [subst_inst2] using b
    · have st : (pathF f x :: Γ.map Fm.shift) ⊢[PRAAx]
          ap2 (sumF (cB f)) (succ (var 0)) (Syn.shift x) + sgn f zero (Syn.shift x) +
              sgn f (succ (var 0)) (Syn.shift x) +
              two * ap2 (sumF (mB f)) (succ (var 0)) (Syn.shift x) ≐
            two * ap2 (sumF (sgB f)) (succ (succ (var 0))) (Syn.shift x) :=
        path_step f Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero, subst_inst2] using st
  have h2 := Prf.allE k hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero, subst_inst2] using h2

/-- "A cyclic sign sequence has an even number of changes": for the signs `s_0, …, s_e`,
`C + 2 M = 2 T` with `C` the number of cyclic changes, `M` the number of cyclically adjacent
pairs of ones and `T` the number of ones. -/
theorem cyclic_changes_even (e x : PTm n) :
    Γ ⊢[PRAAx]
      (ap2 (sumF (cB f)) e x + monus one (eqb (sgn f e x) (sgn f zero x))) +
        two * (ap2 (sumF (mB f)) e x + sgn f e x * sgn f zero x) ≐
      two * ap2 (sumF (sgB f)) (succ e) x := by
  ipra_lc natEq (path_changes (Γ := Γ) f e x) + natEq (xor_bit (sgn_bit (Γ := Γ) f e x) (sgn_bit f zero x))

end Walk

/-! ## The bound for one face walk -/

/-- A face walk of length `d ≥ 3` with `c ≤ d` sign changes, `c` even, has `c + 4 ≤ 2d`. -/
theorem face_bound {c d M T : PTm n} (h3 : Γ ⊢[PRAAx] le three d) (hc : Γ ⊢[PRAAx] le c d)
    (hpar : Γ ⊢[PRAAx] c + two * M ≐ two * T) : Γ ⊢[PRAAx] le (c + four) (two * d) := by
  refine .orE (lt_or_eq_of_le h3) ?_ ?_
  · -- `d ≥ 4`
    refine le_of_eq_add (d := monus d c + monus d (succ three)) ?_
    ipra_lc natEq (eq_add_of_le (hc.wk (ψ := lt three d))) +
      natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := lt three d)))
  · -- `d = 3`
    have hd : ((three ≐ d) :: Γ) ⊢[PRAAx] three ≐ d := Prf.hyp0
    have hc3 : ((three ≐ d) :: Γ) ⊢[PRAAx] le c three := le_congr (.eqRefl _) hd.eqSymm hc.wk
    refine .orE (lt_or_eq_of_le hc3) ?_ ?_
    · have hc2 : (lt c three :: (three ≐ d) :: Γ) ⊢[PRAAx] le c two :=
        (succ_monus_succ c two).eqSymm.eqTrans Prf.hyp0
      refine le_of_eq_add (d := monus two c) ?_
      ipra_lc natEq (eq_add_of_le hc2) - 2 * natEq (hd.wk (ψ := lt c three))
    · have e₃ := natEq (Prf.hyp0 (Γ := (three ≐ d) :: Γ) (φ := c ≐ three))
      refine even_ne_odd (k := T) (m := succ M) _ ?_
      ipra_lc -natEq ((hpar.wk (ψ := three ≐ d)).wk (ψ := c ≐ three)) + e₃

/-! ## The count -/

/-- `lem:signcount`, the count: `4V ≤ S ≤ 4E − 4F = 4V − 8` is impossible. -/
theorem sign_count (cF dF wV : PTm 2) {V E F x : PTm n} (φ : Fm PTm n)
    (hf : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift F) ⟶
      le (inst2 cF (var 0) (Syn.shift x) + four) (two * inst2 dF (var 0) (Syn.shift x))))
    (hE : Γ ⊢[PRAAx] ap2 (sumF dF) F x ≐ two * E)
    (hw : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift V) ⟶
      le four (inst2 wV (var 0) (Syn.shift x))))
    (hcorner : Γ ⊢[PRAAx] ap2 (sumF wV) V x ≐ ap2 (sumF cF) F x)
    (hEuler : Γ ⊢[PRAAx] V + F ≐ E + two) : Γ ⊢[PRAAx] φ := by
  have s₁ : Γ ⊢[PRAAx] le (ap2 (sumF cF) F x * one + four * ap2 (sumF (one : PTm 2)) F x)
      (ap2 (sumF dF) F x * two + zero * ap2 (sumF (zero : PTm 2)) F x) := by
    refine sum_lin_le cF (one : PTm 2) dF (zero : PTm 2) (.allI (.impI ?_))
    refine le_congr ?_ ?_ (Prf.impE hf.allOpen.wk Prf.hyp0)
    · simp only [inst2, Syn.shift]
      simp
      ipra_ring
    · simp only [inst2, Syn.shift]
      simp
      ipra_ring
  have s₂ : Γ ⊢[PRAAx] le (ap2 (sumF (one : PTm 2)) V x * four +
        zero * ap2 (sumF (zero : PTm 2)) V x)
      (ap2 (sumF wV) V x * one + zero * ap2 (sumF (zero : PTm 2)) V x) := by
    refine sum_lin_le (one : PTm 2) (zero : PTm 2) wV (zero : PTm 2) (.allI (.impI ?_))
    refine le_congr ?_ ?_ (Prf.impE hw.allOpen.wk Prf.hyp0)
    · simp only [inst2, Syn.shift]
      simp
      ipra_ring
    · simp only [inst2, Syn.shift]
      simp
      ipra_ring
  have a₁ : Γ ⊢[PRAAx] le (ap2 (sumF cF) F x + four * F) (two * (two * E)) := by
    refine le_congr ?_ ?_ s₁
    · ipra_lc 4 * natEq (sum_one (Γ := Γ) F x)
    · ipra_lc 2 * natEq hE
  have a₂ : Γ ⊢[PRAAx] le (four * V) (ap2 (sumF cF) F x) := by
    refine le_congr ?_ ?_ s₂
    · ipra_lc 4 * natEq (sum_one (Γ := Γ) V x)
    · ipra_lc natEq hcorner
  have tot : Γ ⊢[PRAAx] le (four * V + four * F) (two * (two * E)) :=
    le_trans (add_le_add_right (four * F) a₂) a₁
  refine not_succ_le_self (two * (two * E)) φ (le_trans (le_of_eq_add (d := four + three) ?_) tot)
  ipra_lc 4 * natEq hEuler

end LeanProofs.IPRA.Geometry.CauchySignCount
