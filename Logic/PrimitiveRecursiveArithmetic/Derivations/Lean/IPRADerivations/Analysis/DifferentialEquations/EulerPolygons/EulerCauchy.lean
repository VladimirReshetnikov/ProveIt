import IPRADerivations.Analysis.DifferentialEquations.EulerPolygons.EulerRefinement

/-!
# The dyadic Euler polygons are a Cauchy sequence with an explicit modulus

Packet: `analysis/ipra_certified_continuation_2026-11-19`, `paper/sections/07_ode.tex`, Theorem
`thm:ode-produced-refinement`, `eq:ode-produced-cauchy`: "Consequently, for `s ≥ r`,
`‖X_{2^r}(t) − X_{2^s}(t)‖ ≤ C (2^{−r} − 2^{−s}) ≤ C 2^{−r}`", at the nodes `t = a / 2^r` of the level `r`
(in particular at the endpoint `t = 1`, `a = 2^r`). The proof of the paper: "Finally add this bound for
`n = 2^r, 2^{r+1}, …, 2^{s−1}`. The finite geometric sum is `∑_{i=r}^{s−1} 2^{−i−1} = 2^{−r} − 2^{−s}`."

At the level `r + k` the node `a / 2^r` has the index `a 2^k` on the mesh `2^{r+k}`. With
`crossNum = N_r D_{r+k} − N_{r+k} D_r`, the numerator of the difference of the two values `N_r / D_r` and
`N_{r+k} / D_{r+k}`:

* `refine_at`: `eq:ode-produced-refine` (`EulerRefinement.euler_refinement`) for a mesh and a fine mesh that are
  given by terms provably equal to `n₀ + 1` and to its double;
* `tele_le`: one step of a dyadic telescoping for three rational values, by the triangle inequality
  `EulerAlgebra.tele_step`; `cauchy_step`: its instance for the three node values at the levels `r`, `r + k`,
  `r + k + 1`, with the refinement estimate at the level `r + k`;
* `euler_cauchy`: by quantifier-free induction on `k`,
  `2^{r+k} |crossNum| + C D_r D_{r+k} ≤ C 2^k D_r D_{r+k}`, which is
  `‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C (2^{−r} − 2^{−(r+k)})`, the sharp finite geometric sum;
* `euler_cauchy_tail`: `2^{r+k} |crossNum| ≤ C 2^k D_r D_{r+k}`, which is `‖…‖ ≤ C 2^{−r}`.

The sum is evaluated exactly, level by level, because the exact Euler values have no common denominator over
all levels: `Foundations/OdeRefinement.geometric_cauchy`, which bounds a natural-valued distance at one fixed
scale by `2C`, is the same telescoping without the closed form and is not needed for the exact arrays.
-/

namespace LeanProofs.IPRA.Analysis.EulerCauchy

open_ipra
open LeanProofs.IPRA.Foundations.TupleRecursion LeanProofs.IPRA.Foundations.SignedNorms
  LeanProofs.IPRA.Foundations.SignedCone LeanProofs.IPRA.Analysis.EulerProgram
  LeanProofs.IPRA.Analysis.EulerNodeBound LeanProofs.IPRA.Analysis.EulerRefinement
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (pw_pos')

variable {n d : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The numerator of the difference of two node values -/

/-- The numerator of the `c`-th component of `X_{nn,j} − X_{nn',j'}`, over `Xd(j; nn) · Xd(j'; nn')`. -/
def crossNum (B : Kernel d) (v : Fin d → ZT n) (dv x j nn j' nn' : PTm n) (c : Fin d) : ZT n :=
  Xn B v j nn x c * ZT.ofNat (Xd B dv j' nn' x) - Xn B v j' nn' x c * ZT.ofNat (Xd B dv j nn x)

theorem subst_crossNum {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n)
    (dv x j nn j' nn' : PTm n) (c : Fin d) :
    (crossNum B v dv x j nn j' nn' c).subst σ =
      crossNum B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ x) (Syn.subst σ j) (Syn.subst σ nn)
        (Syn.subst σ j') (Syn.subst σ nn') c := by
  simp only [crossNum, ZT.subst_sub, ZT.subst_mul, ZT.subst_ofNat, subst_Xn, subst_Xd]

theorem toZ_crossNum (B : Kernel d) (v : Fin d → ZT n) (dv x j nn j' nn' : PTm n) (c : Fin d) :
    ZT.toZ Γ (crossNum B v dv x j nn j' nn' c) =
      ZT.toZ Γ (Xn B v j nn x c) * 𝔞 (Xd B dv j' nn' x) - ZT.toZ Γ (Xn B v j' nn' x c) * 𝔞 (Xd B dv j nn x) := by
  simp only [crossNum, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]

theorem mk_two : (𝔞 (two : PTm n) : Groth (Q Γ)) = 2 := by
  simp only [Q.mk_succ, Q.mk_zero, map_add, map_one, map_zero]; ring

theorem congrDbl {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] dbl a ≐ dbl b := congrAdd h h

/-- `2^{k+1} = 2^k · 2` in the ring of differences. -/
theorem mk_pw_two_succ (k : PTm n) : (𝔞 (pw two (succ k)) : Groth (Q Γ)) = 𝔞 (pw two k) * 2 := by
  have q := natEq (pw_succ (Γ := Γ) two k)
  simp only [Q.mk_mul, map_mul] at q
  rw [q, mk_two]

/-- One step of a dyadic telescoping for rational values `a / α`, `b / β`, `z / ζ` (signed numerators over
natural denominators): from `s |a β − b α| + C α β ≤ C P α β` (the distance of the first two is at most
`C (P − 1)/s`) and `t |b ζ − z β| ≤ C β ζ` with `t = 2s` (the distance of the last two is at most `C/(2s)`),
`t |a ζ − z α| + C α ζ ≤ C (2P) α ζ`. The triangle inequality is `EulerAlgebra.tele_step`, and the positive factor
`s β` is cancelled. -/
theorem tele_le {a b z : ZT n} {α β ζ s t C P P' : PTm n}
    (ih : Γ ⊢[PRAAx] le (s * abs (a * ZT.ofNat β - b * ZT.ofNat α) + C * (α * β)) (C * P * (α * β)))
    (R : Bd (Nonneg Γ) (𝔞 t * (ZT.toZ Γ b * 𝔞 ζ - ZT.toZ Γ z * 𝔞 β)) (𝔞 C * (𝔞 β * 𝔞 ζ)))
    (et : (𝔞 t : Groth (Q Γ)) = 2 * 𝔞 s) (eP : (𝔞 P' : Groth (Q Γ)) = 𝔞 P * 2)
    (hpos : Γ ⊢[PRAAx] le one (s * β)) :
    Γ ⊢[PRAAx] le (t * abs (a * ZT.ofNat ζ - z * ZT.ofNat α) + C * (α * ζ)) (C * P' * (α * ζ)) := by
  have IH : Bd (Nonneg Γ) (𝔞 s * (ZT.toZ Γ a * 𝔞 β - ZT.toZ Γ b * 𝔞 α))
      (𝔞 (C * P * (α * β)) - 𝔞 (C * (α * β))) :=
    (bd_of_le_add ih).congr (by simp only [ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]) rfl
  have T := EulerAlgebra.tele_step nnCone (nn_term s) (nn_term t) (nn_term α) (nn_term ζ) IH R
  refine Common.mul_cancel_le hpos ?_
  have key := le_abs_of_bd (σ := s * β * t) (e := s * β * (C * (α * ζ))) (c := s * β * (C * P' * (α * ζ)))
    (u := a * ZT.ofNat ζ - z * ZT.ofNat α)
    (T.congr (by simp only [Q.mk_mul, map_mul, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_ofNat]; ring)
      (by simp only [Q.mk_mul, map_mul]; rw [et, eP]; ring))
  exact le_congr (by ipra_ring) (.eqRefl _) key

section Refine

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x : PTm n}

/-- The denominators are positive, for a mesh given by a term that is provably a successor. -/
theorem Xd_pos_at {nn n₀ j : PTm n} (hm : Γ ⊢[PRAAx] nn ≐ succ n₀) (hK : Γ ⊢[PRAAx] KBound B x K)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hj : Γ ⊢[PRAAx] le j nn) : Γ ⊢[PRAAx] lt zero (Xd B dv j nn x) :=
  le_congr (.eqRefl _) (congrXd B dv x (.eqRefl j) hm).eqSymm
    (Xd_pos hK hdv (le_congr (.eqRefl j) hm hj))

/-- `eq:ode-produced-refine` at a coarse node, for a mesh `nn = n₀ + 1`, the fine mesh `nn2 = 2 nn` and the
fine index `i2 = 2 i` given up to provable equality. -/
theorem refine_at {nn n₀ i i2 nn2 : PTm n} (hm : Γ ⊢[PRAAx] nn ≐ succ n₀) (hi2 : Γ ⊢[PRAAx] i2 ≐ dbl i)
    (hn2 : Γ ⊢[PRAAx] nn2 ≐ dbl nn) (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (hi : Γ ⊢[PRAAx] le i nn)
    (c : Fin d) :
    Bd (Nonneg Γ) (𝔞 nn2 * (ZT.toZ Γ (Xn B v i nn x c) * 𝔞 (Xd B dv i2 nn2 x) -
        ZT.toZ Γ (Xn B v i2 nn2 x c) * 𝔞 (Xd B dv i nn x)))
      (𝔞 (Cc K L U) * (𝔞 (Xd B dv i nn x) * 𝔞 (Xd B dv i2 nn2 x))) := by
  have h := bd_of_le (euler_refinement hK hL hdv hv (le_congr (.eqRefl i) hm hi) c)
  have hn2' : Γ ⊢[PRAAx] nn2 ≐ dbl (succ n₀) := hn2.eqTrans (congrDbl hm)
  have cX1 := congrXn (Γ := Γ) B v x c (.eqRefl i) hm
  have cX2 := congrXn (Γ := Γ) B v x c hi2 hn2'
  have cD1 := natEq (congrXd (Γ := Γ) B dv x (.eqRefl i) hm)
  have cD2 := natEq (congrXd (Γ := Γ) B dv x hi2 hn2')
  have cM := natEq hn2'
  refine h.congr ?_ ?_
  · rw [toZ_errNum, cX1, cX2, cD1, cD2, cM]
  · simp only [Q.mk_mul, map_mul]
    rw [cD1, cD2]

end Refine

/-! ## The telescoping -/

/-- The invariant of the telescoping: `2^{r+k} |crossNum| + C D_r D_{r+k} ≤ C 2^k D_r D_{r+k}`. -/
def CauchyInv (B : Kernel d) (v : Fin d → ZT n) (dv U K L x r a k : PTm n) : Fm PTm n :=
  conjFin fun c =>
    le (pw two (r + k) * abs (crossNum B v dv x a (pw two r) (a * pw two k) (pw two (r + k)) c) +
        Cc K L U * (Xd B dv a (pw two r) x * Xd B dv (a * pw two k) (pw two (r + k)) x))
      (Cc K L U * pw two k * (Xd B dv a (pw two r) x * Xd B dv (a * pw two k) (pw two (r + k)) x))

@[simp] theorem subst_CauchyInv {m : ℕ} (σ : Fin n → PTm m) (B : Kernel d) (v : Fin d → ZT n)
    (dv U K L x r a k : PTm n) :
    (CauchyInv B v dv U K L x r a k).subst σ =
      CauchyInv B (fun l => (v l).subst σ) (Syn.subst σ dv) (Syn.subst σ U) (Syn.subst σ K) (Syn.subst σ L)
        (Syn.subst σ x) (Syn.subst σ r) (Syn.subst σ a) (Syn.subst σ k) := by
  simp only [CauchyInv, subst_le, subst_conjFin, subst_abs, subst_crossNum, subst_Cc, subst_Xd, PTm.subst_mul,
    PTm.subst_add, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

theorem CauchyInv_QF (B : Kernel d) (v : Fin d → ZT n) (dv U K L x r a k : PTm n) :
    (CauchyInv B v dv U K L x r a k).QF :=
  conjFin_QF fun _ => le_QF _ _

section Step

variable {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r a k : PTm n}

/-- The base of the telescoping: the levels `r` and `r + 0` have the same value. -/
theorem cauchy_base (c : Fin d) :
    Γ ⊢[PRAAx] le (pw two (r + zero) *
        abs (crossNum B v dv x a (pw two r) (a * pw two zero) (pw two (r + zero)) c) +
        Cc K L U * (Xd B dv a (pw two r) x * Xd B dv (a * pw two zero) (pw two (r + zero)) x))
      (Cc K L U * pw two zero * (Xd B dv a (pw two r) x * Xd B dv (a * pw two zero) (pw two (r + zero)) x)) := by
  have ea : Γ ⊢[PRAAx] a * pw two zero ≐ a := by
    have p := natEq (pw_zero (Γ := Γ) two)
    apply deriveNat; ipra_simps; rw [p]; ring
  have em : Γ ⊢[PRAAx] pw two (r + zero) ≐ pw two r := congrAp2 powF (add_zero r) (.eqRefl two)
  have cX := congrXn (Γ := Γ) B v x c ea em
  have cD := natEq (congrXd (Γ := Γ) B dv x ea em)
  have p0 := natEq (pw_zero (Γ := Γ) two)
  simp only [Q.mk_one, map_one] at p0
  refine le_abs_of_bd ((Bd.zero nn_zero).congr ?_ ?_)
  · rw [toZ_crossNum, cX, cD]; ring
  · simp only [Q.mk_mul, map_mul]
    rw [p0]; ring

/-- One level of the telescoping. -/
theorem cauchy_step (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L)
    (hdv : Γ ⊢[PRAAx] lt zero dv) (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv))
    (ha : Γ ⊢[PRAAx] le a (pw two r))
    (ih : ∀ c, Γ ⊢[PRAAx] le (pw two (r + k) *
        abs (crossNum B v dv x a (pw two r) (a * pw two k) (pw two (r + k)) c) +
        Cc K L U * (Xd B dv a (pw two r) x * Xd B dv (a * pw two k) (pw two (r + k)) x))
      (Cc K L U * pw two k * (Xd B dv a (pw two r) x * Xd B dv (a * pw two k) (pw two (r + k)) x)))
    (c : Fin d) :
    Γ ⊢[PRAAx] le (pw two (r + succ k) *
        abs (crossNum B v dv x a (pw two r) (a * pw two (succ k)) (pw two (r + succ k)) c) +
        Cc K L U * (Xd B dv a (pw two r) x * Xd B dv (a * pw two (succ k)) (pw two (r + succ k)) x))
      (Cc K L U * pw two (succ k) *
        (Xd B dv a (pw two r) x * Xd B dv (a * pw two (succ k)) (pw two (r + succ k)) x)) := by
  -- the level `r + k`: its mesh, the node, and the next level as its refinement
  have hm : Γ ⊢[PRAAx] pw two (r + k) ≐ succ (pred (pw two (r + k))) := pw_pos' Common.two_pos (r + k)
  have hi : Γ ⊢[PRAAx] le (a * pw two k) (pw two (r + k)) := by
    have e := natEq (pw_add (Γ := Γ) two r k)
    ipra_le sl ha * 𝔞 (pw two k) with e
  have ps := natEq (pw_succ (Γ := Γ) two k)
  have hi2 : Γ ⊢[PRAAx] a * pw two (succ k) ≐ dbl (a * pw two k) := by
    show Γ ⊢[PRAAx] a * pw two (succ k) ≐ a * pw two k + a * pw two k
    apply deriveNat; ipra_simps; rw [ps]; ring
  have hn2 : Γ ⊢[PRAAx] pw two (r + succ k) ≐ dbl (pw two (r + k)) := by
    have e1 : Γ ⊢[PRAAx] r + succ k ≐ succ (r + k) := by ipra_ring
    have e2 : Γ ⊢[PRAAx] pw two (r + k) * two ≐ pw two (r + k) + pw two (r + k) := by ipra_ring
    exact ((congrAp2 powF e1 (.eqRefl two)).eqTrans (pw_succ two (r + k))).eqTrans e2
  have R := refine_at hm hi2 hn2 hK hL hdv hv hi c
  have hpos : Γ ⊢[PRAAx] le one (pw two (r + k) * Xd B dv (a * pw two k) (pw two (r + k)) x) :=
    mul_pos₀ (le_congr (.eqRefl _) hm.eqSymm (succ_pos₀ _)) (Xd_pos_at hm hK hdv hi)
  have eN2 : (𝔞 (pw two (r + succ k)) : Groth (Q Γ)) = 2 * 𝔞 (pw two (r + k)) :=
    (natEq hn2).trans (mk_dbl _)
  exact tele_le (ih c) R eN2 (mk_pw_two_succ k) hpos

end Step

/-- `eq:ode-produced-cauchy`, the sharp form `‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C (2^{−r} − 2^{−(r+k)})` at the
node `t = a / 2^r`: `2^{r+k} |crossNum| + C D_r D_{r+k} ≤ C 2^k D_r D_{r+k}`. -/
theorem euler_cauchy {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r a : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (ha : Γ ⊢[PRAAx] le a (pw two r)) (k : PTm n) :
    Γ ⊢[PRAAx] CauchyInv B v dv U K L x r a k := by
  have hvs : ∀ l, Γ.map Fm.shift ⊢[PRAAx] le (abs (zshift (v l))) (Syn.shift U * Syn.shift dv) := fun l => by
    have h := (hv l).shift
    simp only [Fm.shift, subst_le, subst_abs, PTm.subst_mul] at h
    exact h
  have hdvs : Γ.map Fm.shift ⊢[PRAAx] lt zero (Syn.shift dv) := by
    have h := hdv.shift
    simp only [Fm.shift, subst_lt, ConciseIPRA.PTm.subst_zero] at h
    exact h
  have has : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (pw two (Syn.shift r)) := by
    have h := ha.shift
    simp only [Fm.shift, subst_le, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h
    exact h
  have hall : Γ ⊢[PRAAx] Fm.all (CauchyInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K)
      (Syn.shift L) (Syn.shift x) (Syn.shift r) (Syn.shift a) (var 0)) := by
    ipra_qfind (CauchyInv_QF _ _ _ _ _ _ _ _ _ _) [subst_CauchyInv, zshift_inst, zshift_repl]
    · exact conjFin_intro fun c => cauchy_base c
    · have H0 : (CauchyInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K) (Syn.shift L)
          (Syn.shift x) (Syn.shift r) (Syn.shift a) (var 0) :: Γ.map Fm.shift) ⊢[PRAAx]
          CauchyInv B (fun l => zshift (v l)) (Syn.shift dv) (Syn.shift U) (Syn.shift K) (Syn.shift L)
            (Syn.shift x) (Syn.shift r) (Syn.shift a) (var 0) := Prf.hyp0
      exact conjFin_intro fun c =>
        cauchy_step (kbound_shift hK).wk (lbound_shift hL).wk hdvs.wk (fun l => (hvs l).wk) has.wk
          (conjFin_elim H0) c
  have h := Prf.allE k hall
  simp only [subst_CauchyInv, zshift_inst, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h
  exact h

/-- `eq:ode-produced-cauchy`, the tail form `‖X_{2^r}(t) − X_{2^{r+k}}(t)‖ ≤ C 2^{−r}` at the node
`t = a / 2^r`: `2^{r+k} |crossNum| ≤ C 2^k D_r D_{r+k}`. -/
theorem euler_cauchy_tail {B : Kernel d} {v : Fin d → ZT n} {dv U K L x r a : PTm n}
    (hK : Γ ⊢[PRAAx] KBound B x K) (hL : Γ ⊢[PRAAx] LBound B x L) (hdv : Γ ⊢[PRAAx] lt zero dv)
    (hv : ∀ i, Γ ⊢[PRAAx] le (abs (v i)) (U * dv)) (ha : Γ ⊢[PRAAx] le a (pw two r)) (k : PTm n)
    (c : Fin d) :
    Γ ⊢[PRAAx] le (pw two (r + k) * abs (crossNum B v dv x a (pw two r) (a * pw two k) (pw two (r + k)) c))
      (Cc K L U * pw two k * (Xd B dv a (pw two r) x * Xd B dv (a * pw two k) (pw two (r + k)) x)) :=
  le_trans (le_add_right _ _) (conjFin_elim (euler_cauchy hK hL hdv hv ha k) c)

end LeanProofs.IPRA.Analysis.EulerCauchy
