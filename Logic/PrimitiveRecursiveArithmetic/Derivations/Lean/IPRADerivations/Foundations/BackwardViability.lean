import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Foundations.FiniteGluing

/-!
# Backward viability (`ipra_evidence_framework`, "PR backward viability")

Packet: `foundations/ipra_evidence_framework`, Section "Finite constraint amalgamation":
theorem "PR backward viability and certified finite chain", recursion (1).

A finite compatibility instance (`Instance`) is given by fixed terms in a parameter `p`: a
local test `G(i, a, p)`, an edge test `T(i, a, b, p)` (both true when nonzero), a bound
`B(i, p)` on the candidates of level `i`, and a horizon `h(p)`. The packet's function

`D(h, a) = G(h, a)`, `D(i, a) = G(i, a) · max_{b < B(i+1)} (T(i, a, b) · D(i + 1, b))`

changes its parameter `a` in the recursive call, so it is not a primitive recursion as
written. Here the whole row is one number: `row j p` is the bitmask whose bit `a` is the
viability of candidate `a` at level `h ∸ j` (`j` levels remain), built by ordinary primitive
recursion on `j` with `code` of `Foundations/FiniteSetExponential`, and

`V(j, a, p) = bit a of row j p`.

For candidates below the bound of their level (`i = h ∸ (j + 1)`, `i' = h ∸ j`):

* `V_zero`: `V(0, a) = sg G(h, a)`;
* `V_succ`: `V(j + 1, a) = sg G(i, a) · [∃ b < B(i'). T(i, a, b) · V(j, b) ≠ 0]`, the recursion
  (1) with the maximum as a bounded existence bit;
* `V_unfold`: if `V(j + 1, a) = 1`, then `G(i, a) ≠ 0` and the selected successor
  `nxt(j, a) < B(i')` (least passing candidate) has `T(i, a, nxt) ≠ 0` and `V(j, nxt) = 1`;
* `V_fold`: conversely, `G(i, a) ≠ 0`, `b < B(i')`, `T(i, a, b) ≠ 0` and `V(j, b) = 1` give
  `V(j + 1, a) = 1`.

`V_unfold` and `V_fold` are the two directions of the reverse-row invariant, one level at a
time, with the successor produced by bounded search.

Not derived: the assembled chain `S(x, h)` as a single coded object and its verification
along all levels, the statement for candidates at or above the bound, and the refinement
theorem of the packet.
-/

namespace LeanProofs.IPRA.Foundations.BackwardViability

open_ipra exports
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Probability.ProductPower (dg)
open LeanProofs.IPRA.Foundations.FiniteSetExponential (code ev_curry rem_of_lt dg_lt)
open LeanProofs.IPRA.Foundations.BoundedReflection
  (exB wit ex_intro ex_elim ex_cases sg_cases one_ne_zero)
open LeanProofs.IPRA.Foundations.FiniteGluing (one_of_ne sg_of_ne)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## Bits -/

theorem two_pos : Γ ⊢[PRAAx] (two : PTm k) ≐ succ (pred two) :=
  pos_of_eq_succ (c := one) (.eqRefl _)

/-- A bit is below `2`. -/
theorem lt_two_of_bit {b : PTm k} (h : Γ ⊢[PRAAx] (b ≐ zero) ⋎ (b ≐ one)) :
    Γ ⊢[PRAAx] lt b two :=
  .orE h (lt_congr Prf.hyp0.eqSymm (.eqRefl _) (le_succ_self one))
    (lt_congr Prf.hyp0.eqSymm (.eqRefl _) (le_refl two))

/-- A number below `2` is a bit. -/
theorem bit_of_lt_two {b : PTm k} (h : Γ ⊢[PRAAx] lt b two) :
    Γ ⊢[PRAAx] (b ≐ zero) ⋎ (b ≐ one) := by
  refine .orE (Order.lt_succ_cases h) (.orI₁ ?_) (.orI₂ Prf.hyp0)
  exact (monus_zero b).eqSymm.eqTrans (Order.le_of_lt_succ Prf.hyp0)

/-- A product of two bits is a bit. -/
theorem mul_bit {x y : PTm k} (hx : Γ ⊢[PRAAx] (x ≐ zero) ⋎ (x ≐ one))
    (hy : Γ ⊢[PRAAx] (y ≐ zero) ⋎ (y ≐ one)) : Γ ⊢[PRAAx] (x * y ≐ zero) ⋎ (x * y ≐ one) := by
  refine .orE hx (.orI₁ ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _))) ?_
  refine .orE hy.wk (.orI₁ ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _))) ?_
  exact .orI₂ ((congrMul Prf.hyp1 Prf.hyp0).eqTrans (one_mul _))

/-- If a product of two bits is `1`, the first factor is `1`. -/
theorem left_of_mul_one {x y : PTm k} (hx : Γ ⊢[PRAAx] (x ≐ zero) ⋎ (x ≐ one))
    (h : Γ ⊢[PRAAx] x * y ≐ one) : Γ ⊢[PRAAx] x ≐ one :=
  .orE hx (one_ne_zero _ (h.wk.eqSymm.eqTrans
    ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))) Prf.hyp0

/-- If a product of two bits is `1`, the second factor is `1`. -/
theorem right_of_mul_one {x y : PTm k} (hy : Γ ⊢[PRAAx] (y ≐ zero) ⋎ (y ≐ one))
    (h : Γ ⊢[PRAAx] x * y ≐ one) : Γ ⊢[PRAAx] y ≐ one :=
  .orE hy (one_ne_zero _ (h.wk.eqSymm.eqTrans
    ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)))) Prf.hyp0

/-! ## Instances -/

/-- A finite compatibility instance. -/
structure Instance where
  /-- The local test `G(i, a, p)`; variables `0 = i`, `1 = a`, `2 = p`. -/
  G : PTm 3
  /-- The edge test `T(i, a, b, p)`; variables `0 = i`, `1 = a`, `2 = b`, `3 = p`. -/
  T : PTm 4
  /-- The candidate bound `B(i, p)`; variables `0 = i`, `1 = p`. -/
  B : PTm 2
  /-- The horizon `h(p)`; variable `0 = p`. -/
  hz : PTm 1

namespace Instance

variable (I : Instance)

/-- `G(i, a, p)`. -/
def g (i a p : PTm k) : PTm k := Syn.subst ![i, a, p] I.G
/-- `T(i, a, b, p)`. -/
def t (i a b p : PTm k) : PTm k := Syn.subst ![i, a, b, p] I.T
/-- `B(i, p)`. -/
def bd (i p : PTm k) : PTm k := Syn.subst ![i, p] I.B
/-- `h(p)`. -/
def h (p : PTm k) : PTm k := Syn.subst ![p] I.hz

@[simp] theorem subst_g {m : ℕ} (σ : Fin k → PTm m) (i a p : PTm k) :
    Syn.subst σ (I.g i a p) = I.g (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ p) := by
  simp only [g, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_t {m : ℕ} (σ : Fin k → PTm m) (i a b p : PTm k) :
    Syn.subst σ (I.t i a b p) =
      I.t (Syn.subst σ i) (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ p) := by
  simp only [t, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_bd {m : ℕ} (σ : Fin k → PTm m) (i p : PTm k) :
    Syn.subst σ (I.bd i p) = I.bd (Syn.subst σ i) (Syn.subst σ p) := by
  simp only [bd, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> rfl

@[simp] theorem subst_h {m : ℕ} (σ : Fin k → PTm m) (p : PTm k) :
    Syn.subst σ (I.h p) = I.h (Syn.subst σ p) := by
  simp only [h, Syn.subst_subst]
  congr 1; funext j; fin_cases j; rfl

/-- `T(i, a, b, p) · (bit b of R)` with `i = h(p) ∸ (j + 1)`; variables `0 = b`,
`1 = ⟨a, ⟨j, ⟨R, p⟩⟩⟩`. -/
def f : PTm 2 :=
  I.t (monus (I.h (sndT (sndT (sndT (var 1))))) (succ (fstT (sndT (var 1))))) (fstT (var 1)) (var 0)
      (sndT (sndT (sndT (var 1)))) *
    dg two (var 0) (fstT (sndT (sndT (var 1))))

/-- The entry of the next row at candidate `a`; variables `0 = a`, `1 = ⟨j, ⟨R, p⟩⟩`. -/
def tb : PTm 2 :=
  sg (I.g (monus (I.h (sndT (sndT (var 1)))) (succ (fstT (var 1)))) (var 0) (sndT (sndT (var 1)))) *
    exB I.f (I.bd (monus (I.h (sndT (sndT (var 1)))) (fstT (var 1))) (sndT (sndT (var 1))))
      (pairT (var 0) (var 1))

/-- The entry of the last row; variables `0 = a`, `1 = p`. -/
def t0 : PTm 2 := sg (I.g (I.h (var 1)) (var 0) (var 1))

/-- The last row; variable `0 = p`. -/
def base : PTm 1 := code I.t0 (I.bd (I.h (var 0)) (var 0)) two (var 0)

/-- The next row from the current one; variables `0 = j`, `1 = row j p`, `2 = p`. -/
def step : PTm 3 :=
  code I.tb (I.bd (monus (I.h (var 2)) (succ (var 0))) (var 2)) two
    (pairT (var 0) (pairT (var 1) (var 2)))

/-- `row j p`: the bitmask of viable candidates at level `h(p) ∸ j`. -/
def row (j p : PTm k) : PTm k := ap2 (rec2 I.base I.step) j p

/-- `V(j, a, p)`: candidate `a` at level `h(p) ∸ j` is viable. -/
def V (j a p : PTm k) : PTm k := dg two a (I.row j p)

/-- The selected successor of `a`: the least passing candidate of the next level. -/
def nxt (j a p : PTm k) : PTm k :=
  wit I.f (I.bd (monus (I.h p) j) p) (pairT a (pairT j (pairT (I.row j p) p)))

end Instance

open Instance

section Rows

variable (I : Instance)

theorem row_zero (p : PTm k) :
    Γ ⊢[PRAAx] I.row zero p ≐ code I.t0 (I.bd (I.h p) p) two p := by
  have h := rec2_zero (Γ := Γ) I.base I.step p
  have e : Syn.subst ![p] I.base = code I.t0 (I.bd (I.h p) p) two p := by
    simp [Instance.base]
  rw [e] at h
  exact h

theorem row_succ (j p : PTm k) :
    Γ ⊢[PRAAx] I.row (succ j) p ≐
      code I.tb (I.bd (monus (I.h p) (succ j)) p) two (pairT j (pairT (I.row j p) p)) := by
  have h := rec2_succ (Γ := Γ) I.base I.step j p
  have e : Syn.subst ![j, ap2 (rec2 I.base I.step) j p, p] I.step =
      code I.tb (I.bd (monus (I.h p) (succ j)) p) two (pairT j (pairT (I.row j p) p)) := by
    simp [Instance.step, Instance.row]
  rw [e] at h
  exact h

theorem t0_at (a p : PTm k) : inst2 I.t0 a p = sg (I.g (I.h p) a p) := by
  show Syn.subst ![a, p] I.t0 = _
  simp [Instance.t0]

theorem f_at (b a j R p : PTm k) :
    Γ ⊢[PRAAx] inst2 I.f b (pairT a (pairT j (pairT R p))) ≐
      I.t (monus (I.h p) (succ j)) a b p * dg two b R := by
  have e₁ : inst2 I.f b (pairT a (pairT j (pairT R p))) =
      Syn.subst ![b, fstT (pairT a (pairT j (pairT R p))),
          fstT (sndT (pairT a (pairT j (pairT R p)))),
          fstT (sndT (sndT (pairT a (pairT j (pairT R p))))),
          sndT (sndT (sndT (pairT a (pairT j (pairT R p)))))]
        (I.t (monus (I.h (var 4 : PTm 5)) (succ (var 2))) (var 1) (var 0) (var 4) *
          dg two (var 0) (var 3)) := by
    show Syn.subst ![b, pairT a (pairT j (pairT R p))] I.f = _
    simp [Instance.f]
  have e₂ : I.t (monus (I.h p) (succ j)) a b p * dg two b R =
      Syn.subst ![b, a, j, R, p]
        (I.t (monus (I.h (var 4 : PTm 5)) (succ (var 2))) (var 1) (var 0) (var 4) *
          dg two (var 0) (var 3)) := by simp
  rw [e₁, e₂]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT a (pairT j (pairT R p))) ≐ pairT j (pairT R p) :=
    snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT (pairT a (pairT j (pairT R p)))) ≐ pairT R p :=
    (congrSnd s₁).eqTrans (snd_pair _ _)
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrFst s₂).eqTrans (fst_pair _ _)
    · exact (congrSnd s₂).eqTrans (snd_pair _ _)

theorem tb_at (a j R p : PTm k) :
    Γ ⊢[PRAAx] inst2 I.tb a (pairT j (pairT R p)) ≐
      sg (I.g (monus (I.h p) (succ j)) a p) *
        exB I.f (I.bd (monus (I.h p) j) p) (pairT a (pairT j (pairT R p))) := by
  have e₁ : inst2 I.tb a (pairT j (pairT R p)) =
      Syn.subst ![a, fstT (pairT j (pairT R p)), sndT (sndT (pairT j (pairT R p))),
          pairT j (pairT R p)]
        (sg (I.g (monus (I.h (var 2 : PTm 4)) (succ (var 1))) (var 0) (var 2)) *
          exB I.f (I.bd (monus (I.h (var 2)) (var 1)) (var 2)) (pairT (var 0) (var 3))) := by
    show Syn.subst ![a, pairT j (pairT R p)] I.tb = _
    simp [Instance.tb]
  have e₂ : sg (I.g (monus (I.h p) (succ j)) a p) *
        exB I.f (I.bd (monus (I.h p) j) p) (pairT a (pairT j (pairT R p))) =
      Syn.subst ![a, j, p, pairT j (pairT R p)]
        (sg (I.g (monus (I.h (var 2 : PTm 4)) (succ (var 1))) (var 0) (var 2)) *
          exB I.f (I.bd (monus (I.h (var 2)) (var 1)) (var 2)) (pairT (var 0) (var 3))) := by simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _)
    · exact .eqRefl _

/-- `V(0, a) = sg G(h, a)` for `a < B(h)`. -/
theorem V_zero {a p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd (I.h p) p)) :
    Γ ⊢[PRAAx] I.V zero a p ≐ sg (I.g (I.h p) a p) := by
  have c : Γ ⊢[PRAAx] I.V zero a p ≐ dg two a (code I.t0 (I.bd (I.h p) p) two p) :=
    congrAp2 remF (congrAp2 quoF (row_zero I p) (.eqRefl _)) (.eqRefl _)
  have e := ev_curry I.t0 two_pos ha p
  rw [t0_at] at e
  exact c.eqTrans (e.eqTrans (rem_of_lt two_pos (lt_two_of_bit (sg_cases _))))

/-- The recursion (1): `V(j + 1, a) = sg G(i, a) · [∃ b < B(i'). T(i, a, b) · V(j, b) ≠ 0]`
for `a < B(i)`, with `i = h ∸ (j + 1)` and `i' = h ∸ j`. -/
theorem V_succ {j a p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd (monus (I.h p) (succ j)) p)) :
    Γ ⊢[PRAAx] I.V (succ j) a p ≐
      sg (I.g (monus (I.h p) (succ j)) a p) *
        exB I.f (I.bd (monus (I.h p) j) p) (pairT a (pairT j (pairT (I.row j p) p))) := by
  have c : Γ ⊢[PRAAx] I.V (succ j) a p ≐
      dg two a (code I.tb (I.bd (monus (I.h p) (succ j)) p) two
        (pairT j (pairT (I.row j p) p))) :=
    congrAp2 remF (congrAp2 quoF (row_succ I j p) (.eqRefl _)) (.eqRefl _)
  have e := ev_curry I.tb two_pos ha (pairT j (pairT (I.row j p) p))
  have r : Γ ⊢[PRAAx] rem (inst2 I.tb a (pairT j (pairT (I.row j p) p))) two ≐
      rem (sg (I.g (monus (I.h p) (succ j)) a p) *
        exB I.f (I.bd (monus (I.h p) j) p) (pairT a (pairT j (pairT (I.row j p) p)))) two :=
    congrAp2 remF (tb_at I a j (I.row j p) p) (.eqRefl two)
  exact c.eqTrans (e.eqTrans (r.eqTrans
    (rem_of_lt two_pos (lt_two_of_bit (mul_bit (sg_cases _) (ex_cases _ _ _))))))

/-- Viability unfolds one level: the selected successor is a compatible viable candidate. -/
theorem V_unfold {j a p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd (monus (I.h p) (succ j)) p))
    (hv : Γ ⊢[PRAAx] I.V (succ j) a p ≐ one) :
    Γ ⊢[PRAAx] neg (I.g (monus (I.h p) (succ j)) a p ≐ zero) ⋏
      (lt (I.nxt j a p) (I.bd (monus (I.h p) j) p) ⋏
        (neg (I.t (monus (I.h p) (succ j)) a (I.nxt j a p) p ≐ zero) ⋏
          (I.V j (I.nxt j a p) p ≐ one))) := by
  have m := (V_succ I ha).eqSymm.eqTrans hv
  have hs := left_of_mul_one (sg_cases _) m
  have he := right_of_mul_one (ex_cases _ _ _) m
  have w := ex_elim I.f he
  -- the test at the witness, unfolded
  have hne : Γ ⊢[PRAAx]
      neg (I.t (monus (I.h p) (succ j)) a (I.nxt j a p) p * I.V j (I.nxt j a p) p ≐ zero) :=
    .impI (.impE (Prf.andE₂ w).wk ((f_at I _ a j (I.row j p) p).eqTrans Prf.hyp0))
  refine .andI ?_ (.andI (.andE₁ w) (.andI ?_ ?_))
  · exact .impI (one_ne_zero _ (hs.wk.eqSymm.eqTrans (sg_of_zero Prf.hyp0)))
  · exact .impI (.impE hne.wk ((congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)))
  · refine one_of_ne (bit_of_lt_two (dg_lt two_pos _ _)) (.impI (.impE hne.wk ?_))
    exact (congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)

/-- Viability folds one level: a compatible viable candidate of the next level makes a
locally valid candidate viable. -/
theorem V_fold {j a b p : PTm k} (ha : Γ ⊢[PRAAx] lt a (I.bd (monus (I.h p) (succ j)) p))
    (hg : Γ ⊢[PRAAx] neg (I.g (monus (I.h p) (succ j)) a p ≐ zero))
    (hb : Γ ⊢[PRAAx] lt b (I.bd (monus (I.h p) j) p))
    (ht : Γ ⊢[PRAAx] neg (I.t (monus (I.h p) (succ j)) a b p ≐ zero))
    (hv : Γ ⊢[PRAAx] I.V j b p ≐ one) : Γ ⊢[PRAAx] I.V (succ j) a p ≐ one := by
  have hf : Γ ⊢[PRAAx]
      neg (inst2 I.f b (pairT a (pairT j (pairT (I.row j p) p))) ≐ zero) := by
    refine .impI (.impE ht.wk ?_)
    have e := (f_at (Γ := (inst2 I.f b (pairT a (pairT j (pairT (I.row j p) p))) ≐ zero) :: Γ)
      I b a j (I.row j p) p).eqSymm.eqTrans Prf.hyp0
    exact ((one_mul _).eqSymm.eqTrans ((mul_comm _ _).eqTrans
      (congrMul (.eqRefl _) hv.wk.eqSymm))).eqTrans e
  have he := ex_intro I.f hf hb
  exact (V_succ I ha).eqTrans ((congrMul (sg_of_ne hg) he).eqTrans (one_mul _))

end Rows

end LeanProofs.IPRA.Foundations.BackwardViability
