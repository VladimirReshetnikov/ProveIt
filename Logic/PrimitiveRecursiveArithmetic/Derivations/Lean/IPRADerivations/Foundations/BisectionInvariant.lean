import IPRADerivations.Foundations.TraceReflection
import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Core.Pairing
import IPRADerivations.Core.OrderCertificates

/-!
# The bisection invariant

Packets (`docs/proofs/foundations`):

* `FINER-iPRA-framework-2026-11-16`, `paper/sections/14_applications.tex`, Theorem "Bisection invariant":
  for every `t`, `L_t ≤ U_t`, `f_x(L_t) ≤ 0 ≤ f_x(U_t)` and `U_t − L_t = 2^{-t}(U_0 − L_0)`;
* `ipra_uniform_certificates`, Lemma `lem:bisect` ("Bisection with non-strict signs");
* `cifer_ipra_framework_2026-11-15`, Lemma `lem:cubic-bisect`, and
  `ipra_cfp_contract_compiler_2026-11-15`, "Bisection invariant" (the same invariant for the cubic chart).

No division is needed when the stage is part of the scale: at stage `t` the endpoints are numerators
`ℓ_t`, `u_t` over a denominator `D · 2^t`. The midpoint at stage `t + 1` has numerator `ℓ_t + u_t`, and the
next interval is `[ℓ_t + u_t, 2u_t]` or `[2ℓ_t, ℓ_t + u_t]`. The state is the pair `⟨ℓ, u⟩`.

The data are a test term `c(m, t, x)` (zero when the function is `≤ 0` at the point of numerator `m` at
stage `t + 1`) and two quantifier-free formulas `Lo(a, t, x)`, `Hi(a, t, x)` ("the function is `≤ 0`",
"`≥ 0`", at the point of numerator `a` at stage `t`), with the rules

* rescaling: `Lo(a, t) ⊢ Lo(2a, t + 1)` and `Hi(a, t) ⊢ Hi(2a, t + 1)`;
* the test: `c(m, t) = 0 ⊢ Lo(m, t + 1)` and `c(m, t) = d + 1 ⊢ Hi(m, t + 1)`.

Then, from `Lo(L_0, 0)`, `Hi(U_0, 0)` and `U_0 = L_0 + W`:

* `bisection_invariant`: for every `t`, `Lo(ℓ_t, t)`, `Hi(u_t, t)` and `u_t = ℓ_t + W`. The last equation
  gives `ℓ_t ≤ u_t` and, on the scale `D · 2^t`, the width `2^{-t}(U_0 − L_0)`;
* `bisection_at`: the instance at a stage `t`.

`bStep`, `step_lo`, `step_hi` describe one step; the case distinction is on the value of the test term,
which is decidable. `bis_nested`: for `ℓ ≤ u` the next interval lies inside the current one (`2ℓ ≤ ℓ′`,
`u′ ≤ 2u` on the next scale). The regular name of the root is not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.BisectionInvariant

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.ClockedDescent (subst_QF')
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos sg_of_zero)
open LeanProofs.IPRA.Foundations.TraceReflection (Run I3 subst_I3 run_zero run_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)} {c : PTm 3}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `c(m, t, x)`. -/
def cAt (c : PTm 3) (m t x : PTm k) : PTm k := Syn.subst ![m, t, x] c

/-- The test at the midpoint of the state; variables `0 = t`, `1 = s = ⟨ℓ, u⟩`, `2 = x`. -/
def tst (c : PTm 3) : PTm 3 := Syn.subst ![fstT (var 1) + sndT (var 1), var 0, var 2] c

theorem subst_tst (t s x : PTm k) :
    Syn.subst ![t, s, x] (tst c) = cAt c (fstT s + sndT s) t x := by
  simp only [tst, cAt, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- The bisection step; variables `0 = t`, `1 = s = ⟨ℓ, u⟩`, `2 = x`. -/
def bStep (c : PTm 3) : PTm 3 :=
  pairT
    (sg (tst c) * (fstT (var 1) + fstT (var 1)) + monus one (sg (tst c)) * (fstT (var 1) + sndT (var 1)))
    (sg (tst c) * (fstT (var 1) + sndT (var 1)) + monus one (sg (tst c)) * (sndT (var 1) + sndT (var 1)))

theorem step_at (t s x : PTm k) :
    Syn.subst ![t, s, x] (bStep c) =
      pairT
        (sg (cAt c (fstT s + sndT s) t x) * (fstT s + fstT s) +
          monus one (sg (cAt c (fstT s + sndT s) t x)) * (fstT s + sndT s))
        (sg (cAt c (fstT s + sndT s) t x) * (fstT s + sndT s) +
          monus one (sg (cAt c (fstT s + sndT s) t x)) * (sndT s + sndT s)) := by
  simp [bStep, subst_tst]

/-- The test value zero keeps the upper half `[ℓ + u, 2u]`. -/
theorem step_lo {t s x : PTm k} (h : Γ ⊢[PRAAx] cAt c (fstT s + sndT s) t x ≐ zero) :
    Γ ⊢[PRAAx] (fstT (Syn.subst ![t, s, x] (bStep c)) ≐ fstT s + sndT s) ⋏
      (sndT (Syn.subst ![t, s, x] (bStep c)) ≐ sndT s + sndT s) := by
  rw [step_at]
  have sb := sg_of_zero h
  have e₁ := natEq sb
  have e₂ := natEq ((congrMonus (.eqRefl one) sb).eqTrans (monus_zero one))
  refine .andI ((fst_pair _ _).eqTrans ?_) ((snd_pair _ _).eqTrans ?_)
  · apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

/-- A positive test value keeps the lower half `[2ℓ, ℓ + u]`. -/
theorem step_hi {t s x d : PTm k} (h : Γ ⊢[PRAAx] cAt c (fstT s + sndT s) t x ≐ succ d) :
    Γ ⊢[PRAAx] (fstT (Syn.subst ![t, s, x] (bStep c)) ≐ fstT s + fstT s) ⋏
      (sndT (Syn.subst ![t, s, x] (bStep c)) ≐ fstT s + sndT s) := by
  rw [step_at]
  have sb := sg_of_pos h
  have e₁ := natEq sb
  have e₂ := natEq ((congrMonus (.eqRefl one) sb).eqTrans (monus_self one))
  refine .andI ((fst_pair _ _).eqTrans ?_) ((snd_pair _ _).eqTrans ?_)
  · apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

/-- For `ℓ ≤ u` the next interval lies inside the current one, on the next scale: `2ℓ ≤ ℓ′` and
`u′ ≤ 2u`. -/
theorem bis_nested {t s s' x : PTm k} (hs' : Γ ⊢[PRAAx] s' ≐ Syn.subst ![t, s, x] (bStep c))
    (hle : Γ ⊢[PRAAx] le (fstT s) (sndT s)) :
    Γ ⊢[PRAAx] le (fstT s + fstT s) (fstT s') ⋏ le (sndT s') (sndT s + sndT s) := by
  refine .orE (zero_or_succ (cAt c (fstT s + sndT s) t x)) ?_ ?_
  · have h0 : ((cAt c (fstT s + sndT s) t x ≐ zero) :: Γ) ⊢[PRAAx]
        cAt c (fstT s + sndT s) t x ≐ zero := Prf.hyp0
    have st := step_lo h0
    have eL := natEq ((congrFst hs'.wk).eqTrans (Prf.andE₁ st))
    have eU := natEq ((congrSnd hs'.wk).eqTrans (Prf.andE₂ st))
    have hle' := hle.wk (ψ := cAt c (fstT s + sndT s) t x ≐ zero)
    refine .andI ?_ ?_
    · ipra_le sl hle' using linear_combination eL
    · ipra_le 0 using linear_combination -eU
  · have h1 : ((cAt c (fstT s + sndT s) t x ≐ succ (pred (cAt c (fstT s + sndT s) t x))) :: Γ) ⊢[PRAAx]
        cAt c (fstT s + sndT s) t x ≐ succ (pred (cAt c (fstT s + sndT s) t x)) := Prf.hyp0
    have st := step_hi h1
    have eL := natEq ((congrFst hs'.wk).eqTrans (Prf.andE₁ st))
    have eU := natEq ((congrSnd hs'.wk).eqTrans (Prf.andE₂ st))
    have hle' := hle.wk
      (ψ := cAt c (fstT s + sndT s) t x ≐ succ (pred (cAt c (fstT s + sndT s) t x)))
    refine .andI ?_ ?_
    · ipra_le 0 using linear_combination eL
    · ipra_le sl hle' using linear_combination -eU

/-- Congruence of `I3` in its first argument. -/
theorem I3_congr₁ (F : Fm PTm 3) {a a' b d : PTm k} (h : Γ ⊢[PRAAx] a ≐ a')
    (hi : Γ ⊢[PRAAx] I3 F a b d) : Γ ⊢[PRAAx] I3 F a' b d :=
  Prf.eqSubst F ![a, b, d] ![a', b, d] (fun j => by
    fin_cases j
    · exact h
    · exact .eqRefl b
    · exact .eqRefl d) hi

section Invariant

variable {Lo Hi : Fm PTm 3}

/-- The invariant at a state `s` and stage `t`. -/
abbrev BInv (Lo Hi : Fm PTm 3) (s t x W : PTm k) : Fm PTm k :=
  I3 Lo (fstT s) t x ⋏ (I3 Hi (sndT s) t x ⋏ (sndT s ≐ fstT s + W))

/-- One bisection step preserves the invariant. -/
theorem bis_step
    (hLo2 : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] I3 Lo a t x) → (Θ ⊢[PRAAx] I3 Lo (a + a) (succ t) x))
    (hHi2 : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] I3 Hi a t x) → (Θ ⊢[PRAAx] I3 Hi (a + a) (succ t) x))
    (hmidLo : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] cAt c a t x ≐ zero) → (Θ ⊢[PRAAx] I3 Lo a (succ t) x))
    (hmidHi : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x d : PTm m),
      (Θ ⊢[PRAAx] cAt c a t x ≐ succ d) → (Θ ⊢[PRAAx] I3 Hi a (succ t) x))
    {t s s' x W : PTm k} (hs' : Γ ⊢[PRAAx] s' ≐ Syn.subst ![t, s, x] (bStep c))
    (h : Γ ⊢[PRAAx] BInv Lo Hi s t x W) : Γ ⊢[PRAAx] BInv Lo Hi s' (succ t) x W := by
  have hl := Prf.andE₁ h
  have hh := Prf.andE₁ (Prf.andE₂ h)
  have hw := Prf.andE₂ (Prf.andE₂ h)
  refine .orE (zero_or_succ (cAt c (fstT s + sndT s) t x)) ?_ ?_
  · have h0 : ((cAt c (fstT s + sndT s) t x ≐ zero) :: Γ) ⊢[PRAAx]
        cAt c (fstT s + sndT s) t x ≐ zero := Prf.hyp0
    have st := step_lo h0
    have eL := (congrFst hs'.wk).eqTrans (Prf.andE₁ st)
    have eU := (congrSnd hs'.wk).eqTrans (Prf.andE₂ st)
    refine .andI (I3_congr₁ Lo eL.eqSymm (hmidLo _ t x h0))
      (.andI (I3_congr₁ Hi eU.eqSymm (hHi2 _ t x hh.wk)) ?_)
    have k₁ := natEq eL
    have k₂ := natEq eU
    have k₃ := natEq (hw.wk (ψ := cAt c (fstT s + sndT s) t x ≐ zero))
    apply deriveNat; ipra_simps
    linear_combination k₂ - k₁ + k₃
  · have h1 : ((cAt c (fstT s + sndT s) t x ≐ succ (pred (cAt c (fstT s + sndT s) t x))) :: Γ) ⊢[PRAAx]
        cAt c (fstT s + sndT s) t x ≐ succ (pred (cAt c (fstT s + sndT s) t x)) := Prf.hyp0
    have st := step_hi h1
    have eL := (congrFst hs'.wk).eqTrans (Prf.andE₁ st)
    have eU := (congrSnd hs'.wk).eqTrans (Prf.andE₂ st)
    refine .andI (I3_congr₁ Lo eL.eqSymm (hLo2 _ t x hl.wk))
      (.andI (I3_congr₁ Hi eU.eqSymm (hmidHi _ t x _ h1)) ?_)
    have k₁ := natEq eL
    have k₂ := natEq eU
    have k₃ := natEq (hw.wk
      (ψ := cAt c (fstT s + sndT s) t x ≐ succ (pred (cAt c (fstT s + sndT s) t x))))
    apply deriveNat; ipra_simps
    linear_combination k₂ - k₁ + k₃

/-- The bisection invariant at every stage. -/
theorem bisection_invariant (hLoQF : Lo.QF) (hHiQF : Hi.QF)
    (hLo2 : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] I3 Lo a t x) → (Θ ⊢[PRAAx] I3 Lo (a + a) (succ t) x))
    (hHi2 : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] I3 Hi a t x) → (Θ ⊢[PRAAx] I3 Hi (a + a) (succ t) x))
    (hmidLo : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] cAt c a t x ≐ zero) → (Θ ⊢[PRAAx] I3 Lo a (succ t) x))
    (hmidHi : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x d : PTm m),
      (Θ ⊢[PRAAx] cAt c a t x ≐ succ d) → (Θ ⊢[PRAAx] I3 Hi a (succ t) x))
    (init : PTm 1) {x W : PTm k}
    (hbase : Γ ⊢[PRAAx] BInv Lo Hi (Syn.subst ![x] init) zero x W) :
    Γ ⊢[PRAAx] Fm.all (BInv Lo Hi (Run init (bStep c) (var 0) (Syn.shift x)) (var 0) (Syn.shift x)
      (Syn.shift W)) := by
  refine PRA.qfInd _ ⟨subst_QF' hLoQF _, subst_QF' hHiQF _, trivial⟩ ?_ ?_
  · have e : (BInv Lo Hi (Run init (bStep c) (var 0) (Syn.shift x)) (var 0) (Syn.shift x)
        (Syn.shift W)).subst (Syn.inst zero) = BInv Lo Hi (Run init (bStep c) zero x) zero x W := by
      simp [subst_I3]
    rw [e]
    have r := (run_zero (init := init) (step := bStep c) (Δ := Γ) x).eqSymm
    have hl := Prf.andE₁ hbase
    have hh := Prf.andE₁ (Prf.andE₂ hbase)
    have hw := Prf.andE₂ (Prf.andE₂ hbase)
    refine .andI (I3_congr₁ Lo (congrFst r) hl) (.andI (I3_congr₁ Hi (congrSnd r) hh) ?_)
    exact (congrSnd r).eqSymm.eqTrans (hw.eqTrans (congrAdd (congrFst r) (.eqRefl W)))
  · have e : (BInv Lo Hi (Run init (bStep c) (var 0) (Syn.shift x)) (var 0) (Syn.shift x)
        (Syn.shift W)).subst (Syn.repl (succ (var 0))) =
        BInv Lo Hi (Run init (bStep c) (succ (var 0)) (Syn.shift x)) (succ (var 0)) (Syn.shift x)
          (Syn.shift W) := by
      simp [subst_I3]
    rw [e]
    exact bis_step hLo2 hHi2 hmidLo hmidHi (run_succ (var 0) (Syn.shift x)) Prf.hyp0

/-- The bisection invariant at a stage `t`. -/
theorem bisection_at (hLoQF : Lo.QF) (hHiQF : Hi.QF)
    (hLo2 : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] I3 Lo a t x) → (Θ ⊢[PRAAx] I3 Lo (a + a) (succ t) x))
    (hHi2 : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] I3 Hi a t x) → (Θ ⊢[PRAAx] I3 Hi (a + a) (succ t) x))
    (hmidLo : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x : PTm m),
      (Θ ⊢[PRAAx] cAt c a t x ≐ zero) → (Θ ⊢[PRAAx] I3 Lo a (succ t) x))
    (hmidHi : ∀ {m : ℕ} {Θ : List (Fm PTm m)} (a t x d : PTm m),
      (Θ ⊢[PRAAx] cAt c a t x ≐ succ d) → (Θ ⊢[PRAAx] I3 Hi a (succ t) x))
    (init : PTm 1) {x W : PTm k}
    (hbase : Γ ⊢[PRAAx] BInv Lo Hi (Syn.subst ![x] init) zero x W) (t : PTm k) :
    Γ ⊢[PRAAx] BInv Lo Hi (Run init (bStep c) t x) t x W := by
  have a := Prf.allE t (bisection_invariant hLoQF hHiQF hLo2 hHi2 hmidLo hmidHi init hbase)
  have e : (BInv Lo Hi (Run init (bStep c) (var 0) (Syn.shift x)) (var 0) (Syn.shift x)
      (Syn.shift W)).subst (Syn.inst t) = BInv Lo Hi (Run init (bStep c) t x) t x W := by
    simp [subst_I3]
  rw [e] at a
  exact a

end Invariant

end LeanProofs.IPRA.Foundations.BisectionInvariant
