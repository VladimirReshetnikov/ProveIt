import IPRADerivations.Foundations.FiniteCoverSkeleton

/-!
# Quotients of finite sets by least representatives (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "Finite colimits by bounded
equivalence closure", the quotient step: "For each `u < N` choose the least `v < N` with
`R_N(u, v)`. This bounded minimum exists because `R_N(u, u)` holds. ... The map taking `u` to
... its minimum is our quotient map. In particular no abstract quotient type or choice axiom is
needed in the object theory. ... Define `v : [q] → [z]` by evaluating the cocone at the chosen
least representative. Then `v ∘ ι = t`. Any other such map agrees on every class because every
class has its displayed representative."

For a decidable equivalence `E(a, b) ⟺ e(a, b) = 0` with its laws (`Laws` of
`Foundations/FiniteCoverSkeleton`) and a size `N`, the quotient map is the first-match scan of
the list `L_i = i`: `quot N u = μ v < N. E(v, u)`.

* `quot_spec`: for `u < N`: `quot N u < N`, `E(quot N u, u)` and `quot N u ≤ u`;
* `quot_idem`: `quot N (quot N u) = quot N u`: representatives are fixed;
* `quot_sound`, `quot_exact`: for `u, v < N`, `quot N u = quot N v` exactly when `E(u, v)`: the
  kernel of the quotient map is `E`;
* `med_comm`: a term `t` that respects `E` (`Respects`) satisfies `t(quot N u) = t(u)`: the
  mediator is `t` evaluated at the representative;
* `med_unique`: a table `v` with `v(quot N u) = t(u)` for all `u < N` agrees with `t` at every
  representative `c = quot N c < N`;
* `quot_kernel_closed`: the kernel statement as a closed sentence.

Instance with every hypothesis discharged: the kernel of an arbitrary term `f`,
`E(a, b) ⟺ f(a) = f(b)` (`kerE`, `ker_laws`, `ker_resp`). Then `image_factor`: `f(quot N u) =
f(u)`, and `image_mono`: `f` is injective on representatives, so `f` restricted to `[N]` factors
as the quotient map followed by an injection.

Not derived here: the equivalence closure of a generating relation (the packet's Warshall
recurrence and its path invariant), so this is the quotient by a supplied equivalence, not yet
the colimit of an arbitrary finite diagram; and the compaction of the representatives to `[q]`.
-/

namespace LeanProofs.IPRA.Foundations.FiniteQuotient

open_ipra exports
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)
open LeanProofs.IPRA.Foundations.FiniteCoverSkeleton

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- Congruence of a unary term. -/
theorem congrInst1 (t : PTm 1) {a b : PTm k} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] inst1 t a ≐ inst1 t b :=
  Prf.eqCongr t fun j => by fin_cases j; exact h

/-! ## The quotient map -/

/-- The quotient map: the least `v < N` with `E(v, u)`. -/
abbrev quot (e : PTm 2) (N u : PTm k) : PTm k := rep e (var 0) N u

variable {e : PTm 2}

/-- The representative of `u < N` is below `N`, equivalent to `u`, and at most `u`. -/
theorem quot_spec (H : Laws e) {N u : PTm k} (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] lt (quot e N u) N ⋏ (E e (quot e N u) u ⋏ le (quot e N u) u) := by
  have g := rep_found (e := e) (l := var 0) (x := u) (j := u) hu
    (by rw [inst1_id]; exact H.refl u)
  simp only [inst1_id] at g
  exact g

/-- Representatives are fixed by the quotient map. -/
theorem quot_idem (H : Laws e) {N u : PTm k} (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] quot e N (quot e N u) ≐ quot e N u := by
  have i : Γ ⊢[PRAAx] rep e (var 0) N (inst1 (var 0) (rep e (var 0) N u)) ≐ rep e (var 0) N u :=
    rep_idem (l := var 0) H (Prf.andE₁ (quot_spec H hu))
  simp only [inst1_id] at i
  exact i

/-- Equivalent elements have the same representative. -/
theorem quot_sound (H : Laws e) {N u v : PTm k} (h : Γ ⊢[PRAAx] E e u v) :
    Γ ⊢[PRAAx] quot e N u ≐ quot e N v :=
  rep_congr H h

/-- Elements below `N` with the same representative are equivalent. -/
theorem quot_exact (H : Laws e) {N u v : PTm k} (hu : Γ ⊢[PRAAx] lt u N)
    (hv : Γ ⊢[PRAAx] lt v N) (h : Γ ⊢[PRAAx] quot e N u ≐ quot e N v) :
    Γ ⊢[PRAAx] E e u v := by
  have a := Prf.andE₁ (Prf.andE₂ (quot_spec H hu))
  have b := Prf.andE₁ (Prf.andE₂ (quot_spec H hv))
  exact H.trans (H.symm a) ((congrInst2 e h (.eqRefl _)).eqTrans b)

/-- The kernel of the quotient map is `E`, as a closed sentence. Variables: `0 = N`, `1 = u`,
`2 = v`. -/
theorem quot_kernel_closed (H : Laws e) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (lt (var 1) (var 0) ⟶ lt (var 2) (var 0) ⟶
      (((quot e (var 0) (var 1) ≐ quot e (var 0) (var 2)) ⟶ E e (var 1) (var 2)) ⋏
        (E e (var 1) (var 2) ⟶ (quot e (var 0) (var 1) ≐ quot e (var 0) (var 2))))) :=
  closeUniv 3 (.impI (.impI (.andI (.impI (quot_exact H hyp2 Prf.hyp1 Prf.hyp0))
    (.impI (quot_sound H Prf.hyp0)))))

/-! ## The mediator -/

/-- The term `t` is constant on the classes of `E`. -/
structure Respects (e : PTm 2) (t : PTm 1) : Prop where
  resp : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {a b : PTm k},
    (Γ ⊢[PRAAx] E e a b) → (Γ ⊢[PRAAx] inst1 t a ≐ inst1 t b)

/-- A map constant on classes factors through the quotient map: its value at the
representative is its value. -/
theorem med_comm (H : Laws e) {t : PTm 1} (R : Respects e t) {N u : PTm k}
    (hu : Γ ⊢[PRAAx] lt u N) : Γ ⊢[PRAAx] inst1 t (quot e N u) ≐ inst1 t u :=
  R.resp (Prf.andE₁ (Prf.andE₂ (quot_spec H hu)))

/-- Uniqueness of the mediator: a table `v` with `v ∘ quot = t` on `[N]` agrees with `t` at
every representative. -/
theorem med_unique {t v : PTm 1} {N c : PTm k} (hc : Γ ⊢[PRAAx] lt c N)
    (hk : Γ ⊢[PRAAx] quot e N c ≐ c)
    (hv : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst1 v (quot e (Syn.shift N) (var 0)) ≐ inst1 t (var 0)))) :
    Γ ⊢[PRAAx] inst1 v c ≐ inst1 t c := by
  have a := Prf.allE c hv
  simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_inst1, subst_ap2, Syn.subst_var,
    Syn.inst_zero, Syn.subst_inst_shift] at a
  exact (congrInst1 v hk).eqSymm.eqTrans (.impE a hc)

/-! ## An instance: the kernel of a map, and image factorization -/

/-- `x = y` from `1 ∸ [x = y] = 0`. -/
theorem eq_of_compl {x y : PTm k} (h : Γ ⊢[PRAAx] monus one (eqb x y) ≐ zero) :
    Γ ⊢[PRAAx] x ≐ y :=
  Common.eq_of_eqb_compl_zero h

/-- `1 ∸ [x = y] = 0` from `x = y`. -/
theorem compl_of_eq {x y : PTm k} (h : Γ ⊢[PRAAx] x ≐ y) :
    Γ ⊢[PRAAx] monus one (eqb x y) ≐ zero :=
  Common.eqb_compl_zero_of_eq h

variable (f : PTm 1)

/-- The kernel relation of `f`: `1 ∸ [f(a) = f(b)]`. -/
def kerE : PTm 2 :=
  monus one (eqb (Syn.subst ![(var 0 : PTm 2)] f) (Syn.subst ![(var 1 : PTm 2)] f))

theorem inst2_kerE (a b : PTm k) :
    inst2 (kerE f) a b = monus one (eqb (inst1 f a) (inst1 f b)) := by
  have e₁ : Syn.subst ![a, b] (Syn.subst ![(var 0 : PTm 2)] f) = Syn.subst ![a] f := by
    rw [Syn.subst_subst]
    congr 1; funext j; fin_cases j; rfl
  have e₂ : Syn.subst ![a, b] (Syn.subst ![(var 1 : PTm 2)] f) = Syn.subst ![b] f := by
    rw [Syn.subst_subst]
    congr 1; funext j; fin_cases j; rfl
  simp [inst2, inst1, kerE, e₁, e₂]

theorem ker_of_eq {a b : PTm k} (h : Γ ⊢[PRAAx] inst1 f a ≐ inst1 f b) :
    Γ ⊢[PRAAx] E (kerE f) a b := by
  show Γ ⊢[PRAAx] inst2 (kerE f) a b ≐ zero
  rw [inst2_kerE]
  exact compl_of_eq h

theorem eq_of_ker {a b : PTm k} (h : Γ ⊢[PRAAx] E (kerE f) a b) :
    Γ ⊢[PRAAx] inst1 f a ≐ inst1 f b := by
  have h' : Γ ⊢[PRAAx] inst2 (kerE f) a b ≐ zero := h
  rw [inst2_kerE] at h'
  exact eq_of_compl h'

/-- The kernel of any term is an equivalence relation. -/
theorem ker_laws : Laws (kerE f) where
  refl _ := ker_of_eq f (.eqRefl _)
  symm h := ker_of_eq f (eq_of_ker f h).eqSymm
  trans h₁ h₂ := ker_of_eq f ((eq_of_ker f h₁).eqTrans (eq_of_ker f h₂))

/-- A term is constant on the classes of its kernel. -/
theorem ker_resp : Respects (kerE f) f where
  resp h := eq_of_ker f h

/-- Image factorization, first half: `f(quot N u) = f(u)` for `u < N`. -/
theorem image_factor {N u : PTm k} (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] inst1 f (quot (kerE f) N u) ≐ inst1 f u :=
  med_comm (ker_laws f) (ker_resp f) hu

/-- Image factorization, second half: `f` is injective on representatives. -/
theorem image_mono {N u v : PTm k} (hu : Γ ⊢[PRAAx] lt u N) (hv : Γ ⊢[PRAAx] lt v N)
    (h : Γ ⊢[PRAAx] inst1 f (quot (kerE f) N u) ≐ inst1 f (quot (kerE f) N v)) :
    Γ ⊢[PRAAx] quot (kerE f) N u ≐ quot (kerE f) N v :=
  quot_sound (ker_laws f) (ker_of_eq f
    ((image_factor f hu).eqSymm.eqTrans (h.eqTrans (image_factor f hv))))

/-- Image factorization as a closed sentence. Variables: `0 = N`, `1 = u`. -/
theorem image_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (lt (var 1) (var 0) ⟶
      (lt (quot (kerE f) (var 0) (var 1)) (var 0) ⋏
        ((quot (kerE f) (var 0) (quot (kerE f) (var 0) (var 1)) ≐ quot (kerE f) (var 0) (var 1)) ⋏
          (inst1 f (quot (kerE f) (var 0) (var 1)) ≐ inst1 f (var 1))))) :=
  closeUniv 2 (.impI (.andI (Prf.andE₁ (quot_spec (ker_laws f) Prf.hyp0))
    (.andI (quot_idem (ker_laws f) Prf.hyp0) (image_factor f Prf.hyp0))))

end LeanProofs.IPRA.Foundations.FiniteQuotient
