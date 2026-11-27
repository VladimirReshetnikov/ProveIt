import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.Descent

/-!
# A supplied finite cover gives an explicit skeleton (`ipra_categorical_methods`, Section 7)

Packet: `foundations/ipra_categorical_methods`, theorem "Finite-cover skeleton construction"
(`thm:finite-cover-skeleton`): for a decidable equivalence relation `E` with its laws proved, and
a supplied finite list `L` with the covering assertion `∀ x ∃ j < |L|, E(x, L_j)`, "there is a PR
algorithm producing a sublist `R` of `L` whose elements are pairwise inequivalent and still
satisfy" the covering assertion, and "the corresponding thin groupoid is explicitly equivalent to
the discrete finite category on the indices of `R`".

Data: a term `e(a, b)` with `E(a, b)` the equation `e(a, b) = 0`, its three laws supplied as
rules (`Laws`), a list term `l(i)` (`L_i = l(i)`) and a length `N`.

* `rep N x = μ i < N. E(L_i, x)` is the first-match scan (`N` when it fails): the paper's
  `q(x)`; `rep_le`, `rep_hit`, `rep_min`, `rep_found`.
* `kept N r` is the quantifier-free statement `rep N L_r = r`: the entry `r` is its own first
  match. This is the retained sublist `R`. `kept_scan`, `kept_of_scan`: for `r < N` it says
  exactly that `L_r` is inequivalent to every earlier entry, the paper's retention test.
* `kept_inj`: retained entries are pairwise inequivalent.
* `rep_congr`: `E(x, y)` gives `rep N x = rep N y` (the functor `F` to the discrete category
  sends every arrow to an identity).
* `rep_idem`: a successful scan returns a retained index.
* `cover_hit`, `skeleton`: from the covering assertion at `x` (an existential hypothesis, used
  once and outside every induction), `rep N x < N`, the index `rep N x` is retained, and
  `E(L_{rep N x}, x)` (coverage by `R`, and the component `R_{q(x)} → x` of `U F ≅ Id`).
  `F U = Id` is the definition of `kept`.
* `skeleton_closed`, `rep_congr_closed`: closed sentences.
* Instance: equality is such a relation (`eqE`, `eq_laws`), so the laws are satisfiable in the
  stated rule form; for the list `L_i = i` every index below `N` is retained (`id_kept`).

The retained sublist is presented by its decidable membership in `[N]`; its compaction to an
initial segment `[ℓ]` is `rank`/`sel` of `Foundations/FilteredEnumeration` and is not repeated
here.
-/

namespace LeanProofs.IPRA.Foundations.FiniteCoverSkeleton

open_ipra exports
open LeanProofs.IPRA.Search (mu search_spec search_minimal search_found)
open LeanProofs.IPRA.Foundations.BoundedReflection (eqb_cases eq_of_eqb one_ne_zero)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-! ## The data -/

/-- The relation `E(a, b)`: the equation `e(a, b) = 0`. -/
abbrev E (e : PTm 2) (a b : PTm k) : Fm PTm k := inst2 e a b ≐ zero

/-- The laws of an equivalence relation, as rules. -/
structure Laws (e : PTm 2) : Prop where
  refl : ∀ {k : ℕ} {Γ : List (Fm PTm k)} (a : PTm k), Γ ⊢[PRAAx] E e a a
  symm : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {a b : PTm k},
    (Γ ⊢[PRAAx] E e a b) → (Γ ⊢[PRAAx] E e b a)
  trans : ∀ {k : ℕ} {Γ : List (Fm PTm k)} {a b c : PTm k},
    (Γ ⊢[PRAAx] E e a b) → (Γ ⊢[PRAAx] E e b c) → (Γ ⊢[PRAAx] E e a c)

variable (e : PTm 2) (l : PTm 1)

/-- The scan body `e(L_i, x)`; variables `0 = i`, `1 = x`. -/
def fB : PTm 2 := Syn.subst ![Syn.subst ![(var 0 : PTm 2)] l, var 1] e

theorem inst2_fB (i x : PTm k) : inst2 (fB e l) i x = inst2 e (inst1 l i) x := by
  simp only [inst2, inst1, fB, Syn.subst_subst]
  congr 1; funext j; fin_cases j
  · show Syn.subst ![i, x] (Syn.subst ![(var 0 : PTm 2)] l) = Syn.subst ![i] l
    rw [Syn.subst_subst]
    congr 1; funext j; fin_cases j; rfl
  · rfl

/-- The first-match scan `q(x)`: the least `i < N` with `E(L_i, x)`, or `N`. -/
abbrev rep (N x : PTm k) : PTm k := mu (fB e l) N x

/-- The index `r` is retained: `L_r` is its own first match. -/
abbrev kept (N r : PTm k) : Fm PTm k := rep e l N (inst1 l r) ≐ r

/-- The covering assertion at `x`: `∃ j < N, E(L_j, x)`. -/
def Cov (N x : PTm k) : Fm PTm k :=
  Fm.ex (lt (var 0) (Syn.shift N) ⋏ E e (inst1 l (var 0)) (Syn.shift x))

variable {e l}

/-! ## The scan -/

theorem rep_le (N x : PTm k) : Γ ⊢[PRAAx] le (rep e l N x) N :=
  Prf.andE₁ (search_spec (f := fB e l) N zero x)

/-- A successful scan returns an equivalent entry. -/
theorem rep_hit {N x : PTm k} (h : Γ ⊢[PRAAx] lt (rep e l N x) N) :
    Γ ⊢[PRAAx] E e (inst1 l (rep e l N x)) x := by
  have s := Prf.impE (Prf.andE₁ (Prf.andE₂ (search_spec (Γ := Γ) (f := fB e l) N zero x))) h
  rw [inst2_fB] at s
  exact s

/-- Entries before the scan result are inequivalent to `x`. -/
theorem rep_min {N i x : PTm k} (h : Γ ⊢[PRAAx] lt i (rep e l N x)) :
    Γ ⊢[PRAAx] neg (E e (inst1 l i) x) := by
  have m := search_minimal (f := fB e l) h
  rw [inst2_fB] at m
  exact m

/-- An equivalent entry below `N` makes the scan succeed, at or before it. -/
theorem rep_found {N j x : PTm k} (hj : Γ ⊢[PRAAx] lt j N)
    (hE : Γ ⊢[PRAAx] E e (inst1 l j) x) :
    Γ ⊢[PRAAx] lt (rep e l N x) N ⋏ (E e (inst1 l (rep e l N x)) x ⋏ le (rep e l N x) j) := by
  have z : Γ ⊢[PRAAx] inst2 (fB e l) j x ≐ zero := by
    rw [inst2_fB]; exact hE
  have s := search_found z hj
  exact .andI (Prf.andE₁ s) (.andI (rep_hit (Prf.andE₁ s)) (Prf.andE₂ (Prf.andE₂ s)))

theorem rep_le_of (H : Laws e) {N x y : PTm k} (h : Γ ⊢[PRAAx] E e x y) :
    Γ ⊢[PRAAx] le (rep e l N x) (rep e l N y) := by
  refine .orE (lt_or_le (rep e l N y) (rep e l N x)) ?_ Prf.hyp0
  have hlt : (lt (rep e l N y) (rep e l N x) :: Γ) ⊢[PRAAx] lt (rep e l N y) (rep e l N x) :=
    Prf.hyp0
  have hy := rep_hit (lt_of_lt_of_le hlt (rep_le N x))
  exact .botE _ (.impE (rep_min hlt) (H.trans hy (H.symm h.wk)))

/-- The scan is constant on equivalence classes. -/
theorem rep_congr (H : Laws e) {N x y : PTm k} (h : Γ ⊢[PRAAx] E e x y) :
    Γ ⊢[PRAAx] rep e l N x ≐ rep e l N y :=
  le_antisymm (rep_le_of H h) (rep_le_of H (H.symm h))

/-- A successful scan returns a retained index. -/
theorem rep_idem (H : Laws e) {N x : PTm k} (h : Γ ⊢[PRAAx] lt (rep e l N x) N) :
    Γ ⊢[PRAAx] kept e l N (rep e l N x) := by
  have hrx := rep_hit h
  have g := rep_found (x := inst1 l (rep e l N x)) h (H.refl _)
  refine .orE (lt_or_eq_of_le (Prf.andE₂ (Prf.andE₂ g))) ?_ Prf.hyp0
  exact .botE _ (.impE (rep_min Prf.hyp0) (H.trans (Prf.andE₁ (Prf.andE₂ g)).wk hrx.wk))

/-! ## The retained sublist -/

/-- Retained entries are pairwise inequivalent. -/
theorem kept_inj (H : Laws e) {N r s : PTm k} (hr : Γ ⊢[PRAAx] kept e l N r)
    (hs : Γ ⊢[PRAAx] kept e l N s) (h : Γ ⊢[PRAAx] E e (inst1 l r) (inst1 l s)) :
    Γ ⊢[PRAAx] r ≐ s :=
  hr.eqSymm.eqTrans ((rep_congr H h).eqTrans hs)

/-- A retained entry is inequivalent to every earlier entry. -/
theorem kept_scan {N r i : PTm k} (hr : Γ ⊢[PRAAx] kept e l N r) (hi : Γ ⊢[PRAAx] lt i r) :
    Γ ⊢[PRAAx] neg (E e (inst1 l i) (inst1 l r)) :=
  rep_min (lt_congr (.eqRefl _) hr.eqSymm hi)

/-- An entry below `N` that is inequivalent to every earlier entry is retained. -/
theorem kept_of_scan (H : Laws e) {N r : PTm k} (hr : Γ ⊢[PRAAx] lt r N)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift r) ⟶
      neg (E e (inst1 l (var 0)) (inst1 l (Syn.shift r))))) :
    Γ ⊢[PRAAx] kept e l N r := by
  have g := rep_found (x := inst1 l r) hr (H.refl _)
  refine .orE (lt_or_eq_of_le (Prf.andE₂ (Prf.andE₂ g))) ?_ Prf.hyp0
  have i : Γ ⊢[PRAAx] lt (rep e l N (inst1 l r)) r ⟶
      neg (E e (inst1 l (rep e l N (inst1 l r))) (inst1 l r)) := by
    have a := Prf.allE (rep e l N (inst1 l r)) h
    simp only [Fm.subst_imp, Fm.subst_eq, subst_lt, subst_neg, subst_inst2, subst_inst1,
      Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at a
    exact a
  exact .botE _ (.impE (.impE i.wk Prf.hyp0) (Prf.andE₁ (Prf.andE₂ g)).wk)

/-! ## The skeleton from a supplied cover -/

/-- The covering assertion makes the scan succeed. -/
theorem cover_hit {N x : PTm k} (h : Γ ⊢[PRAAx] Cov e l N x) :
    Γ ⊢[PRAAx] lt (rep e l N x) N := by
  refine Prf.exE h ?_
  have e' : Fm.shift (lt (rep e l N x) N) =
      lt (rep e l (Syn.shift N) (Syn.shift x)) (Syn.shift N) := by
    simp [Fm.shift, Syn.shift]
  rw [e']
  exact Prf.andE₁ (rep_found (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0))

/-- `thm:finite-cover-skeleton`: a covered object has a retained representative
`R_{q(x)}`, found by the scan, and equivalent to it. -/
theorem skeleton (H : Laws e) {N x : PTm k} (h : Γ ⊢[PRAAx] Cov e l N x) :
    Γ ⊢[PRAAx] lt (rep e l N x) N ⋏
      (kept e l N (rep e l N x) ⋏ E e (inst1 l (rep e l N x)) x) := by
  have hr := cover_hit h
  exact .andI hr (.andI (rep_idem H hr) (rep_hit hr))

/-- The skeleton as a closed sentence. Variables: `0 = N`, `1 = x`. -/
theorem skeleton_closed (H : Laws e) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Cov e l (var 0) (var 1) ⟶
      (lt (rep e l (var 0) (var 1)) (var 0) ⋏
        (kept e l (var 0) (rep e l (var 0) (var 1)) ⋏
          E e (inst1 l (rep e l (var 0) (var 1))) (var 1)))) :=
  closeUniv 2 (.impI (skeleton H Prf.hyp0))

/-- The scan is constant on classes, as a closed sentence. Variables: `0 = N`, `1 = x`,
`2 = y`. -/
theorem rep_congr_closed (H : Laws e) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (E e (var 1) (var 2) ⟶ (rep e l (var 0) (var 1) ≐ rep e l (var 0) (var 2))) :=
  closeUniv 3 (.impI (rep_congr H Prf.hyp0))

/-! ## An instance: equality, and a list without repetitions -/

/-- `1 ∸ [a = b]`: zero exactly when `a = b`. -/
def eqE : PTm 2 := monus one (eqb (var 0) (var 1))

theorem inst2_eqE (a b : PTm k) : inst2 eqE a b = monus one (eqb a b) := by simp [inst2, eqE]

theorem eqE_of_eq {a b : PTm k} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] E eqE a b := by
  show Γ ⊢[PRAAx] inst2 eqE a b ≐ zero
  rw [inst2_eqE]
  exact (congrMonus (.eqRefl _) (eqb_of_eq h)).eqTrans (le_refl one)

theorem eq_of_eqE {a b : PTm k} (h : Γ ⊢[PRAAx] E eqE a b) : Γ ⊢[PRAAx] a ≐ b := by
  have h' : Γ ⊢[PRAAx] inst2 eqE a b ≐ zero := h
  rw [inst2_eqE] at h'
  refine .orE (eqb_cases a b) ?_ (eq_of_eqb Prf.hyp0)
  exact one_ne_zero _ ((monus_zero _).eqSymm.eqTrans
    ((congrMonus (.eqRefl _) Prf.hyp0).eqSymm.eqTrans h'.wk))

/-- Equality satisfies the laws. -/
theorem eq_laws : Laws eqE where
  refl a := eqE_of_eq (.eqRefl a)
  symm h := eqE_of_eq (eq_of_eqE h).eqSymm
  trans h₁ h₂ := eqE_of_eq ((eq_of_eqE h₁).eqTrans (eq_of_eqE h₂))

theorem inst1_id (t : PTm k) : inst1 (var 0 : PTm 1) t = t := by simp [inst1]

/-- For equality and the list `L_i = i`, which has no repetitions, the scan retains every
index below `N`. -/
theorem id_kept {N r : PTm k} (hr : Γ ⊢[PRAAx] lt r N) :
    Γ ⊢[PRAAx] kept eqE (var 0) N r := by
  have g := rep_found (e := eqE) (l := var 0) (x := inst1 (var 0) r) hr (eq_laws.refl _)
  have q := eq_of_eqE (Prf.andE₁ (Prf.andE₂ g))
  simp only [inst1_id] at q ⊢
  exact q

/-- The skeleton theorem for equality, as a closed sentence in an arbitrary list term. -/
theorem eq_skeleton_closed (l : PTm 1) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (Cov eqE l (var 0) (var 1) ⟶
      (lt (rep eqE l (var 0) (var 1)) (var 0) ⋏
        (kept eqE l (var 0) (rep eqE l (var 0) (var 1)) ⋏
          E eqE (inst1 l (rep eqE l (var 0) (var 1))) (var 1)))) :=
  skeleton_closed eq_laws

end LeanProofs.IPRA.Foundations.FiniteCoverSkeleton
