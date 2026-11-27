import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.AnalyticNumberTheory.Valuation
import IPRADerivations.Core.Header

/-!
# Uniform finite gluing (`ipra_categorical_methods`, `thm:finite-glue`)

Packet: `foundations/ipra_categorical_methods`, Section 5, Subsection "A finite sheaf of
function tables", Theorem `thm:finite-glue`.

The data are two terms in the packed parameter `⟨x, q⟩` (`x` a point of `X = [N]`, `q` an
arbitrary parameter, for example the code of the cover and of the local tables):

* a mask `u(i, ⟨x, q⟩)`: `x ∈ U_i` when `u(i, ⟨x, q⟩) ≠ 0`;
* a section `f(i, ⟨x, q⟩)`: the value `f_i(x)`.

The two hypotheses of the packet are bounded Boolean tests, primitive-recursive bits built
with the aggregators of `Foundations/BoundedReflection`:

* `covB u N K q`, the bit of (5.1) `∀ x < N ∃ i < K (x ∈ U_i)`;
* `ovB u f N K q`, the bit of (5.2)
  `∀ x < N ∀ i < K ∀ j < K (x ∈ U_i ∧ x ∈ U_j → f_i(x) = f_j(x))`.

The glued table is `glue(x) = f_{i(x)}(x)` with `i(x) = first u K x q` the first mask
containing `x` (bounded search). Derived:

* `first_spec`: if the cover test passes and `x < N`, then `i(x) < K` and `x ∈ U_{i(x)}`;
* `overlap_elim`: if the overlap test passes, compatible sections agree at `x`;
* `glue_restrict` (`thm:finite-glue`, existence): `glue(x) = f_j(x)` whenever `x ∈ U_j`,
  `j < K`, `x < N`; closed sentence `gluing_closed`;
* `glue_unique` (uniqueness): a value `g` with `g = f_j(x)` for every `j < K` with `x ∈ U_j`
  equals `glue(x)`;
* `glue_of_global`: if every section is the restriction of one table `g`, gluing recovers
  `g(x)` (restriction followed by gluing);
* `glue_lt`: if the sections take values below `m` on their masks, so does the glued table.

The choice of the first covering patch affects the term `glue` but not its value: by
`glue_restrict` it equals every section defined at `x`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.FiniteGluing

open_ipra
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Foundations.BoundedReflection
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- A bit that is not `0` is `1`. -/
theorem one_of_ne {a : PTm k} (hc : Γ ⊢[PRAAx] (a ≐ zero) ⋎ (a ≐ one))
    (h : Γ ⊢[PRAAx] neg (a ≐ zero)) : Γ ⊢[PRAAx] a ≐ one :=
  .orE hc (.botE _ (.impE h.wk Prf.hyp0)) Prf.hyp0

/-- `sg a = 1` for `a ≠ 0`. -/
theorem sg_of_ne {a : PTm k} (h : Γ ⊢[PRAAx] neg (a ≐ zero)) : Γ ⊢[PRAAx] sg a ≐ one :=
  .orE (zero_or_succ a) (.botE _ (.impE h.wk Prf.hyp0)) (sg_of_pos Prf.hyp0)

section Glue

variable (u f : PTm 2)

/-- The first mask containing `x`: the least `i < K` with `u(i, ⟨x, q⟩) ≠ 0`. -/
abbrev first (K x q : PTm k) : PTm k := wit u K (pairT x q)

/-- The glued table `glue(x) = f_{i(x)}(x)`. -/
abbrev glue (K x q : PTm k) : PTm k := inst2 f (first u K x q) (pairT x q)

/-! ### The cover test -/

/-- `[∃ i < K, x ∈ U_i]`; variables `0 = x`, `1 = ⟨K, q⟩`. -/
def cv : PTm 2 := exB u (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem cv_at (x K q : PTm k) :
    Γ ⊢[PRAAx] inst2 (cv u) x (pairT K q) ≐ exB u K (pairT x q) := by
  have e₁ : inst2 (cv u) x (pairT K q) =
      Syn.subst ![fstT (pairT K q), x, sndT (pairT K q)]
        (exB u (var 0 : PTm 3) (pairT (var 1) (var 2))) := by
    show Syn.subst ![x, pairT K q] (cv u) = _
    simp [cv]
  have e₂ : exB u K (pairT x q) =
      Syn.subst ![K, x, q] (exB u (var 0 : PTm 3) (pairT (var 1) (var 2))) := by simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun j => by
    fin_cases j
    · exact fst_pair _ _
    · exact .eqRefl _
    · exact snd_pair _ _

/-- The bit of the cover condition (5.1). -/
abbrev covB (N K q : PTm k) : PTm k := allB (cv u) N (pairT K q)

/-- If the cover test passes, the first mask containing `x < N` exists. -/
theorem first_spec {N K x q : PTm k} (hc : Γ ⊢[PRAAx] covB u N K q ≐ one)
    (hx : Γ ⊢[PRAAx] lt x N) :
    Γ ⊢[PRAAx] lt (first u K x q) K ⋏ neg (inst2 u (first u K x q) (pairT x q) ≐ zero) := by
  have a : Γ ⊢[PRAAx] neg (inst2 (cv u) x (pairT K q) ≐ zero) := all_elim (cv u) hc hx
  have b : Γ ⊢[PRAAx] neg (exB u K (pairT x q) ≐ zero) :=
    .impI (.impE a.wk ((cv_at u x K q).eqTrans Prf.hyp0))
  exact ex_elim u (one_of_ne (ex_cases u K (pairT x q)) b)

/-! ### The overlap test -/

/-- `[x ∈ U_i ∧ x ∈ U_j → f_i(x) = f_j(x)]`, nonzero when the implication holds; variables
`0 = j`, `1 = ⟨i, y⟩` with `y = ⟨x, q⟩`. -/
def o3 : PTm 2 :=
  monus one (sg (inst2 u (fstT (var 1)) (sndT (var 1))) * sg (inst2 u (var 0) (sndT (var 1)))) +
    eqb (inst2 f (fstT (var 1)) (sndT (var 1))) (inst2 f (var 0) (sndT (var 1)))

theorem o3_at (j i y : PTm k) :
    Γ ⊢[PRAAx] inst2 (o3 u f) j (pairT i y) ≐
      monus one (sg (inst2 u i y) * sg (inst2 u j y)) + eqb (inst2 f i y) (inst2 f j y) := by
  have e₁ : inst2 (o3 u f) j (pairT i y) =
      Syn.subst ![fstT (pairT i y), j, sndT (pairT i y)]
        (monus one (sg (inst2 u (var 0 : PTm 3) (var 2)) * sg (inst2 u (var 1) (var 2))) +
          eqb (inst2 f (var 0) (var 2)) (inst2 f (var 1) (var 2))) := by
    show Syn.subst ![j, pairT i y] (o3 u f) = _
    simp [o3]
  have e₂ : monus one (sg (inst2 u i y) * sg (inst2 u j y)) + eqb (inst2 f i y) (inst2 f j y) =
      Syn.subst ![i, j, y]
        (monus one (sg (inst2 u (var 0 : PTm 3) (var 2)) * sg (inst2 u (var 1) (var 2))) +
          eqb (inst2 f (var 0) (var 2)) (inst2 f (var 1) (var 2))) := by simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact fst_pair _ _
    · exact .eqRefl _
    · exact snd_pair _ _

/-- `[∀ j < K, …]`; variables `0 = i`, `1 = ⟨K, y⟩`. -/
def o2 : PTm 2 := allB (o3 u f) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem o2_at (i K y : PTm k) :
    Γ ⊢[PRAAx] inst2 (o2 u f) i (pairT K y) ≐ allB (o3 u f) K (pairT i y) := by
  have e₁ : inst2 (o2 u f) i (pairT K y) =
      Syn.subst ![fstT (pairT K y), i, sndT (pairT K y)]
        (allB (o3 u f) (var 0 : PTm 3) (pairT (var 1) (var 2))) := by
    show Syn.subst ![i, pairT K y] (o2 u f) = _
    simp [o2]
  have e₂ : allB (o3 u f) K (pairT i y) =
      Syn.subst ![K, i, y] (allB (o3 u f) (var 0 : PTm 3) (pairT (var 1) (var 2))) := by simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact fst_pair _ _
    · exact .eqRefl _
    · exact snd_pair _ _

/-- `[∀ i < K ∀ j < K, …]`; variables `0 = x`, `1 = ⟨K, q⟩`. -/
def o1 : PTm 2 :=
  allB (o2 u f) (fstT (var 1)) (pairT (fstT (var 1)) (pairT (var 0) (sndT (var 1))))

theorem o1_at (x K q : PTm k) :
    Γ ⊢[PRAAx] inst2 (o1 u f) x (pairT K q) ≐ allB (o2 u f) K (pairT K (pairT x q)) := by
  have e₁ : inst2 (o1 u f) x (pairT K q) =
      Syn.subst ![fstT (pairT K q), x, sndT (pairT K q)]
        (allB (o2 u f) (var 0 : PTm 3) (pairT (var 0) (pairT (var 1) (var 2)))) := by
    show Syn.subst ![x, pairT K q] (o1 u f) = _
    simp [o1]
  have e₂ : allB (o2 u f) K (pairT K (pairT x q)) =
      Syn.subst ![K, x, q]
        (allB (o2 u f) (var 0 : PTm 3) (pairT (var 0) (pairT (var 1) (var 2)))) := by simp
  rw [e₁, e₂]
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact fst_pair _ _
    · exact .eqRefl _
    · exact snd_pair _ _

/-- The bit of the overlap condition (5.2). -/
abbrev ovB (N K q : PTm k) : PTm k := allB (o1 u f) N (pairT K q)

/-- If the overlap test passes, two sections defined at `x < N` agree there. -/
theorem overlap_elim {N K x q i j : PTm k} (ho : Γ ⊢[PRAAx] ovB u f N K q ≐ one)
    (hx : Γ ⊢[PRAAx] lt x N) (hi : Γ ⊢[PRAAx] lt i K) (hj : Γ ⊢[PRAAx] lt j K)
    (hui : Γ ⊢[PRAAx] neg (inst2 u i (pairT x q) ≐ zero))
    (huj : Γ ⊢[PRAAx] neg (inst2 u j (pairT x q) ≐ zero)) :
    Γ ⊢[PRAAx] inst2 f i (pairT x q) ≐ inst2 f j (pairT x q) := by
  -- level 1: the point `x`
  have a₁ := all_elim (o1 u f) ho hx
  have b₁ : Γ ⊢[PRAAx] allB (o2 u f) K (pairT K (pairT x q)) ≐ one :=
    one_of_ne (all_cases _ _ _) (.impI (.impE a₁.wk ((o1_at u f x K q).eqTrans Prf.hyp0)))
  -- level 2: the index `i`
  have a₂ := all_elim (o2 u f) b₁ hi
  have b₂ : Γ ⊢[PRAAx] allB (o3 u f) K (pairT i (pairT x q)) ≐ one :=
    one_of_ne (all_cases _ _ _) (.impI (.impE a₂.wk ((o2_at u f i K _).eqTrans Prf.hyp0)))
  -- level 3: the index `j`
  have a₃ := all_elim (o3 u f) b₂ hj
  exact guarded_eqb_read (o3_at u f j i _)
    ((congrMonus (.eqRefl _) ((congrMul (sg_of_ne hui) (sg_of_ne huj)).eqTrans (one_mul _))).eqTrans
      (le_refl one)) a₃

/-! ### Gluing -/

/-- `thm:finite-glue`, existence: the glued table restricts to every section. -/
theorem glue_restrict {N K x q j : PTm k} (hc : Γ ⊢[PRAAx] covB u N K q ≐ one)
    (ho : Γ ⊢[PRAAx] ovB u f N K q ≐ one) (hx : Γ ⊢[PRAAx] lt x N) (hj : Γ ⊢[PRAAx] lt j K)
    (huj : Γ ⊢[PRAAx] neg (inst2 u j (pairT x q) ≐ zero)) :
    Γ ⊢[PRAAx] glue u f K x q ≐ inst2 f j (pairT x q) := by
  have s := first_spec u hc hx
  exact overlap_elim u f ho hx (.andE₁ s) hj (.andE₂ s) huj

/-- `thm:finite-glue`, uniqueness: a value agreeing with every section defined at `x` is the
glued value. Only the cover test is used. -/
theorem glue_unique {N K x q g : PTm k} (hc : Γ ⊢[PRAAx] covB u N K q ≐ one)
    (hx : Γ ⊢[PRAAx] lt x N)
    (hg : ∀ j : PTm k, Γ ⊢[PRAAx] lt j K ⟶ neg (inst2 u j (pairT x q) ≐ zero) ⟶
      (g ≐ inst2 f j (pairT x q))) :
    Γ ⊢[PRAAx] g ≐ glue u f K x q := by
  have s := first_spec u hc hx
  exact .impE (.impE (hg _) (.andE₁ s)) (.andE₂ s)

/-- Restriction followed by gluing: if every section is the restriction of one table `g`,
the glued value is `g`. -/
theorem glue_of_global {K x q g : PTm k}
    (hf : ∀ i : PTm k, Γ ⊢[PRAAx] inst2 f i (pairT x q) ≐ g) : Γ ⊢[PRAAx] glue u f K x q ≐ g :=
  hf _

/-- If the sections take values below `m` on their masks, so does the glued table. -/
theorem glue_lt {N K x q m : PTm k} (hc : Γ ⊢[PRAAx] covB u N K q ≐ one)
    (hx : Γ ⊢[PRAAx] lt x N)
    (hm : ∀ j : PTm k, Γ ⊢[PRAAx] lt j K ⟶ neg (inst2 u j (pairT x q) ≐ zero) ⟶
      lt (inst2 f j (pairT x q)) m) :
    Γ ⊢[PRAAx] lt (glue u f K x q) m := by
  have s := first_spec u hc hx
  exact .impE (.impE (hm _) (.andE₁ s)) (.andE₂ s)

/-- `thm:finite-glue` as one closed sentence of iPRA, for all masks `u` and sections `f`:
if both Boolean tests pass, the glued table restricts to every section. Variables: `0 = N`,
`1 = K`, `2 = q`, `3 = x`, `4 = j`. -/
theorem gluing_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((covB u (var 0) (var 1) (var 2) ≐ one) ⟶ (ovB u f (var 0) (var 1) (var 2) ≐ one) ⟶
      lt (var 3) (var 0) ⟶ lt (var 4) (var 1) ⟶
      neg (inst2 u (var 4) (pairT (var 3) (var 2)) ≐ zero) ⟶
      (glue u f (var 1) (var 3) (var 2) ≐ inst2 f (var 4) (pairT (var 3) (var 2)))) :=
  closeUniv 5 (.impI (.impI (.impI (.impI (.impI
    (glue_restrict u f (.hyp (by simp)) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0))))))

end Glue

end LeanProofs.IPRA.Foundations.FiniteGluing
