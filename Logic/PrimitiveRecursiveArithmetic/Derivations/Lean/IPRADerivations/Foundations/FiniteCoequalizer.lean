import IPRADerivations.Foundations.FiniteSetCategory
import IPRADerivations.Foundations.FiniteQuotient

/-!
# Coequalizers of finite sets by sequential merging (`ipra_categorical_methods`, Section 4)

Packet: `foundations/ipra_categorical_methods`, Subsection "Finite colimits by bounded
equivalence closure": "Its equivalence closure can be computed by finite reachability. ... A
cocone `t_i : [d_i] → [z]` has equal values on every generating edge. ... This proves the
colimit universal property with a PR mediator. ... a parallel pair yields a coequalizer".

For a parallel pair `f, g : [a] → [N]` (closed unary terms, totalized as `F(j) = f(j) mod N`,
`G(j) = g(j) mod N`), the coequalizer is computed without a closure matrix, by merging one
generating edge per step. The state is the code `Λ_i` of a label table `[N] → [N]`:

* `Λ_0` is the identity table;
* `Λ_{i+1}(u) = Λ_i(F(i))` if `Λ_i(u) = Λ_i(G(i))`, and `Λ_i(u)` otherwise (`rho`).

`lab i N u` is the label of `u` after `i` steps; the quotient map is `q = lab a N`. Labels are
elements of `[N]` (`lab_lt`). For `N ≥ 1`:

* `lab_zero`, `lab_succ`: the recursion, entrywise;
* `coeq_merge`: `q(F(j)) = q(G(j))` for every `j < a`: `q ∘ f = q ∘ g`;
* `coeq_factor`: for a cocone `t` (a closed unary term with `t(F(j)) = t(G(j))` for `j < a`,
  given as the bit `Coc`; `coc_of_all` produces the bit from the quantified statement),
  `t(q(u)) = t(u)` for `u < N`: the mediator is `t` itself, restricted to labels;
* `coeq_unique`: a table `v` with `v ∘ q = t` at `u` agrees with `t` at the label `q(u)`;
* `coeq_merge_closed`, `coeq_factor_closed`: closed sentences.

The merge equations are proved pointwise in `j` (`merge₀`); the cocone invariant
`∀ u < N, t(Λ_i(u)) = t(u)` is the bit `allB … = 1` and is carried through quantifier-free
induction on `i` (`inv₀`). This replaces the packet's Warshall recurrence and its path
invariant: no reachability relation is constructed. Not derived: the description of the
fibres of `q` as the classes of the generated equivalence, the compaction of the labels to
`[q]`, and colimits of diagrams other than a parallel pair (a general finite diagram reduces to
this case by the coproduct of `Foundations/FiniteSetCoproducts`; that reduction is not stated).
-/

namespace LeanProofs.IPRA.Foundations.FiniteCoequalizer

open_ipra exports
open LeanProofs.IPRA.Probability.ProductPower (dg rem_lt'')
open LeanProofs.IPRA.Foundations.BoundedReflection
  (allB all_elim all_intro eqb_cases eq_of_eqb one_ne_zero)
open LeanProofs.IPRA.Foundations.FiniteSetExponential
open LeanProofs.IPRA.Foundations.FiniteSetCategory
open LeanProofs.IPRA.Foundations.FiniteQuotient (congrInst1)

variable {k : ℕ} {Γ : List (Fm PTm k)}

/-- Congruence of the equality bit. -/
alias eqb_congr' := Common.congrEqb

theorem shift_succ' (a : PTm k) : Syn.shift (succ a) = succ (Syn.shift a) := by
  simp [Syn.shift]

theorem shift_zero' : Syn.shift (zero : PTm k) = zero := by simp [Syn.shift]

variable (f g : PTm 1)

/-! ## The relabelling step -/

/-- The label of `F(i)` in the table `Λ`. -/
abbrev fv (i N Λ : PTm k) : PTm k := dg N (rem (inst1 f i) N) Λ
/-- The label of `G(i)` in the table `Λ`. -/
abbrev gv (i N Λ : PTm k) : PTm k := dg N (rem (inst1 g i) N) Λ

/-- The relabelling `ρ_i(l)`: the label of `G(i)` is replaced by the label of `F(i)`. -/
abbrev rho (i N Λ l : PTm k) : PTm k :=
  eqb l (gv g i N Λ) * fv f i N Λ + monus one (eqb l (gv g i N Λ)) * l

theorem rho_eq {i N Λ l : PTm k} (h : Γ ⊢[PRAAx] eqb l (gv g i N Λ) ≐ one) :
    Γ ⊢[PRAAx] rho f g i N Λ l ≐ fv f i N Λ := by
  ipra_lc 𝔞 (fv f i N Λ) * natEq h + 𝔞 l * natEq ((congrMonus (.eqRefl (one : PTm k)) h).eqTrans (le_refl one))

theorem rho_ne {i N Λ l : PTm k} (h : Γ ⊢[PRAAx] eqb l (gv g i N Λ) ≐ zero) :
    Γ ⊢[PRAAx] rho f g i N Λ l ≐ l := by
  ipra_lc 𝔞 (fv f i N Λ) * natEq h + 𝔞 l * natEq ((congrMonus (.eqRefl (one : PTm k)) h).eqTrans (monus_zero _))

theorem rho_congr {i N Λ l l' : PTm k} (h : Γ ⊢[PRAAx] l ≐ l') :
    Γ ⊢[PRAAx] rho f g i N Λ l ≐ rho f g i N Λ l' :=
  congrAdd (congrMul (eqb_congr' h (.eqRefl _)) (.eqRefl _))
    (congrMul (congrMonus (.eqRefl _) (eqb_congr' h (.eqRefl _))) h)

theorem rho_lt {i N Λ l : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hl : Γ ⊢[PRAAx] lt l N) : Γ ⊢[PRAAx] lt (rho f g i N Λ l) N :=
  .orE (eqb_cases l (gv g i N Λ))
    (lt_congr (rho_ne f g Prf.hyp0).eqSymm (.eqRefl _) hl.wk)
    (lt_congr (rho_eq f g Prf.hyp0).eqSymm (.eqRefl _) (dg_lt hN.wk _ _))

/-- The relabelled entry as a term in `0 = u`, `1 = i`, `2 = N`, `3 = Λ`. -/
def relG : PTm 4 :=
  eqb (dg (var 2) (var 0) (var 3)) (dg (var 2) (rem (inst1 g (var 1)) (var 2)) (var 3)) *
      dg (var 2) (rem (inst1 f (var 1)) (var 2)) (var 3) +
    monus one
        (eqb (dg (var 2) (var 0) (var 3)) (dg (var 2) (rem (inst1 g (var 1)) (var 2)) (var 3))) *
      dg (var 2) (var 0) (var 3)

/-- The relabelled table; variables `0 = u`, `1 = ⟨i, ⟨N, Λ⟩⟩`. -/
def relT : PTm 2 :=
  Syn.subst ![var 0, fstT (var 1), fstT (sndT (var 1)), sndT (sndT (var 1))] (relG f g)

theorem relT_at (u i N Λ : PTm k) :
    Γ ⊢[PRAAx] inst2 (relT f g) u (pairT i (pairT N Λ)) ≐ rho f g i N Λ (dg N u Λ) := by
  have value : rho f g i N Λ (dg N u Λ) = Syn.subst ![u, i, N, Λ] (relG f g) := by
    simp [relG]
  rw [value]
  simpa [inst2, relT, pairVector, pairVectorField] using
    (subst_pairVector_eq (Γ := Γ) (relG f g) u ![i, N, Λ])

/-! ## The label tables -/

/-- `Λ_0`: the identity table of `[N]`; variable `0 = N`. -/
def lamBase : PTm 1 := code idT (var 0) (var 0) zero

/-- `Λ_{i+1}` from `Λ_i`; variables `0 = i`, `1 = Λ_i`, `2 = N`. -/
def lamStep : PTm 3 :=
  code (relT f g) (var 2) (var 2) (pairT (var 0) (pairT (var 2) (var 1)))

/-- The code `Λ_i` of the label table after `i` merging steps. -/
abbrev lam (i N : PTm k) : PTm k := ap2 (rec2 lamBase (lamStep f g)) i N

/-- The label of `u` after `i` merging steps. -/
abbrev lab (i N u : PTm k) : PTm k := dg N u (lam f g i N)

theorem lam_zero (N : PTm k) : Γ ⊢[PRAAx] lam f g zero N ≐ code idT N N zero := by
  have h := rec2_zero (Γ := Γ) lamBase (lamStep f g) N
  have e : Syn.subst ![N] lamBase = code idT N N zero := by simp [lamBase]
  rw [e] at h
  exact h

theorem lam_succ (i N : PTm k) :
    Γ ⊢[PRAAx] lam f g (succ i) N ≐
      code (relT f g) N N (pairT i (pairT N (lam f g i N))) := by
  have h := rec2_succ (Γ := Γ) lamBase (lamStep f g) i N
  have e : Syn.subst ![i, ap2 (rec2 lamBase (lamStep f g)) i N, N] (lamStep f g) =
      code (relT f g) N N (pairT i (pairT N (lam f g i N))) := by
    show Syn.subst ![i, ap2 (rec2 lamBase (lamStep f g)) i N, N]
      (code (relT f g) (var 2) (var 2) (pairT (var 0) (pairT (var 2) (var 1)))) = _
    simp
  rw [e] at h
  exact h

/-- Labels are elements of `[N]`. -/
theorem lab_lt {N : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (i u : PTm k) :
    Γ ⊢[PRAAx] lt (lab f g i N u) N := dg_lt hN _ _

/-- Initially every element is its own label. -/
theorem lab_zero {N u : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] lab f g zero N u ≐ u :=
  (congrAp2 remF (congrAp2 quoF (lam_zero f g N) (.eqRefl _)) (.eqRefl _)).eqTrans (ev_id hN hu)

/-- One merging step relabels every entry by `ρ_i`. -/
theorem lab_succ {i N u : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] lab f g (succ i) N u ≐ rho f g i N (lam f g i N) (lab f g i N u) :=
  (congrAp2 remF (congrAp2 quoF (lam_succ f g i N) (.eqRefl _)) (.eqRefl _)).eqTrans
    ((ev_curry (relT f g) hN hu _).eqTrans
      ((congrAp2 remF (relT_at f g u i N (lam f g i N)) (.eqRefl _)).eqTrans
        (rem_of_lt hN (rho_lt f g hN (dg_lt hN _ _)))))

/-! ## The quotient map coequalizes -/

theorem merge_step {i j N : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hj : Γ ⊢[PRAAx] lt j (succ i))
    (ih : Γ ⊢[PRAAx] lt j i ⟶
      (lab f g i N (rem (inst1 f j) N) ≐ lab f g i N (rem (inst1 g j) N))) :
    Γ ⊢[PRAAx] lab f g (succ i) N (rem (inst1 f j) N) ≐
      lab f g (succ i) N (rem (inst1 g j) N) := by
  have hle : Γ ⊢[PRAAx] le j i := (succ_monus_succ j i).eqSymm.eqTrans hj
  have sF := lab_succ f g (i := i) hN (rem_lt'' hN (inst1 f j))
  have sG := lab_succ f g (i := i) hN (rem_lt'' hN (inst1 g j))
  refine .orE (lt_or_eq_of_le hle) ?_ ?_
  · exact sF.wk.eqTrans ((rho_congr f g (.impE ih.wk Prf.hyp0)).eqTrans sG.wk.eqSymm)
  · have hji : ((j ≐ i) :: Γ) ⊢[PRAAx] j ≐ i := Prf.hyp0
    have eF : ((j ≐ i) :: Γ) ⊢[PRAAx] lab f g i N (rem (inst1 f j) N) ≐
        fv f i N (lam f g i N) :=
      dg_idx (congrAp2 remF (congrInst1 f hji) (.eqRefl _))
    have eG : ((j ≐ i) :: Γ) ⊢[PRAAx] lab f g i N (rem (inst1 g j) N) ≐
        gv g i N (lam f g i N) :=
      dg_idx (congrAp2 remF (congrInst1 g hji) (.eqRefl _))
    have rF : ((j ≐ i) :: Γ) ⊢[PRAAx]
        rho f g i N (lam f g i N) (fv f i N (lam f g i N)) ≐ fv f i N (lam f g i N) :=
      .orE (eqb_cases (fv f i N (lam f g i N)) (gv g i N (lam f g i N)))
        (rho_ne f g Prf.hyp0) (rho_eq f g Prf.hyp0)
    have rG : ((j ≐ i) :: Γ) ⊢[PRAAx]
        rho f g i N (lam f g i N) (gv g i N (lam f g i N)) ≐ fv f i N (lam f g i N) :=
      rho_eq f g (eqb_of_eq (.eqRefl _))
    exact sF.wk.eqTrans (((rho_congr f g eF).eqTrans rF).eqTrans
      (sG.wk.eqTrans ((rho_congr f g eG).eqTrans rG)).eqSymm)

/-- Variables: `0 = i`, `1 = j`, `2 = N`. -/
private abbrev mergeF : Fm PTm 3 :=
  (var 2 ≐ succ (pred (var 2))) ⟶ lt (var 1) (var 0) ⟶
    (lab f g (var 0) (var 2) (rem (inst1 f (var 1)) (var 2)) ≐
      lab f g (var 0) (var 2) (rem (inst1 g (var 1)) (var 2)))

private theorem merge₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] mergeF f g := by
  ipra_ind (⟨trivial, trivial, trivial⟩) [subst_lt, subst_ap2, subst_inst1]
  · exact .impI (.impI (lt_zero_absurd _ Prf.hyp0))
  · exact .impI (.impI (merge_step f g Prf.hyp1 Prf.hyp0 (.impE hyp2 Prf.hyp1)))

/-- After `i` steps the first `i` generating edges are merged. -/
theorem merged {i j N : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hj : Γ ⊢[PRAAx] lt j i) :
    Γ ⊢[PRAAx] lab f g i N (rem (inst1 f j) N) ≐ lab f g i N (rem (inst1 g j) N) := by
  have h := inst (Γ := Γ) (merge₀ f g) (![i, j, N] : Fin 3 → PTm k)
  simp at h
  exact .impE (.impE h hN) hj

/-! ## Cocones factor through the quotient map -/

variable (t : PTm 1)

/-- The cocone bit `[t(F(j)) = t(G(j))]`; variables `0 = j`, `1 = N`. -/
def cT : PTm 2 :=
  eqb (inst1 t (rem (inst1 f (var 0)) (var 1))) (inst1 t (rem (inst1 g (var 0)) (var 1)))

theorem inst2_cT (j N : PTm k) : inst2 (cT f g t) j N =
    eqb (inst1 t (rem (inst1 f j) N)) (inst1 t (rem (inst1 g j) N)) := by
  show Syn.subst ![j, N] (cT f g t) = _
  simp [cT]

/-- The cocone condition `∀ j < a, t(F(j)) = t(G(j))` as a bit equation. -/
abbrev Coc (a N : PTm k) : Fm PTm k := allB (cT f g t) a N ≐ one

theorem coc_elim {a N j : PTm k} (h : Γ ⊢[PRAAx] Coc f g t a N) (hj : Γ ⊢[PRAAx] lt j a) :
    Γ ⊢[PRAAx] inst1 t (rem (inst1 f j) N) ≐ inst1 t (rem (inst1 g j) N) := by
  have e := all_elim (cT f g t) h hj
  rw [inst2_cT] at e
  exact eq_of_eqb_ne e

/-- The cocone bit from the quantified cocone condition. -/
theorem coc_of_all {a N : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift a) ⟶
      (inst1 t (rem (inst1 f (var 0)) (Syn.shift N)) ≐
        inst1 t (rem (inst1 g (var 0)) (Syn.shift N))))) :
    Γ ⊢[PRAAx] Coc f g t a N := by
  refine all_intro (cT f g t) (.allI (.impI ?_))
  rw [inst2_cT]
  exact .impI (one_ne_zero _
    ((eqb_of_eq (Prf.impE h.allOpen.wk.wk Prf.hyp1)).eqSymm.eqTrans Prf.hyp0))

/-- The invariant bit `[t(Λ_i(u)) = t(u)]` as a term in `0 = u`, `1 = i`, `2 = N`. -/
def kG : PTm 3 :=
  eqb (inst1 t (dg (var 2) (var 0) (ap2 (rec2 lamBase (lamStep f g)) (var 1) (var 2))))
    (inst1 t (var 0))

/-- The invariant bit; variables `0 = u`, `1 = ⟨i, N⟩`. -/
def kT : PTm 2 := Syn.subst ![var 0, fstT (var 1), sndT (var 1)] (kG f g t)

theorem kT_at (u i N : PTm k) :
    Γ ⊢[PRAAx] inst2 (kT f g t) u (pairT i N) ≐ eqb (inst1 t (lab f g i N u)) (inst1 t u) := by
  have value : eqb (inst1 t (lab f g i N u)) (inst1 t u) = Syn.subst ![u, i, N] (kG f g t) := by
    simp [kG]
  rw [value]
  simpa [inst2, kT, pairVector, pairVectorField] using
    (subst_pairVector_eq (Γ := Γ) (kG f g t) u ![i, N])

/-- The invariant `∀ u < N, t(Λ_i(u)) = t(u)` as a bit equation. -/
abbrev Inv (i N : PTm k) : Fm PTm k := allB (kT f g t) N (pairT i N) ≐ one

theorem inv_elim {i N u : PTm k} (h : Γ ⊢[PRAAx] Inv f g t i N) (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] inst1 t (lab f g i N u) ≐ inst1 t u :=
  eq_of_eqb_ne (.impI (.impE (all_elim (kT f g t) h hu).wk
    ((kT_at f g t u i N).eqTrans Prf.hyp0)))

theorem ne_of_pt {u i N : PTm k} (e : Γ ⊢[PRAAx] inst1 t (lab f g i N u) ≐ inst1 t u) :
    Γ ⊢[PRAAx] neg (inst2 (kT f g t) u (pairT i N) ≐ zero) :=
  .impI (one_ne_zero _ ((eqb_of_eq e.wk).eqSymm.eqTrans
    ((kT_at f g t u i N).eqSymm.eqTrans Prf.hyp0)))

theorem inv_intro {i N : PTm k}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst1 t (lab f g (Syn.shift i) (Syn.shift N) (var 0)) ≐ inst1 t (var 0)))) :
    Γ ⊢[PRAAx] Inv f g t i N := by
  refine all_intro (kT f g t) (.allI (.impI ?_))
  rw [shift_pairT]
  exact ne_of_pt f g t (.impE h.allOpen.wk Prf.hyp0)

/-- The invariant holds for the identity table. -/
theorem inv_zero {N : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] Inv f g t zero N := by
  refine inv_intro f g t (.allI (.impI ?_))
  rw [shift_zero']
  have hN' := hN.shift
  rw [shift_pos] at hN'
  exact congrInst1 t (lab_zero f g hN'.wk Prf.hyp0)

theorem step_pt {i N u : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hK : Γ ⊢[PRAAx] Inv f g t i N)
    (hC : Γ ⊢[PRAAx] inst1 t (rem (inst1 f i) N) ≐ inst1 t (rem (inst1 g i) N))
    (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] inst1 t (lab f g (succ i) N u) ≐ inst1 t u := by
  have ku := inv_elim f g t hK hu
  have kF := inv_elim f g t hK (rem_lt'' hN (inst1 f i))
  have kG' := inv_elim f g t hK (rem_lt'' hN (inst1 g i))
  refine (congrInst1 t (lab_succ f g hN hu)).eqTrans ?_
  refine .orE (eqb_cases (lab f g i N u) (gv g i N (lam f g i N))) ?_ ?_
  · exact (congrInst1 t (rho_ne f g Prf.hyp0)).eqTrans ku.wk
  · have el : ((eqb (lab f g i N u) (gv g i N (lam f g i N)) ≐ one) :: Γ) ⊢[PRAAx]
        lab f g i N u ≐ gv g i N (lam f g i N) := eq_of_eqb Prf.hyp0
    exact (congrInst1 t (rho_eq f g Prf.hyp0)).eqTrans
      (kF.wk.eqTrans (hC.wk.eqTrans (kG'.wk.eqSymm.eqTrans
        ((congrInst1 t el).eqSymm.eqTrans ku.wk))))

/-- One merging step along a generating edge of the cocone preserves the invariant. -/
theorem inv_step {i N : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hK : Γ ⊢[PRAAx] Inv f g t i N)
    (hC : Γ ⊢[PRAAx] inst1 t (rem (inst1 f i) N) ≐ inst1 t (rem (inst1 g i) N)) :
    Γ ⊢[PRAAx] Inv f g t (succ i) N := by
  refine inv_intro f g t (.allI (.impI ?_))
  rw [shift_succ']
  have hN' := hN.shift
  rw [shift_pos] at hN'
  have hK' := hK.shift
  have eK : Fm.shift (Inv f g t i N) = Inv f g t (Syn.shift i) (Syn.shift N) := by
    simp [Fm.shift, Syn.shift]
  rw [eK] at hK'
  have hC' := hC.shift
  have eC : Fm.shift (inst1 t (rem (inst1 f i) N) ≐ inst1 t (rem (inst1 g i) N)) =
      (inst1 t (rem (inst1 f (Syn.shift i)) (Syn.shift N)) ≐
        inst1 t (rem (inst1 g (Syn.shift i)) (Syn.shift N))) := by
    simp [Fm.shift, Syn.shift]
  rw [eC] at hC'
  exact step_pt f g t hN'.wk hK'.wk hC'.wk Prf.hyp0

/-- Variables: `0 = i`, `1 = a`, `2 = N`. -/
private abbrev invF : Fm PTm 3 :=
  (var 2 ≐ succ (pred (var 2))) ⟶ Coc f g t (var 1) (var 2) ⟶ le (var 0) (var 1) ⟶
    Inv f g t (var 0) (var 2)

private theorem inv₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] invF f g t := by
  ipra_ind (⟨trivial, trivial, trivial, trivial⟩) [subst_le, subst_ap2, subst_pairT]
  · exact .impI (.impI (.impI (inv_zero f g t hyp2)))
  · refine .impI (.impI (.impI ?_))
    have hN : [le (succ (var 0 : PTm 3)) (var 1), Coc f g t (var 1 : PTm 3) (var 2),
        (var 2 : PTm 3) ≐ succ (pred (var 2)), invF f g t] ⊢[PRAAx]
        (var 2 : PTm 3) ≐ succ (pred (var 2)) := hyp2
    have hC : [le (succ (var 0 : PTm 3)) (var 1), Coc f g t (var 1 : PTm 3) (var 2),
        (var 2 : PTm 3) ≐ succ (pred (var 2)), invF f g t] ⊢[PRAAx]
        Coc f g t (var 1 : PTm 3) (var 2) := Prf.hyp1
    have hi : [le (succ (var 0 : PTm 3)) (var 1), Coc f g t (var 1 : PTm 3) (var 2),
        (var 2 : PTm 3) ≐ succ (pred (var 2)), invF f g t] ⊢[PRAAx]
        le (succ (var 0 : PTm 3)) (var 1) := Prf.hyp0
    have IH : [le (succ (var 0 : PTm 3)) (var 1), Coc f g t (var 1 : PTm 3) (var 2),
        (var 2 : PTm 3) ≐ succ (pred (var 2)), invF f g t] ⊢[PRAAx] invF f g t :=
      Prf.hyp (by simp)
    have ih := Prf.impE (Prf.impE (Prf.impE IH hN) hC) (le_trans (le_succ_self _) hi)
    exact inv_step f g t hN ih (coc_elim f g t hC hi)

/-- The invariant after any number `i ≤ a` of merging steps. -/
theorem inv_all {a N i : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hC : Γ ⊢[PRAAx] Coc f g t a N) (hi : Γ ⊢[PRAAx] le i a) :
    Γ ⊢[PRAAx] Inv f g t i N := by
  have h := inst (Γ := Γ) (inv₀ f g t) (![i, a, N] : Fin 3 → PTm k)
  simp at h
  exact .impE (.impE (.impE h hN) hC) hi

/-! ## The universal property -/

/-- `q ∘ f = q ∘ g` for the quotient map `q = lab a N`. -/
theorem coeq_merge {a N j : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hj : Γ ⊢[PRAAx] lt j a) :
    Γ ⊢[PRAAx] lab f g a N (rem (inst1 f j) N) ≐ lab f g a N (rem (inst1 g j) N) :=
  merged f g hN hj

/-- A cocone factors through the quotient map: `t(q(u)) = t(u)`. -/
theorem coeq_factor {a N u : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hC : Γ ⊢[PRAAx] Coc f g t a N) (hu : Γ ⊢[PRAAx] lt u N) :
    Γ ⊢[PRAAx] inst1 t (lab f g a N u) ≐ inst1 t u :=
  inv_elim f g t (inv_all f g t hN hC (le_refl a)) hu

/-- Uniqueness of the mediator on labels: a table `v` with `v(q(u)) = t(u)` agrees with `t` at
the label `q(u)`. -/
theorem coeq_unique {v : PTm 1} {a N u : PTm k} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hC : Γ ⊢[PRAAx] Coc f g t a N) (hu : Γ ⊢[PRAAx] lt u N)
    (hv : Γ ⊢[PRAAx] inst1 v (lab f g a N u) ≐ inst1 t u) :
    Γ ⊢[PRAAx] inst1 v (lab f g a N u) ≐ inst1 t (lab f g a N u) :=
  hv.eqTrans (coeq_factor f g t hN hC hu).eqSymm

/-- `q ∘ f = q ∘ g` as a closed sentence. Variables: `0 = a`, `1 = N`, `2 = j`. -/
theorem coeq_merge_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((var 1 ≐ succ (pred (var 1))) ⟶ lt (var 2) (var 0) ⟶
      (lab f g (var 0) (var 1) (rem (inst1 f (var 2)) (var 1)) ≐
        lab f g (var 0) (var 1) (rem (inst1 g (var 2)) (var 1)))) :=
  closeUniv 3 (.impI (.impI (coeq_merge f g Prf.hyp1 Prf.hyp0)))

/-- The factorization of cocones as a closed sentence. Variables: `0 = a`, `1 = N`, `2 = u`. -/
theorem coeq_factor_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    ((var 1 ≐ succ (pred (var 1))) ⟶ Coc f g t (var 0) (var 1) ⟶ lt (var 2) (var 1) ⟶
      (inst1 t (lab f g (var 0) (var 1) (var 2)) ≐ inst1 t (var 2))) :=
  closeUniv 3 (.impI (.impI (.impI (coeq_factor f g t hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Foundations.FiniteCoequalizer
