import IPRADerivations.Analysis.Polynomials.RootFinding.RealRoots.PolynomialRootName
import IPRADerivations.Probability.Minkowski

/-!
# Exact rational logistic iteration of a finite regular name

Packet `foundations/ipra_finite_demand`, Section 2,
`thm:nonlinear-name-validity`. Rational inputs have signed natural-pair
numerators and positive denominators. The parameter is the runtime rational
`A/B`, with `B>0` and `A≤4B`. No normalization of fractions is used.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.LogisticName

open_ipra
open LeanProofs.IPRA.Foundations.GapDecision
open LeanProofs.IPRA.Analysis.PolynomialRootName (abs_mul abs_scale abs_ofNat)
open LeanProofs.IPRA.Probability.Variance (ad)
open LeanProofs.IPRA.Probability.MedianWeighted (le_add_ad ad_le_of)
open LeanProofs.IPRA.Probability.Minkowski (monus_le_of_le_add le_add_monus)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Positive-part subtraction contracts signed differences. -/
theorem positive_contraction (a b c d : PTm n) :
    Γ ⊢[PRAAx] le (ad (monus a b) (monus c d)) (ad (a+d) (c+b)) := by
  have first (a b c d : PTm n) : Γ ⊢[PRAAx]
      le (monus a b) (monus c d + ad (a+d) (c+b)) := by
    have bound := le_trans (le_add_ad (Γ := Γ) (a+d) (c+b))
      (add_le_add₂ (add_le_add₂ (le_add_monus c d) (le_refl b))
        (le_refl (ad (a+d) (c+b))))
    have reduced : Γ ⊢[PRAAx] le a (b+(monus c d + ad (a+d) (c+b))) :=
      le_of_add_le_add_right (le_congr (.eqRefl _) (by ipra_ring) bound)
    exact monus_le_of_le_add reduced
  exact ad_le_of (first a b c d)
    (le_congr (.eqRefl _) (congrAdd (.eqRefl _) (add_comm _ _)) (first c d a b))

/-- Multiplication commutes with truncated subtraction, including scale zero. -/
theorem monus_scale (a b c : PTm n) :
    Γ ⊢[PRAAx] monus (c*a) (c*b) ≐ c*monus a b := by
  refine .orE (le_total a b) ?_ ?_
  · exact (show (le a b :: Γ) ⊢[PRAAx] monus (c*a) (c*b) ≐ zero from
      le_mul_mono (le_refl c) Prf.hyp0).eqTrans
      ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)).eqSymm
  · ipra_lc -natEq (eq_add_of_le (le_mul_mono (le_refl c) (Prf.hyp0 : (le b a :: Γ) ⊢[PRAAx] le b a))) +
      𝔞 c * natEq (eq_add_of_le (Prf.hyp0 : (le b a :: Γ) ⊢[PRAAx] le b a))

/-- The literal numerator of `min(1,max(0,(p-q)/D))`. -/
def clip (p q D : PTm n) : PTm n := monus D (monus D (monus p q))

ipra_subst clip

alias monus_le_left := Common.monus_le_self

theorem clip_range (p q D : PTm n) : Γ ⊢[PRAAx] le (clip p q D) D :=
  monus_le_left _ _

/-- Below zero the clipping program returns zero exactly. -/
theorem clip_below {p q D : PTm n} (h : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] clip p q D ≐ zero :=
  (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)).eqTrans
    ((congrMonus (.eqRefl _) (monus_zero D)).eqTrans (monus_self D))

/-- On the middle interval the clipping program is the original rational value. -/
theorem clip_middle {p q D : PTm n} (h : Γ ⊢[PRAAx] le (monus p q) D) :
    Γ ⊢[PRAAx] clip p q D ≐ monus p q :=
  (congrMonus (eq_add_of_le h) (.eqRefl _)).eqTrans (add_monus _ _)

/-- Above one the clipping program returns the denominator exactly. -/
theorem clip_above {p q D : PTm n} (h : Γ ⊢[PRAAx] le D (monus p q)) :
    Γ ⊢[PRAAx] clip p q D ≐ D :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero D)

theorem clip_scale (p q D c : PTm n) :
    Γ ⊢[PRAAx] clip (c*p) (c*q) (c*D) ≐ c*clip p q D := by
  unfold clip
  exact (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (monus_scale p q c))).eqTrans
    ((congrMonus (.eqRefl _) (monus_scale D (monus p q) c)).eqTrans
      (monus_scale D (monus D (monus p q)) c))

theorem clip_contraction (p q r s D : PTm n) :
    Γ ⊢[PRAAx] le (ad (clip p q D) (clip r s D)) (ad (p+s) (r+q)) := by
  have one := positive_contraction (Γ := Γ) D (monus D (monus p q)) D (monus D (monus r s))
  have two := positive_contraction (Γ := Γ) D (monus r s) D (monus p q)
  have three := positive_contraction (Γ := Γ) p q r s
  have eone : Γ ⊢[PRAAx]
      ad (D+monus D (monus r s)) (D+monus D (monus p q)) ≐
        ad (monus D (monus r s)) (monus D (monus p q)) :=
    zabs_congr (u := ⟨D+monus D (monus r s), D+monus D (monus p q)⟩)
      (v := ⟨monus D (monus r s), monus D (monus p q)⟩)
      (by simp only [ZT.toZ, Q.mk_add, map_add]; ring)
  have etwo : Γ ⊢[PRAAx]
      ad (D+monus p q) (D+monus r s) ≐ ad (monus p q) (monus r s) :=
    zabs_congr (u := ⟨D+monus p q, D+monus r s⟩) (v := ⟨monus p q, monus r s⟩)
      (by simp only [ZT.toZ, Q.mk_add, map_add]; ring)
  exact le_trans (le_congr (.eqRefl _) eone one)
    (le_trans (le_congr (.eqRefl _) etwo two) three)

/-- Clipping is nonexpansive for independent rational denominators. -/
theorem clip_rational (p q d r s e : PTm n) :
    Γ ⊢[PRAAx] le (ad (clip p q d * e) (clip r s e * d))
      (ad (p*e+s*d) (r*d+q*e)) := by
  have first := clip_scale (Γ := Γ) p q d e
  have second := clip_scale (Γ := Γ) r s e d
  have changeSecond : Γ ⊢[PRAAx] clip (d*r) (d*s) (e*d) ≐ d*clip r s e :=
    (congrMonus (mul_comm e d)
      (congrMonus (mul_comm e d) (.eqRefl _))).eqTrans second
  exact le_congr
    ((congrAdd (congrMonus first changeSecond) (congrMonus changeSecond first)).eqTrans
      (congrAdd (congrMonus (mul_comm _ _) (mul_comm _ _))
        (congrMonus (mul_comm _ _) (mul_comm _ _))))
    (congrAdd (congrMonus (by ipra_ring) (by ipra_ring))
      (congrMonus (by ipra_ring) (by ipra_ring)))
    (clip_contraction (e*p) (e*q) (d*r) (d*s) (e*d))

/-- Exact unreduced logistic update of a rational point in `[0,1]`. -/
def advance (A B state : PTm n) : PTm n :=
  pairT (A*fstT state*monus (sndT state) (fstT state)) (B*sndT state*sndT state)

ipra_subst advance

theorem advance_num (A B state : PTm n) : Γ ⊢[PRAAx]
    fstT (advance A B state) ≐ A*fstT state*monus (sndT state) (fstT state) := fst_pair _ _

theorem advance_den (A B state : PTm n) : Γ ⊢[PRAAx]
    sndT (advance A B state) ≐ B*sndT state*sndT state := snd_pair _ _

/-- The sharp elementary bound `4t(D-t)≤D²`. -/
theorem quarter_bound {t D : PTm n} (h : Γ ⊢[PRAAx] le t D) :
    Γ ⊢[PRAAx] le (num 4*t*monus D t) (D*D) := by
  have square := zabs_sq (Γ := Γ) (ZT.ofNat D - ZT.ofNat (two*t))
  refine le_of_eq_add (d := zabs (ZT.ofNat D-ZT.ofNat (two*t))*
    zabs (ZT.ofNat D-ZT.ofNat (two*t))) ?_
  ipra_lc (4*𝔞 t)*natEq (eq_add_of_le h) - square

theorem advance_range {A B state : PTm n} (hA : Γ ⊢[PRAAx] le A (num 4*B))
    (hs : Γ ⊢[PRAAx] le (fstT state) (sndT state)) :
    Γ ⊢[PRAAx] le (fstT (advance A B state)) (sndT (advance A B state)) := by
  have bound : Γ ⊢[PRAAx] le (A*fstT state*monus (sndT state) (fstT state))
      (B*sndT state*sndT state) := le_trans
    (le_mul_mono (le_mul_mono hA (le_refl (fstT state))) (le_refl (monus (sndT state) (fstT state))))
    (le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl B) (quarter_bound hs)))
  exact le_congr (advance_num _ _ _).eqSymm (advance_den _ _ _).eqSymm bound

/-- Exact cross-numerator difference of two nonnegative rational points. -/
def difference (s t : PTm n) : ZT n := ⟨fstT s*sndT t, fstT t*sndT s⟩

ipra_subst difference [ZT.subst]

/-- On the unit square the divided-difference factor has modulus at most one. -/
theorem factor_bound {t d s e : PTm n} (ht : Γ ⊢[PRAAx] le t d) (hs : Γ ⊢[PRAAx] le s e) :
    Γ ⊢[PRAAx] le (ad (d*e) (t*e+s*d)) (d*e) := by
  apply ad_le_of
  · exact le_add_left _ _
  · exact le_congr (.eqRefl _) (by ipra_ring)
      (add_le_add₂ (le_mul_mono ht (le_refl e)) (le_mul_mono hs (le_refl d)))

/-- The exact logistic factorization, with independent input denominators. -/
theorem logistic_factor {A B t d s e : PTm n}
    (ht : Γ ⊢[PRAAx] le t d) (hs : Γ ⊢[PRAAx] le s e) :
    Γ ⊢[PRAAx] ad (A*t*monus d t*(B*e*e)) (A*s*monus e s*(B*d*d)) ≐
      A*B*ad (t*e) (s*d)*ad (d*e) (t*e+s*d) := by
  have hd := natEq (eq_add_of_le ht)
  have he := natEq (eq_add_of_le hs)
  have E : Γ ⊢[PRAAx]
      ad (A*t*monus d t*(B*e*e)) (A*s*monus e s*(B*d*d)) ≐
        zabs (ZT.ofNat (A*B) * (⟨t*e,s*d⟩ : ZT n) * (⟨d*e,t*e+s*d⟩ : ZT n)) := by
    apply zabs_congr (u := ⟨_, _⟩)
    simp only [ZT.toZ_mul, ZT.toZ_ofNat]
    simp only [toZ_def, Q.mk_mul, Q.mk_add, map_mul, map_add] at hd he ⊢
    linear_combination -(𝔞 A*𝔞 B*𝔞 t*𝔞 e*𝔞 e)*hd + (𝔞 A*𝔞 B*𝔞 s*𝔞 d*𝔞 d)*he
  exact E.eqTrans ((PolynomialRootName.abs_mul _ _).eqTrans (congrMul (abs_scale _ _) (.eqRefl _)))

/-- Denominator-cleared form of `|T_a(r)-T_a(s)|≤4|r-s|`. -/
theorem advance_lipschitz {A B s t : PTm n}
    (hA : Γ ⊢[PRAAx] le A (num 4*B))
    (hs : Γ ⊢[PRAAx] le (fstT s) (sndT s)) (ht : Γ ⊢[PRAAx] le (fstT t) (sndT t)) :
    Γ ⊢[PRAAx] le (zabs (difference (advance A B s) (advance A B t)))
      (num 4*B*B*sndT s*sndT t*zabs (difference s t)) := by
  have D : Γ ⊢[PRAAx] zabs (difference (advance A B s) (advance A B t)) ≐
      ad (A*fstT s*monus (sndT s) (fstT s)*(B*sndT t*sndT t))
        (A*fstT t*monus (sndT t) (fstT t)*(B*sndT s*sndT s)) := by
    exact congrAdd
      (congrMonus (congrMul (advance_num _ _ _) (advance_den _ _ _))
        (congrMul (advance_num _ _ _) (advance_den _ _ _)))
      (congrMonus (congrMul (advance_num _ _ _) (advance_den _ _ _))
        (congrMul (advance_num _ _ _) (advance_den _ _ _)))
  have H := le_mul_mono (le_mul_mono (le_mul_mono hA (le_refl B))
    (le_refl (ad (fstT s*sndT t) (fstT t*sndT s)))) (factor_bound hs ht)
  exact le_congr (D.eqTrans (logistic_factor hs ht)).eqSymm (by unfold difference; ipra_ring) H

/-- Positivity and range of an encoded nonnegative rational point. -/
def valid (s : PTm n) : Fm PTm n := le one (sndT s) ⋏ le (fstT s) (sndT s)

ipra_subst valid

theorem valid_QF (s : PTm n) : (valid s).QF := ⟨le_QF _ _, le_QF _ _⟩

theorem advance_valid {A B s : PTm n} (hA : Γ ⊢[PRAAx] le A (num 4*B))
    (hB : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] valid s) :
    Γ ⊢[PRAAx] valid (advance A B s) :=
  .andI (le_congr (by ipra_ring) (advance_den _ _ _).eqSymm
    (le_mul_mono (le_mul_mono hB (.andE₁ hs)) (.andE₁ hs)))
    (advance_range hA (.andE₂ hs))

/-- Persistent orbit data contain the parameter and the actual seed. -/
def orbitData (A B seed : PTm n) : PTm n := pairT A (pairT B seed)
def orbitBase : PTm 1 := sndT (sndT (var 0))
def orbitStep : PTm 3 := advance (fstT (var 2)) (fstT (sndT (var 2))) (var 1)
def orbitF : PR 2 := rec2 orbitBase orbitStep
def orbit (N A B seed : PTm n) : PTm n := ap2 orbitF N (orbitData A B seed)

ipra_subst orbit [orbitData, subst_ap2, subst_pairT]

theorem advance_congr {A A' B B' s s' : PTm n}
    (hA : Γ ⊢[PRAAx] A ≐ A') (hB : Γ ⊢[PRAAx] B ≐ B') (hs : Γ ⊢[PRAAx] s ≐ s') :
    Γ ⊢[PRAAx] advance A B s ≐ advance A' B' s' :=
  congrPairT (congrMul (congrMul hA (congrFst hs)) (congrMonus (congrSnd hs) (congrFst hs)))
    (congrMul (congrMul hB (congrSnd hs)) (congrSnd hs))

theorem orbit_zero (A B seed : PTm n) : Γ ⊢[PRAAx] orbit zero A B seed ≐ seed := by
  have eq := rec2_zero (Γ := Γ) orbitBase orbitStep (orbitData A B seed)
  simp only [orbitBase, subst_sndT, Syn.subst_var, Matrix.cons_val_zero] at eq
  exact eq.eqTrans ((congrSnd (snd_pair A (pairT B seed))).eqTrans (snd_pair B seed))

theorem orbit_succ (N A B seed : PTm n) :
    Γ ⊢[PRAAx] orbit (succ N) A B seed ≐ advance A B (orbit N A B seed) := by
  have eq := rec2_succ (Γ := Γ) orbitBase orbitStep N (orbitData A B seed)
  simp only [orbitStep, subst_advance, subst_fstT, subst_sndT, Syn.subst_var,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at eq
  exact eq.eqTrans (advance_congr (fst_pair _ _)
    (snd_pair _ _).fstE (.eqRefl _))

theorem valid_congr {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) (hs : Γ ⊢[PRAAx] valid s) :
    Γ ⊢[PRAAx] valid t :=
  .andI (le_congr (.eqRefl _) (congrSnd h) (.andE₁ hs))
    (le_congr (congrFst h) (congrSnd h) (.andE₂ hs))

/-- Arbitrary internal iteration preserves denominator positivity and range. -/
theorem orbit_valid (N A B seed : PTm n) (hA : Γ ⊢[PRAAx] le A (num 4*B))
    (hB : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] valid seed) :
    Γ ⊢[PRAAx] valid (orbit N A B seed) := by
  have all : Γ ⊢[PRAAx] .all (valid (orbit (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift seed))) := by
    ipra_qfind (valid_QF _) [subst_valid, subst_orbit]
    · exact valid_congr (orbit_zero _ _ _).eqSymm hs
    · have a : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (num 4*Syn.shift B) := by
        simpa only [Fm.shift, subst_le, PTm.subst_mul, PTm.subst_num, Syn.shift] using hA.shift
      have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
        simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hB.shift
      exact valid_congr (orbit_succ _ _ _ _).eqSymm (advance_valid a.wk b.wk Prf.hyp0)
  ipra_simpa_inst [subst_valid, subst_orbit] using Prf.allE N all

/-- A denominator-cleared rational discrepancy budget. -/
def budget (s t T R : PTm n) : Fm PTm n :=
  le (T*zabs (difference s t)) (R*sndT s*sndT t)

@[simp] theorem subst_budget {m : ℕ} (σ : Fin n → PTm m) (s t T R : PTm n) :
    (budget s t T R).subst σ = budget (Syn.subst σ s) (Syn.subst σ t)
      (Syn.subst σ T) (Syn.subst σ R) := by
  simp only [budget, subst_le, PTm.subst_mul, subst_zabs, subst_difference, subst_sndT]

theorem budget_QF (s t T R : PTm n) : (budget s t T R).QF := le_QF _ _

theorem difference_congr {s s' t t' : PTm n} (hs : Γ ⊢[PRAAx] s ≐ s')
    (ht : Γ ⊢[PRAAx] t ≐ t') :
    Γ ⊢[PRAAx] zabs (difference s t) ≐ zabs (difference s' t') :=
  congrAdd
    (congrMonus (congrMul (congrFst hs) (congrSnd ht)) (congrMul (congrFst ht) (congrSnd hs)))
    (congrMonus (congrMul (congrFst ht) (congrSnd hs)) (congrMul (congrFst hs) (congrSnd ht)))

theorem budget_congr {s s' t t' T T' R R' : PTm n}
    (hs : Γ ⊢[PRAAx] s ≐ s') (ht : Γ ⊢[PRAAx] t ≐ t')
    (hT : Γ ⊢[PRAAx] T ≐ T') (hR : Γ ⊢[PRAAx] R ≐ R')
    (h : Γ ⊢[PRAAx] budget s t T R) : Γ ⊢[PRAAx] budget s' t' T' R' :=
  le_congr (congrMul hT (difference_congr hs ht))
    (congrMul (congrMul hR (congrSnd hs)) (congrSnd ht)) h

/-- One exact logistic update multiplies a rational error bound by four. -/
theorem budget_step {A B s t T R : PTm n} (hA : Γ ⊢[PRAAx] le A (num 4*B))
    (hs : Γ ⊢[PRAAx] le (fstT s) (sndT s)) (ht : Γ ⊢[PRAAx] le (fstT t) (sndT t))
    (h : Γ ⊢[PRAAx] budget s t T R) :
    Γ ⊢[PRAAx] budget (advance A B s) (advance A B t) T (num 4*R) := by
  have first := le_mul_mono (le_refl T) (advance_lipschitz hA hs ht)
  have second := le_mul_mono (le_refl (num 4*B*B*sndT s*sndT t)) h
  exact le_trans first (le_congr (by unfold difference; ipra_ring)
    ((by ipra_ring : Γ ⊢[PRAAx]
      num 4*B*B*sndT s*sndT t*(R*sndT s*sndT t) ≐
        (num 4*R)*(B*sndT s*sndT s)*(B*sndT t*sndT t)).eqTrans
      (congrMul (congrMul (.eqRefl _) (advance_den _ _ _).eqSymm) (advance_den _ _ _).eqSymm)) second)

/-- Amplification incurred by `N` logistic steps, written dyadically. -/
def growth (N : PTm n) : PTm n := pw two (N+N)

ipra_subst growth

theorem growth_zero : Γ ⊢[PRAAx] growth (zero : PTm n) ≐ one :=
  (congrAp2 powF (add_zero zero) (.eqRefl _)).eqTrans (pw_zero _)

theorem growth_succ (N : PTm n) : Γ ⊢[PRAAx] growth (succ N) ≐ num 4*growth N := by
  have shift : Γ ⊢[PRAAx] succ N+succ N ≐ succ (succ (N+N)) := by ipra_ring
  exact (congrAp2 powF shift (.eqRefl _)).eqTrans
    ((pw_succ two _).eqTrans ((congrMul (pw_succ two _) (.eqRefl _)).eqTrans (by unfold growth; ipra_ring)))

theorem orbit_budget (N A B s t T R : PTm n)
    (hA : Γ ⊢[PRAAx] le A (num 4*B)) (hB : Γ ⊢[PRAAx] le one B)
    (hs : Γ ⊢[PRAAx] valid s) (ht : Γ ⊢[PRAAx] valid t)
    (h : Γ ⊢[PRAAx] budget s t T R) :
    Γ ⊢[PRAAx] budget (orbit N A B s) (orbit N A B t) T (growth N*R) := by
  have all : Γ ⊢[PRAAx] .all (budget
      (orbit (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift s))
      (orbit (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift t))
      (Syn.shift T) (growth (var 0)*Syn.shift R)) := by
    ipra_qfind (budget_QF _ _ _ _) [subst_budget, subst_orbit, subst_growth]
    · exact budget_congr (orbit_zero _ _ _).eqSymm (orbit_zero _ _ _).eqSymm (.eqRefl _)
        ((congrMul growth_zero (.eqRefl _)).eqTrans (one_mul _)).eqSymm h
    · have a : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (num 4*Syn.shift B) := by
        simpa only [Fm.shift, subst_le, PTm.subst_mul, PTm.subst_num, Syn.shift] using hA.shift
      have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
        simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hB.shift
      have s0 : Γ.map Fm.shift ⊢[PRAAx] valid (Syn.shift s) := by
        simpa only [Fm.shift, subst_valid, Syn.shift] using hs.shift
      have t0 : Γ.map Fm.shift ⊢[PRAAx] valid (Syn.shift t) := by
        simpa only [Fm.shift, subst_valid, Syn.shift] using ht.shift
      exact budget_congr (orbit_succ _ _ _ _).eqSymm (orbit_succ _ _ _ _).eqSymm (.eqRefl _)
        ((by ipra_ring : (_ :: Γ.map Fm.shift) ⊢[PRAAx]
          num 4*(growth (var 0)*Syn.shift R) ≐ (num 4*growth (var 0))*Syn.shift R).eqTrans
            (congrMul (growth_succ _).eqSymm (.eqRefl _)))
        (budget_step a.wk (Prf.andE₂ (orbit_valid _ _ _ _ a b s0)).wk
          (Prf.andE₂ (orbit_valid _ _ _ _ a b t0)).wk Prf.hyp0)
  ipra_simpa_inst [subst_budget, subst_orbit, subst_growth, PTm.subst_mul] using Prf.allE N all

/-- Fixed primitive recursive presentation of a signed rational input family. -/
structure Input where
  positive : PR 2
  negative : PR 2
  denominator : PR 2

def inputDifference (U : Input) (i j x : PTm n) : ZT n :=
  ⟨ap2 U.positive i x*ap2 U.denominator j x+ap2 U.negative j x*ap2 U.denominator i x,
   ap2 U.positive j x*ap2 U.denominator i x+ap2 U.negative i x*ap2 U.denominator j x⟩

def inputBudget (U : Input) (i j x : PTm n) : Fm PTm n :=
  le (pw two i*pw two j*zabs (inputDifference U i j x))
    ((pw two i+pw two j)*ap2 U.denominator i x*ap2 U.denominator j x)

ipra_subst inputDifference [ZT.subst, PTm.subst_add, PTm.subst_mul, subst_ap2]

@[simp] theorem subst_inputBudget {m : ℕ} (σ : Fin n → PTm m) (U : Input) (i j x : PTm n) :
    (inputBudget U i j x).subst σ =
      inputBudget U (Syn.subst σ i) (Syn.subst σ j) (Syn.subst σ x) := by
  simp only [inputBudget, subst_le, PTm.subst_mul]
  rw [subst_zabs, subst_inputDifference]
  simp only [PTm.subst_add, subst_ap2, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]

/-- Literal finite input observation, including positivity of each used denominator. -/
def observation (U : Input) (H x : PTm n) : Fm PTm n :=
  (.all (le (var 0) (Syn.shift H) ⟶ le one (ap2 U.denominator (var 0) (Syn.shift x)))) ⋏
  (.all (.all (le (var 1) (Syn.shift (Syn.shift H)) ⟶
    le (var 0) (Syn.shift (Syn.shift H)) ⟶
    inputBudget U (var 1) (var 0) (Syn.shift (Syn.shift x)))))

ipra_subst observation [Fm.subst_and, Fm.subst_all, Fm.subst_imp, subst_le, subst_inputBudget, subst_ap2,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Syn.up_zero, Syn.up_one, Syn.up_succ,
    Syn.subst_shift, Syn.shift_subst, Syn.shift_var, Fin.succ_zero_eq_one]

theorem observation_den (U : Input) {H x : PTm n} (h : Γ ⊢[PRAAx] observation U H x)
    (i : PTm n) (hi : Γ ⊢[PRAAx] le i H) : Γ ⊢[PRAAx] le one (ap2 U.denominator i x) := by
  have contract : Γ ⊢[PRAAx] le i H ⟶ le one (ap2 U.denominator i x) := by
    simpa only [observation, Fm.subst_imp, subst_le, subst_ap2, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
      Prf.allE i (.andE₁ h)
  exact Prf.impE contract hi

theorem observation_pair (U : Input) {H x : PTm n} (h : Γ ⊢[PRAAx] observation U H x)
    (i j : PTm n) (hi : Γ ⊢[PRAAx] le i H) (hj : Γ ⊢[PRAAx] le j H) :
    Γ ⊢[PRAAx] inputBudget U i j x := by
  have contract : Γ ⊢[PRAAx] le i H ⟶ le j H ⟶ inputBudget U i j x := by
    simpa only [observation, Fm.subst_all, Fm.subst_imp, subst_le, subst_inputBudget,
      Syn.subst_var, Syn.inst_zero, Syn.inst_one, Syn.inst_succ, Syn.up_zero, Syn.up_succ,
      Syn.subst_inst_shift, Syn.subst_shift, Syn.shift_subst, Syn.subst_subst,
      Syn.up_one, Syn.subst_id] using
      Prf.allE j (Prf.allE i (.andE₂ h))
  exact Prf.impE (Prf.impE contract hi) hj

/-- The actual clipped input rational; its denominator is retained exactly. -/
def sample (U : Input) (k x : PTm n) : PTm n :=
  pairT (clip (ap2 U.positive k x) (ap2 U.negative k x) (ap2 U.denominator k x))
    (ap2 U.denominator k x)

ipra_subst sample

theorem sample_num (U : Input) (k x : PTm n) : Γ ⊢[PRAAx] fstT (sample U k x) ≐
    clip (ap2 U.positive k x) (ap2 U.negative k x) (ap2 U.denominator k x) := fst_pair _ _
theorem sample_den (U : Input) (k x : PTm n) : Γ ⊢[PRAAx] sndT (sample U k x) ≐
    ap2 U.denominator k x := snd_pair _ _

theorem sample_valid (U : Input) (k x : PTm n)
    (hd : Γ ⊢[PRAAx] le one (ap2 U.denominator k x)) :
    Γ ⊢[PRAAx] valid (sample U k x) :=
  .andI (le_congr (.eqRefl _) (sample_den U k x).eqSymm hd)
    (le_congr (sample_num U k x).eqSymm (sample_den U k x).eqSymm (clip_range _ _ _))

theorem sample_nonexpansive (U : Input) (i j x : PTm n) :
    Γ ⊢[PRAAx] le (zabs (difference (sample U i x) (sample U j x)))
      (zabs (inputDifference U i j x)) := by
  have E : Γ ⊢[PRAAx] zabs (difference (sample U i x) (sample U j x)) ≐
      ad (clip (ap2 U.positive i x) (ap2 U.negative i x) (ap2 U.denominator i x)*ap2 U.denominator j x)
        (clip (ap2 U.positive j x) (ap2 U.negative j x) (ap2 U.denominator j x)*ap2 U.denominator i x) :=
    congrAdd
      (congrMonus (congrMul (sample_num U i x) (sample_den U j x))
        (congrMul (sample_num U j x) (sample_den U i x)))
      (congrMonus (congrMul (sample_num U j x) (sample_den U i x))
        (congrMul (sample_num U i x) (sample_den U j x)))
  exact le_congr E.eqSymm (.eqRefl _) (clip_rational _ _ _ _ _ _)

theorem sample_budget (U : Input) (i j x : PTm n) (h : Γ ⊢[PRAAx] inputBudget U i j x) :
    Γ ⊢[PRAAx] budget (sample U i x) (sample U j x) (pw two i*pw two j) (pw two i+pw two j) :=
  le_trans (le_mul_mono (le_refl _) (sample_nonexpansive U i j x))
    (le_congr (.eqRefl _) (congrMul (congrMul (.eqRefl _) (sample_den U i x).eqSymm)
      (sample_den U j x).eqSymm) h)

/-- The finite loop in the source: one input evaluation at `k+2N`, then `N` exact steps. -/
def value (U : Input) (N k A B x : PTm n) : PTm n :=
  orbit N A B (sample U (k+(N+N)) x)

ipra_subst value

def valueF (U : Input) : PR 5 := PTm.toPR (value U (var 0) (var 1) (var 2) (var 3) (var 4))

theorem value_at (U : Input) (N k A B x : PTm n) :
    Γ ⊢[PRAAx] app (valueF U) ![N,k,A,B,x] ≐ value U N k A B x := by
  have h := toPR_eq (Γ := Γ) (value U (var 0) (var 1) (var 2) (var 3) (var 4)) ![N,k,A,B,x]
  simpa only [valueF, subst_value, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] using h

theorem sample_congr_index (U : Input) {i j x : PTm n} (h : Γ ⊢[PRAAx] i ≐ j) :
    Γ ⊢[PRAAx] sample U i x ≐ sample U j x :=
  congrPairT (congrMonus (congrAp2 U.denominator h (.eqRefl _))
    (congrMonus (congrAp2 U.denominator h (.eqRefl _))
      (congrMonus (congrAp2 U.positive h (.eqRefl _)) (congrAp2 U.negative h (.eqRefl _)))))
    (congrAp2 U.denominator h (.eqRefl _))

theorem orbit_congr_seed (N A B : PTm n) {s t : PTm n} (h : Γ ⊢[PRAAx] s ≐ t) :
    Γ ⊢[PRAAx] orbit N A B s ≐ orbit N A B t :=
  congrAp2 orbitF (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) h))

/-- Actual parameter-changing recursion identity, without any name-validity premise. -/
theorem value_succ (U : Input) (N k A B x : PTm n) :
    Γ ⊢[PRAAx] value U (succ N) k A B x ≐ advance A B (value U N (succ (succ k)) A B x) :=
  (orbit_succ _ _ _ _).eqTrans (advance_congr (.eqRefl _) (.eqRefl _)
    (orbit_congr_seed N A B (sample_congr_index U (by ipra_ring))))

theorem value_zero (U : Input) (k A B x : PTm n) :
    Γ ⊢[PRAAx] value U zero k A B x ≐ sample U k x :=
  (orbit_zero _ _ _).eqTrans (sample_congr_index U (by ipra_ring))

/-- The regular-name comparison `|s-t|≤2⁻ᵏ+2⁻ˡ`. -/
def regular (s t k l : PTm n) : Fm PTm n := budget s t (pw two k*pw two l) (pw two k+pw two l)

ipra_subst regular

theorem growth_positive (N : PTm n) : Γ ⊢[PRAAx] le one (growth N) :=
  le_trans (le_of_eq_add (d := N+N) (by ipra_ring))
    (RationalClosure.succ_le_two_pow (N+N))

theorem power_shift (k N : PTm n) :
    Γ ⊢[PRAAx] pw two (k+(N+N)) ≐ pw two k*growth N := pw_add _ _ _

private alias cancel_positive := Common.mul_cancel_le

/-- The exact precision shift cancels all amplification, without a limit argument. -/
theorem absorb_growth (s t N k l : PTm n)
    (h : Γ ⊢[PRAAx] budget s t
      (pw two (k+(N+N))*pw two (l+(N+N)))
      (growth N*(pw two (k+(N+N))+pw two (l+(N+N))))) :
    Γ ⊢[PRAAx] regular s t k l := by
  have Ek := natEq (power_shift (Γ := Γ) k N)
  have El := natEq (power_shift (Γ := Γ) l N)
  simp only [Q.mk_mul, map_mul] at Ek El
  have scaled : Γ ⊢[PRAAx] le
      ((growth N*growth N)*(pw two k*pw two l*zabs (difference s t)))
      ((growth N*growth N)*((pw two k+pw two l)*sndT s*sndT t)) := by
    apply le_congr (h := h)
    · apply deriveNat; ipra_simps; rw [Ek, El]; ring
    · apply deriveNat; ipra_simps; rw [Ek, El]; ring
  exact cancel_positive
    (le_congr (one_mul one) (.eqRefl _) (le_mul_mono (growth_positive N) (growth_positive N))) scaled

/-- Finite input observation alone supplies every range and positivity fact used by the loop. -/
theorem value_valid (U : Input) (N K k A B x : PTm n)
    (hA : Γ ⊢[PRAAx] le A (num 4*B)) (hB : Γ ⊢[PRAAx] le one B)
    (ho : Γ ⊢[PRAAx] observation U (K+(N+N)) x) (hk : Γ ⊢[PRAAx] le k K) :
    Γ ⊢[PRAAx] valid (value U N k A B x) :=
  orbit_valid N A B _ hA hB (sample_valid U _ x
    (observation_den U ho _ (add_le_add₂ hk (le_refl (N+N)))))

/-- Finite coherence uses exactly the two input indices bounded by `K+2N`. -/
theorem value_regular (U : Input) (N K k l A B x : PTm n)
    (hA : Γ ⊢[PRAAx] le A (num 4*B)) (hB : Γ ⊢[PRAAx] le one B)
    (ho : Γ ⊢[PRAAx] observation U (K+(N+N)) x)
    (hk : Γ ⊢[PRAAx] le k K) (hl : Γ ⊢[PRAAx] le l K) :
    Γ ⊢[PRAAx] regular (value U N k A B x) (value U N l A B x) k l := by
  have ik := add_le_add₂ hk (le_refl (N+N))
  have il := add_le_add₂ hl (le_refl (N+N))
  exact absorb_growth _ _ N k l (orbit_budget N A B _ _ _ _ hA hB
    (sample_valid U _ x (observation_den U ho _ ik))
    (sample_valid U _ x (observation_den U ho _ il))
    (sample_budget U _ _ x (observation_pair U ho _ _ ik il)))

/-- The full bounded source conclusion, including output-denominator positivity. -/
def finiteValidity (U : Input) (N K A B x : PTm n) : Fm PTm n :=
  (.all (le (var 0) (Syn.shift K) ⟶
    valid (value U (Syn.shift N) (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift x)))) ⋏
  (.all (.all (le (var 1) (Syn.shift (Syn.shift K)) ⟶
    le (var 0) (Syn.shift (Syn.shift K)) ⟶
    regular
      (value U (Syn.shift (Syn.shift N)) (var 1) (Syn.shift (Syn.shift A))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift x)))
      (value U (Syn.shift (Syn.shift N)) (var 0) (Syn.shift (Syn.shift A))
        (Syn.shift (Syn.shift B)) (Syn.shift (Syn.shift x))) (var 1) (var 0))))

/-- Source `thm:nonlinear-name-validity`, under an arbitrary fixed object context. -/
theorem nonlinear_name_validity (U : Input) (N K A B x : PTm n)
    (hA : Γ ⊢[PRAAx] le A (num 4*B)) (hB : Γ ⊢[PRAAx] le one B)
    (ho : Γ ⊢[PRAAx] observation U (K+(N+N)) x) :
    Γ ⊢[PRAAx] finiteValidity U N K A B x := by
  apply Prf.andI
  · refine .allI (.impI ?_)
    have a : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (num 4*Syn.shift B) := by
      simpa only [Fm.shift, subst_le, PTm.subst_mul, PTm.subst_num, Syn.shift] using hA.shift
    have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
      simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hB.shift
    have o : Γ.map Fm.shift ⊢[PRAAx]
        observation U (Syn.shift K+(Syn.shift N+Syn.shift N)) (Syn.shift x) := by
      simpa only [Fm.shift, subst_observation, PTm.subst_add, Syn.shift] using ho.shift
    exact value_valid U _ _ _ _ _ _ a.wk b.wk o.wk Prf.hyp0
  · refine .allI (.allI (.impI (.impI ?_)))
    have a : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
        le (Syn.shift (Syn.shift A)) (num 4*Syn.shift (Syn.shift B)) := by
      simpa only [Fm.shift, subst_le, PTm.subst_mul, PTm.subst_num, Syn.shift] using hA.shift.shift
    have b : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift B)) := by
      simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hB.shift.shift
    have o : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx]
        observation U (Syn.shift (Syn.shift K)+(Syn.shift (Syn.shift N)+Syn.shift (Syn.shift N)))
          (Syn.shift (Syn.shift x)) := by
      simpa only [Fm.shift, subst_observation, PTm.subst_add, Syn.shift] using ho.shift.shift
    exact value_regular U _ _ _ _ _ _ _ a.wk.wk b.wk.wk o.wk.wk Prf.hyp1 Prf.hyp0

/-- Variables are stage, horizon, numerator/denominator of `a`, and persistent input data. -/
def validityFormula (U : Input) : Fm PTm 5 :=
  le (var 2) (num 4*var 3) ⟶ le one (var 3) ⟶
    observation U (var 1+(var 0+var 0)) (var 4) ⟶
    finiteValidity U (var 0) (var 1) (var 2) (var 3) (var 4)

theorem nonlinear_name_validity_closed (U : Input) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 (validityFormula U) :=
  closeUniv 5 (.impI (.impI (.impI
    (nonlinear_name_validity U _ _ _ _ _ Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

/-- The actual parameter-changing identity, universally closed at arbitrary internal terms. -/
theorem parameter_shift_closed (U : Input) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (value U (succ (var 0)) (var 1) (var 2) (var 3) (var 4) ≐
        advance (var 2) (var 3) (value U (var 0) (succ (succ (var 1))) (var 2) (var 3) (var 4))) :=
  closeUniv 5 (value_succ U _ _ _ _ _)

/-- Global regularity is used only by instantiating a finite input observation. -/
def globalInput (U : Input) (x : PTm n) : Fm PTm n :=
  .all (observation U (var 0) (Syn.shift x))

ipra_subst globalInput [Fm.subst_all, subst_observation, Syn.subst_var, Syn.up_zero, Syn.up_succ, Syn.subst_shift,
    Syn.shift_subst]

theorem globalInput_at (U : Input) {x : PTm n} (h : Γ ⊢[PRAAx] globalInput U x) (H : PTm n) :
    Γ ⊢[PRAAx] observation U H x := by
  ipra_simpa_inst [globalInput, subst_observation] using Prf.allE H h

/-- The source's global corollary still proceeds through the finite theorem. -/
theorem globally_regular_output (U : Input) (N A B x : PTm n)
    (hA : Γ ⊢[PRAAx] le A (num 4*B)) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] globalInput U x) :
    Γ ⊢[PRAAx] .all (finiteValidity U (Syn.shift N) (var 0) (Syn.shift A) (Syn.shift B) (Syn.shift x)) := by
  refine .allI ?_
  have a : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift A) (num 4*Syn.shift B) := by
    simpa only [Fm.shift, subst_le, PTm.subst_mul, PTm.subst_num, Syn.shift] using hA.shift
  have b : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift B) := by
    simpa only [Fm.shift, subst_le, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.shift] using hB.shift
  have u : Γ.map Fm.shift ⊢[PRAAx] globalInput U (Syn.shift x) := by
    simpa only [Fm.shift, subst_globalInput, Syn.shift] using hu.shift
  exact nonlinear_name_validity U _ _ _ _ _ a b (globalInput_at U u _)

/-- Variables are stage, rational-parameter numerator/denominator, and persistent data. -/
theorem globally_regular_output_closed (U : Input) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (le (var 1) (num 4*var 2) ⟶ le one (var 2) ⟶ globalInput U (var 3) ⟶
        .all (finiteValidity U (var 1) (var 0) (var 2) (var 3) (var 4))) :=
  closeUniv 4 (.impI (.impI (.impI
    (globally_regular_output U (var 0) (var 1) (var 2) (var 3) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))

#print axioms positive_contraction
#print axioms clip_below
#print axioms clip_middle
#print axioms clip_above
#print axioms clip_scale
#print axioms clip_rational
#print axioms quarter_bound
#print axioms advance_lipschitz
#print axioms orbit_valid
#print axioms orbit_budget
#print axioms value_at
#print axioms parameter_shift_closed
#print axioms absorb_growth
#print axioms nonlinear_name_validity_closed
#print axioms globally_regular_output_closed

end LeanProofs.IPRA.Analysis.LogisticName
