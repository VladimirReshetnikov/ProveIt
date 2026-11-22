import IPRADerivations.Foundations.FiniteAvoidance
import IPRADerivations.Foundations.FilteredEnumeration
import IPRADerivations.Foundations.VandermondeDeterminant

/-!
# A generic height separates finitely many points (`platonic_solids_ipra`, `lem:height`)

Packet: `geometry/platonic_solids_ipra`, `02_counting.tex`, lemma `lem:height`: "For `V`
distinct exactly represented points in three dimensions one can construct a linear functional
taking distinct values on all the points by trying at most `2·C(V, 2) + 1` integer candidates."
Proof: "Try `h_t(x, y, z) = x + ty + t²z` ... For any distinct pair of points, equality of
their heights is a nonzero polynomial equation of degree at most two in `t`. Such a polynomial
has at most two distinct roots, by division by linear factors. There are at most `2·C(V, 2)`
forbidden values. Testing the displayed list therefore returns a valid candidate."

`Foundations/FiniteAvoidance` has the counting. This module derives the bound of two forbidden
candidates per pair, for points with natural coordinates:

* `three_kept`: if a decidable subset of `[T]` has more than two elements, its first three
  elements (`Foundations/FilteredEnumeration.sel`) are pairwise distinct members;
* `three_roots_nat`: if `x + t y + t² z = x' + t y' + t² z'` at three pairwise distinct `t`,
  then `x = x'`, `y = y'`, `z = z'` (`Foundations/VandermondeDeterminant.root_bound`);
* `kB`, `pair_count`: for two distinct points the number of `t < T` with equal heights is at
  most two.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Geometry.GenericHeight

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FilteredEnumeration (rank sel sel_spec)
open LeanProofs.IPRA.Foundations.VandermondeDeterminant (root_bound)
open LeanProofs.IPRA.Foundations.EliminationRoot (vpow toZ_vpow)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## More than two members give three distinct members -/

theorem zero_ne_succ (a : PTm n) : Γ ⊢[PRAAx] neg ((zero : PTm n) ≐ succ a) :=
  .impI (succ_ne_zero' _ (Prf.eqSymm Prf.hyp0))

theorem one_ne_two : Γ ⊢[PRAAx] neg ((one : PTm n) ≐ two) :=
  .impI (succ_ne_zero' _ (a := zero)
    ((pred_succ _).eqSymm.eqTrans ((congrPred (Prf.eqSymm Prf.hyp0)).eqTrans (pred_succ _))))

section Count

variable (K : PTm 2)

theorem sel_distinct {P r r' p : PTm n} (hr : Γ ⊢[PRAAx] lt r (rank K P p))
    (hr' : Γ ⊢[PRAAx] lt r' (rank K P p)) (hne : Γ ⊢[PRAAx] neg (r ≐ r')) :
    Γ ⊢[PRAAx] neg (sel K r P p ≐ sel K r' P p) :=
  .impI (.impE hne.wk ((Prf.andE₂ (Prf.andE₂ (sel_spec K hr))).wk.eqSymm.eqTrans
    ((congrAp2 _ Prf.hyp0 (.eqRefl _)).eqTrans (Prf.andE₂ (Prf.andE₂ (sel_spec K hr'))).wk)))

/-- If more than two elements below `T` are retained, the first three are retained and
pairwise distinct. -/
theorem three_kept {T p : PTm n} (h : Γ ⊢[PRAAx] lt two (rank K T p)) :
    Γ ⊢[PRAAx] (neg (inst2 K (sel K zero T p) p ≐ zero) ⋏
        (neg (inst2 K (sel K one T p) p ≐ zero) ⋏ neg (inst2 K (sel K two T p) p ≐ zero))) ⋏
      (neg (sel K zero T p ≐ sel K one T p) ⋏
        (neg (sel K zero T p ≐ sel K two T p) ⋏ neg (sel K one T p ≐ sel K two T p))) := by
  have h1 : Γ ⊢[PRAAx] lt one (rank K T p) := le_trans (le_succ_self _) h
  have h0 : Γ ⊢[PRAAx] lt zero (rank K T p) := le_trans (le_succ_self _) h1
  exact .andI
    (.andI (Prf.andE₁ (Prf.andE₂ (sel_spec K h0)))
      (.andI (Prf.andE₁ (Prf.andE₂ (sel_spec K h1))) (Prf.andE₁ (Prf.andE₂ (sel_spec K h)))))
    (.andI (sel_distinct K h0 h1 (zero_ne_succ _))
      (.andI (sel_distinct K h0 h (zero_ne_succ _)) (sel_distinct K h1 h one_ne_two)))

end Count

/-! ## Three roots -/

/-- The height `x + t y + t² z`. -/
abbrev hgt (t x y z : PTm n) : PTm n := x + t * y + t * t * z

theorem nat_ne {a b : PTm n} (h : Γ ⊢[PRAAx] neg (a ≐ b)) :
    Γ ⊢[PRAAx] neg (ZT.eq (ZT.ofNat b - ZT.ofNat a) (ZT.natLit 0)) := by
  refine .impI (.impE h.wk (deriveNat ?_))
  have e := ZT.toZ_eq (Prf.hyp0 (Γ := Γ)
    (φ := ZT.eq (ZT.ofNat b - ZT.ofNat a) (ZT.natLit 0)))
  simp only [ZT.toZ_sub, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero] at e
  linear_combination -e

theorem root_eq {t x y z x' y' z' : PTm n} (h : Γ ⊢[PRAAx] hgt t x y z ≐ hgt t x' y' z') :
    Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun l : Fin 3 => vpow (ZT.ofNat t) l *
      (![ZT.ofNat x - ZT.ofNat x', ZT.ofNat y - ZT.ofNat y', ZT.ofNat z - ZT.ofNat z'] :
        Vec 3 n) l) (ZT.natLit 0) := by
  refine ZT.derive ?_
  have e := natEq h
  simp only [ZT.toZ_sumFin, Fin.sum_univ_three, ZT.toZ_mul, toZ_vpow, ZT.toZ_sub,
    ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Fin.val_zero, Fin.val_one,
    Fin.val_two]
  ipra_simps
  linear_combination e

/-- Equal heights at three pairwise distinct `t` force equal points. -/
theorem three_roots_nat {x y z x' y' z' t₀ t₁ t₂ : PTm n}
    (h₀ : Γ ⊢[PRAAx] hgt t₀ x y z ≐ hgt t₀ x' y' z')
    (h₁ : Γ ⊢[PRAAx] hgt t₁ x y z ≐ hgt t₁ x' y' z')
    (h₂ : Γ ⊢[PRAAx] hgt t₂ x y z ≐ hgt t₂ x' y' z')
    (d₀₁ : Γ ⊢[PRAAx] neg (t₀ ≐ t₁)) (d₀₂ : Γ ⊢[PRAAx] neg (t₀ ≐ t₂))
    (d₁₂ : Γ ⊢[PRAAx] neg (t₁ ≐ t₂)) :
    Γ ⊢[PRAAx] (x ≐ x') ⋏ ((y ≐ y') ⋏ (z ≐ z')) := by
  have hv : ∀ i j : Fin 3, i < j → (Γ ⊢[PRAAx] neg (ZT.eq
      ((![ZT.ofNat t₀, ZT.ofNat t₁, ZT.ofNat t₂] : Vec 3 n) j -
        (![ZT.ofNat t₀, ZT.ofNat t₁, ZT.ofNat t₂] : Vec 3 n) i) (ZT.natLit 0))) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> first
      | exact absurd hij (by decide)
      | exact nat_ne d₀₁
      | exact nat_ne d₀₂
      | exact nat_ne d₁₂
  have hz : ∀ i : Fin 3, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun l : Fin 3 =>
      vpow ((![ZT.ofNat t₀, ZT.ofNat t₁, ZT.ofNat t₂] : Vec 3 n) i) l *
        (![ZT.ofNat x - ZT.ofNat x', ZT.ofNat y - ZT.ofNat y', ZT.ofNat z - ZT.ofNat z'] :
          Vec 3 n) l) (ZT.natLit 0) := by
    intro i
    fin_cases i
    · exact root_eq h₀
    · exact root_eq h₁
    · exact root_eq h₂
  have c0 := ZT.toZ_eq (root_bound hv hz 0)
  have c1 := ZT.toZ_eq (root_bound hv hz 1)
  have c2 := ZT.toZ_eq (root_bound hv hz 2)
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, ZT.toZ_sub, ZT.toZ_ofNat, ZT.toZ_natLit, Nat.cast_zero] at c0 c1 c2
  exact .andI (deriveNat (by linear_combination c0))
    (.andI (deriveNat (by linear_combination c1)) (deriveNat (by linear_combination c2)))

/-! ## At most two forbidden candidates per pair -/

/-- The six coordinates of a pair of points, as one code. -/
abbrev pd (x y z x' y' z' : PTm n) : PTm n :=
  pairT (pairT x (pairT y z)) (pairT x' (pairT y' z'))

/-- The bit "the two points of the pair have equal heights at `t`", over `0 = t`,
`1 = pd x y z x' y' z'`. -/
abbrev kB : PTm 2 :=
  eqb (hgt (var 0) (fstT (fstT (var 1))) (fstT (sndT (fstT (var 1)))) (sndT (sndT (fstT (var 1)))))
    (hgt (var 0) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))))

theorem congrHgt {t x x₁ y y₁ z z₁ : PTm n} (hx : Γ ⊢[PRAAx] x ≐ x₁) (hy : Γ ⊢[PRAAx] y ≐ y₁)
    (hz : Γ ⊢[PRAAx] z ≐ z₁) : Γ ⊢[PRAAx] hgt t x y z ≐ hgt t x₁ y₁ z₁ :=
  congrAdd (congrAdd hx (congrMul (.eqRefl _) hy)) (congrMul (.eqRefl _) hz)

theorem k_at (t x y z x' y' z' : PTm n) :
    Γ ⊢[PRAAx] inst2 kB t (pd x y z x' y' z') ≐ eqb (hgt t x y z) (hgt t x' y' z') := by
  have h : inst2 kB t (pd x y z x' y' z') =
      eqb (hgt t (fstT (fstT (pd x y z x' y' z'))) (fstT (sndT (fstT (pd x y z x' y' z'))))
          (sndT (sndT (fstT (pd x y z x' y' z')))))
        (hgt t (fstT (sndT (pd x y z x' y' z'))) (fstT (sndT (sndT (pd x y z x' y' z'))))
          (sndT (sndT (sndT (pd x y z x' y' z'))))) := by simp [inst2]
  rw [h]
  have a : Γ ⊢[PRAAx] fstT (pd x y z x' y' z') ≐ pairT x (pairT y z) := fst_pair _ _
  have b : Γ ⊢[PRAAx] sndT (pd x y z x' y' z') ≐ pairT x' (pairT y' z') := snd_pair _ _
  exact congrEqb
    (congrHgt ((congrFst a).eqTrans (fst_pair _ _))
      ((congrFst ((congrSnd a).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))
      ((congrSnd ((congrSnd a).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)))
    (congrHgt ((congrFst b).eqTrans (fst_pair _ _))
      ((congrFst ((congrSnd b).eqTrans (snd_pair _ _))).eqTrans (fst_pair _ _))
      ((congrSnd ((congrSnd b).eqTrans (snd_pair _ _))).eqTrans (snd_pair _ _)))

theorem k_root {t x y z x' y' z' : PTm n}
    (h : Γ ⊢[PRAAx] neg (inst2 kB t (pd x y z x' y' z') ≐ zero)) :
    Γ ⊢[PRAAx] hgt t x y z ≐ hgt t x' y' z' :=
  eq_of_eqb_ne (.impI (.impE h.wk ((k_at t x y z x' y' z').eqTrans Prf.hyp0)))

/-- Two distinct points have equal heights for at most two candidates `t < T`. -/
theorem pair_count {T x y z x' y' z' : PTm n}
    (hne : Γ ⊢[PRAAx] neg ((x ≐ x') ⋏ ((y ≐ y') ⋏ (z ≐ z')))) :
    Γ ⊢[PRAAx] le (rank kB T (pd x y z x' y' z')) two := by
  refine .orE (lt_or_le two (rank kB T (pd x y z x' y' z'))) ?_ Prf.hyp0
  have tk := three_kept kB (Prf.hyp0 (Γ := Γ)
    (φ := lt two (rank kB T (pd x y z x' y' z'))))
  exact .botE _ (.impE hne.wk (three_roots_nat
    (k_root (Prf.andE₁ (Prf.andE₁ tk)))
    (k_root (Prf.andE₁ (Prf.andE₂ (Prf.andE₁ tk))))
    (k_root (Prf.andE₂ (Prf.andE₂ (Prf.andE₁ tk))))
    (Prf.andE₁ (Prf.andE₂ tk)) (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ tk)))
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ tk)))))

/-! ## The generic height -/

section Height

open LeanProofs.IPRA.Foundations.FiniteAvoidance (aB inst3_aB gB colCount exists_good good
  good_lt good_at height_candidate)
open LeanProofs.IPRA.Foundations.BoundedReflection (exB sgB inst2_sgB)
open LeanProofs.IPRA.Signum (sg)

-- The coordinates of the two points of the pair `c`: bodies over `0 = c`, `1 = x`.
variable (X Y Z X' Y' Z' : PTm 2)

/-- The pair data as a body. -/
def pdB : PTm 2 := pd X Y Z X' Y' Z'

theorem pd_at (c x : PTm n) : inst2 (pdB X Y Z X' Y' Z') c x =
    pd (inst2 X c x) (inst2 Y c x) (inst2 Z c x) (inst2 X' c x) (inst2 Y' c x) (inst2 Z' c x) := by
  simp [inst2, pdB]

/-- `bad(t, c, x)`: the pair `c` has equal heights at the candidate `t`. -/
def bad : PTm 3 := Syn.subst ![var 0, Syn.subst ![var 1, var 2] (pdB X Y Z X' Y' Z')] kB

theorem inst3_bad (t c x : PTm n) : inst3 (bad X Y Z X' Y' Z') t c x =
    inst2 kB t (inst2 (pdB X Y Z X' Y' Z') c x) := by
  have h : Syn.subst ![t, c, x] (Syn.subst ![var 1, var 2] (pdB X Y Z X' Y' Z')) =
      inst2 (pdB X Y Z X' Y' Z') c x := by
    simp only [inst2, Syn.subst_subst]
    congr 1
    funext j
    fin_cases j <;> simp
  simp only [inst3, bad, Syn.subst_subst]
  rw [show inst2 kB t (inst2 (pdB X Y Z X' Y' Z') c x) =
    Syn.subst ![t, inst2 (pdB X Y Z X' Y' Z') c x] kB from rfl]
  congr 1
  funext i
  fin_cases i
  · simp
  · simpa using h

theorem col_eq (T c x : PTm n) :
    Γ ⊢[PRAAx] colCount (bad X Y Z X' Y' Z') T c x ≐
      rank kB T (inst2 (pdB X Y Z X' Y' Z') c x) := by
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [Foundations.FiniteAvoidance.shift_pair, inst2_colB, inst2_sgB]
  have e : Γ.map Fm.shift ⊢[PRAAx]
      inst3 (aB (bad X Y Z X' Y' Z')) (var 0) (fstT (pairT (Syn.shift c) (Syn.shift x)))
        (sndT (pairT (Syn.shift c) (Syn.shift x))) ≐
      inst3 (aB (bad X Y Z X' Y' Z')) (var 0) (Syn.shift c) (Syn.shift x) :=
    congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)
  have r : inst3 (aB (bad X Y Z X' Y' Z')) (var 0 : PTm (n + 1)) (Syn.shift c) (Syn.shift x) =
      sg (inst2 kB (var 0) (inst2 (pdB X Y Z X' Y' Z') (Syn.shift c) (Syn.shift x))) := by
    rw [inst3_aB, inst3_bad]
  rw [r] at e
  have s : Syn.shift (inst2 (pdB X Y Z X' Y' Z') c x) =
      inst2 (pdB X Y Z X' Y' Z') (Syn.shift c) (Syn.shift x) := by simp [Syn.shift]
  rw [s]
  exact e.wk

theorem col_le {T c x : PTm n}
    (hne : Γ ⊢[PRAAx] neg ((inst2 X c x ≐ inst2 X' c x) ⋏
      ((inst2 Y c x ≐ inst2 Y' c x) ⋏ (inst2 Z c x ≐ inst2 Z' c x)))) :
    Γ ⊢[PRAAx] le (colCount (bad X Y Z X' Y' Z') T c x) two := by
  have h := pair_count (T := T) hne
  rw [← pd_at] at h
  exact le_congr (col_eq X Y Z X' Y' Z' T c x).eqSymm (.eqRefl _) h

/-- The pairs `c < P` are pairs of distinct points. -/
abbrev distinctAll (P x : PTm n) : Fm PTm n :=
  Fm.all (lt (var 0) (Syn.shift P) ⟶
    neg ((inst2 X (var 0) (Syn.shift x) ≐ inst2 X' (var 0) (Syn.shift x)) ⋏
      ((inst2 Y (var 0) (Syn.shift x) ≐ inst2 Y' (var 0) (Syn.shift x)) ⋏
        (inst2 Z (var 0) (Syn.shift x) ≐ inst2 Z' (var 0) (Syn.shift x)))))

theorem shift_two : Syn.shift (two : PTm n) = two := by simp [Syn.shift]

/-- `lem:height`: among the candidates `t ≤ 2P` one is forbidden by no pair. -/
theorem height_exists {P x : PTm n} (hd : Γ ⊢[PRAAx] distinctAll X Y Z X' Y' Z' P x) :
    Γ ⊢[PRAAx] exB (gB (bad X Y Z X' Y' Z')) (succ (P * two)) (pairT P x) ≐ one := by
  refine height_candidate (bad X Y Z X' Y' Z') (.allI (.impI ?_))
  rw [shift_two]
  exact col_le X Y Z X' Y' Z' (.impE hd.allOpen.wk Prf.hyp0)

/-- The generic height `t`: the first candidate forbidden by no pair. -/
abbrev tH (P x : PTm n) : PTm n := good (bad X Y Z X' Y' Z') (succ (P * two)) P x

/-- `lem:height`: the candidate is at most `2P`. -/
theorem height_le {P x : PTm n} (hd : Γ ⊢[PRAAx] distinctAll X Y Z X' Y' Z' P x) :
    Γ ⊢[PRAAx] lt (tH X Y Z X' Y' Z' P x) (succ (P * two)) :=
  good_lt _ (height_exists X Y Z X' Y' Z' hd)

/-- `lem:height`: at the generic height the two points of every pair `c < P` have distinct
values `x + t y + t² z`. -/
theorem height_separates {P x c : PTm n} (hd : Γ ⊢[PRAAx] distinctAll X Y Z X' Y' Z' P x)
    (hc : Γ ⊢[PRAAx] lt c P) :
    Γ ⊢[PRAAx] neg (hgt (tH X Y Z X' Y' Z' P x) (inst2 X c x) (inst2 Y c x) (inst2 Z c x) ≐
      hgt (tH X Y Z X' Y' Z' P x) (inst2 X' c x) (inst2 Y' c x) (inst2 Z' c x)) := by
  have z := good_at _ (height_exists X Y Z X' Y' Z' hd) hc
  rw [inst3_bad, pd_at] at z
  refine .impI (Foundations.BoundedReflection.one_ne_zero _ ?_)
  exact ((k_at _ _ _ _ _ _ _).eqTrans (eqb_of_eq Prf.hyp0)).eqSymm.eqTrans z.wk

end Height

end LeanProofs.IPRA.Geometry.GenericHeight
