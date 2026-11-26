import IPRADerivations.Analysis.Optimization.CubeInfimum.RationalCubeInfimumName

/-!
# Finite comparison and uniqueness of the actual cube infimum name

A lower-bound name is below every approximately attained name. The proof
uses an explicit precision computed from the original decoded denominators
and finite gap removal. Approximate points are an actual fixed PR program;
there is no extremizer, subsequence or unbounded choice construction.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCubeInfimumComparison

open_ipra
open RationalCubeGrid (scale)
open RationalCubeMinimum (sample presentedCube coherence continuity)
open RationalCubeInfimumName (data)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

def lowerAt (A : PR 3) (f : PR 2) (x z y p q : PTm n) : Fm PTm n :=
  RationalValueBounds.upper (ap2 f q z) (sample A y p x) (scale q+scale p) (scale q*scale p)
def lowerBound (A : PR 3) (f : PR 2) (d x z : PTm n) : Fm PTm n := .all (.all (.all
  (presentedCube (var 2) (Syn.shift (Syn.shift (Syn.shift d))) ⟶
    lowerAt A f (Syn.shift (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift (Syn.shift z))) (var 2) (var 1) (var 0))))
def cubePoints (b : PR 2) (d y : PTm n) : Fm PTm n := .all (presentedCube (ap2 b (var 0) (Syn.shift y)) (Syn.shift d))
def attainedAt (A : PR 3) (g b : PR 2) (x u y k q p : PTm n) : Fm PTm n :=
  RationalValueBounds.upper (sample A (ap2 b k y) p x) (ap2 g q u)
    ((succ two)*scale q*scale p+((two*two)*scale k)*(scale q+scale p)) (((two*two)*scale k)*scale q*scale p)
def attainment (A : PR 3) (g b : PR 2) (x u y : PTm n) : Fm PTm n := .all (.all (.all
  (attainedAt A g b (Syn.shift (Syn.shift (Syn.shift x))) (Syn.shift (Syn.shift (Syn.shift u)))
    (Syn.shift (Syn.shift (Syn.shift y))) (var 2) (var 1) (var 0))))
def namedAt (f g : PR 2) (z u q t : PTm n) : Fm PTm n :=
  RationalValueBounds.upper (ap2 f q z) (ap2 g t u) (scale q+scale t) (scale q*scale t)
def namedLE (f g : PR 2) (z u : PTm n) : Fm PTm n := .all (.all
  (namedAt f g (Syn.shift (Syn.shift z)) (Syn.shift (Syn.shift u)) (var 1) (var 0)))
def equivalent (f g : PR 2) (z u : PTm n) : Fm PTm n := namedLE f g z u ⋏ namedLE g f u z

ipra_subst lowerAt
ipra_subst lowerBound [Syn.subst_shift, Syn.shift_subst]
ipra_subst cubePoints [Syn.subst_shift, Syn.shift_subst]
ipra_subst attainedAt
ipra_subst attainment [Syn.subst_shift, Syn.shift_subst]
ipra_subst namedAt
ipra_subst namedLE [Syn.subst_shift, Syn.shift_subst]
ipra_subst equivalent

theorem lower_bound_at (A : PR 3) (f : PR 2) (d x z y p q : PTm n) (h : Γ ⊢[PRAAx] lowerBound A f d x z)
    (hy : Γ ⊢[PRAAx] presentedCube y d) : Γ ⊢[PRAAx] lowerAt A f x z y p q := by
  have h' := ((h.allE y).allE p).allE q
  have law : Γ ⊢[PRAAx] presentedCube y d ⟶ lowerAt A f x z y p q := by
    simpa [lowerBound,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using h'
  exact .impE law hy

theorem cube_points_at (b : PR 2) (d y k : PTm n) (h : Γ ⊢[PRAAx] cubePoints b d y) :
    Γ ⊢[PRAAx] presentedCube (ap2 b k y) d := by simpa [cubePoints] using h.allE k

theorem attainment_at (A : PR 3) (g b : PR 2) (x u y k q p : PTm n) (h : Γ ⊢[PRAAx] attainment A g b x u y) :
    Γ ⊢[PRAAx] attainedAt A g b x u y k q p := by
  simpa [attainment,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using ((h.allE k).allE q).allE p

/-- One explicit computed precision removes every auxiliary evaluation error. -/
theorem lower_le_attained_at (A : PR 3) (f g b : PR 2) (d x z u y q t : PTm n)
    (hL : Γ ⊢[PRAAx] lowerBound A f d x z) (hP : Γ ⊢[PRAAx] cubePoints b d y)
    (hA : Γ ⊢[PRAAx] attainment A g b x u y) : Γ ⊢[PRAAx] namedAt f g z u q t := by
  let a := ap2 f q z
  let v := ap2 g t u
  let D := scale q*scale t
  let E := scale q+scale t
  let C := ((two*two)*D)*denominatorOf a*denominatorOf v
  let S := scale C
  have hfirst := lower_bound_at A f d x z (ap2 b C y) C q hL (cube_points_at b d y C hP)
  have hsecond := attainment_at A g b x u y C t C hA
  have relaxed : Γ ⊢[PRAAx] RationalValueBounds.upper (sample A (ap2 b C y) C x) v
      ((succ two)*scale t+S) (scale t*S) := by
    apply RationalValueBounds.upper_mono _ _ _ _ _ _
      (RationalAlgebra.positive_product
        (RationalAlgebra.positive_product (RationalAlgebra.positive_product
          (le_of_eq_add (d := succ two) (by ipra_ring)) (RationalCubeGrid.scale_positive C)) (RationalCubeGrid.scale_positive t))
        (RationalCubeGrid.scale_positive C)) hsecond
    exact le_of_eq_add (d := (succ (two*two))*scale t*scale t*S*S) (by dsimp [S]; ipra_ring)
  have combined := RationalValueBounds.upper_triangle _ _ _ _ _ _ _ hfirst relaxed
  have rescaled : Γ ⊢[PRAAx] RationalValueBounds.upper a v (S*(E*S+(two*two)*D)) (S*(D*S)) :=
    RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (by dsimp [S,D,E]; ipra_ring) (by dsimp [S,D]; ipra_ring) combined
  have bound : Γ ⊢[PRAAx] RationalValueBounds.upper a v (E*S+(two*two)*D) (D*S) :=
    RationalValueBounds.upper_cancel _ _ _ _ S (RationalCubeGrid.scale_positive C) rescaled
  have native : Γ ⊢[PRAAx] le (S*(D*RationalValueBounds.crossLeft a v))
      (S*(D*RationalValueBounds.crossLeft v a+E*denominatorOf a*denominatorOf v)+C) :=
    le_congr (by ipra_ring) (by dsimp [C]; ipra_ring) bound
  have result : Γ ⊢[PRAAx] le (D*RationalValueBounds.crossLeft a v)
      (D*RationalValueBounds.crossLeft v a+E*denominatorOf a*denominatorOf v) :=
    GapRemoval.gap (C := C) (le_congr (by dsimp [S,scale]; ipra_ring) (by dsimp [S,scale]; ipra_ring) native)
  exact result

theorem lower_le_attained (A : PR 3) (f g b : PR 2) (d x z u y : PTm n)
    (hL : Γ ⊢[PRAAx] lowerBound A f d x z) (hP : Γ ⊢[PRAAx] cubePoints b d y)
    (hA : Γ ⊢[PRAAx] attainment A g b x u y) : Γ ⊢[PRAAx] namedLE f g z u := by
  refine .allI (.allI ?_)
  have l : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] lowerBound A f (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift z)) := by
    simpa only [Fm.shift,subst_lowerBound,Syn.shift] using hL.shift.shift
  have p : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] cubePoints b (Syn.shift (Syn.shift d)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_cubePoints,Syn.shift] using hP.shift.shift
  have a : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] attainment A g b (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift u)) (Syn.shift (Syn.shift y)) := by
    simpa only [Fm.shift,subst_attainment,Syn.shift] using hA.shift.shift
  exact lower_le_attained_at A f g b _ _ _ _ _ (var 1) (var 0) l p a

theorem value_unique (A : PR 3) (f g b c : PR 2) (d x z u y v : PTm n)
    (hf : Γ ⊢[PRAAx] lowerBound A f d x z) (hg : Γ ⊢[PRAAx] lowerBound A g d x u)
    (hb : Γ ⊢[PRAAx] cubePoints b d y) (hc : Γ ⊢[PRAAx] cubePoints c d v)
    (ha : Γ ⊢[PRAAx] attainment A f b x z y) (hd : Γ ⊢[PRAAx] attainment A g c x u v) :
    Γ ⊢[PRAAx] equivalent f g z u := .andI (lower_le_attained A f g c d x z u v hf hc hd)
      (lower_le_attained A g f b d x u z y hg hb ha)


def pointBody (A : PR 3) (mu : PR 2) : PTm 2 := RationalCubeMinimum.minimizer A mu (fstT (var 1)) (var 0) (sndT (var 1))
def pointF (A : PR 3) (mu : PR 2) : PR 2 := PTm.toPR (pointBody A mu)
theorem point_at (A : PR 3) (mu : PR 2) (d k x : PTm n) : Γ ⊢[PRAAx]
    ap2 (pointF A mu) k (data d x) ≐ RationalCubeMinimum.minimizer A mu d k x := by
  have e := toPR_eq (Γ := Γ) (pointBody A mu) ![k,data d x]
  have q := Prf.eqCongr (Γ := Γ) (RationalCubeMinimum.minimizer A mu (var 0) (var 1) (var 2) : PTm 3)
    (σ := ![fstT (data d x),k,sndT (data d x)]) (σ' := ![d,k,x])
    (fun i => by fin_cases i; exact fst_pair _ _; exact .eqRefl _; exact snd_pair _ _)
  exact e.eqTrans (by simpa [pointBody,Matrix.cons_val_succ',Matrix.cons_val_zero'] using q)

theorem source_cube_points (A : PR 3) (mu : PR 2) (d x : PTm n) : Γ ⊢[PRAAx] cubePoints (pointF A mu) d (data d x) := by
  refine .allI ?_
  have eq := point_at (Γ := Γ.map Fm.shift) A mu (Syn.shift d) (var 0) (Syn.shift x)
  have proof := Prf.eqSubst (Γ := Γ.map Fm.shift) (presentedCube (var 0) (var 1) : Fm PTm 2)
    ![RationalCubeMinimum.minimizer A mu (Syn.shift d) (var 0) (Syn.shift x),Syn.shift d]
    ![ap2 (pointF A mu) (var 0) (data (Syn.shift d) (Syn.shift x)),Syn.shift d]
    (fun i => by fin_cases i; exact eq.eqSymm; exact .eqRefl _)
    (by simpa using RationalCubeMinimum.minimizer_presented (Γ := Γ.map Fm.shift) A mu (Syn.shift d) (var 0) (Syn.shift x))
  simpa [Syn.shift,RationalCubeInfimumName.subst_data] using proof

theorem source_lower_bound (A : PR 3) (mu : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx] lowerBound A (RationalCubeInfimumName.nameF A mu) d x (data d x) := by
  refine .allI (.allI (.allI (.impI ?_)))
  let D := Syn.shift (Syn.shift (Syn.shift d))
  let X := Syn.shift (Syn.shift (Syn.shift x))
  let Δ := presentedCube (var 2) D :: ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have c : Δ ⊢[PRAAx] coherence A D X := by
    simpa only [Δ,D,X,Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift.shift.wk
  have t : Δ ⊢[PRAAx] continuity A mu D X := by
    simpa only [Δ,D,X,Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift.shift.wk
  have h := RationalValueBounds.upper_congr (RationalCubeInfimumName.name_at A mu D (var 0) X).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _)
    (RationalCubeInfimumName.value_lower_bound A mu D (var 0) X (var 2) (var 1) c t (Prf.hyp0 : Δ ⊢[PRAAx] presentedCube (var 2) D))
  simpa only [lowerAt,Δ,D,X,Syn.shift,RationalCubeInfimumName.subst_data] using h

theorem source_attainment (A : PR 3) (mu : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    attainment A (RationalCubeInfimumName.nameF A mu) (pointF A mu) x (data d x) (data d x) := by
  refine .allI (.allI (.allI ?_))
  let D := Syn.shift (Syn.shift (Syn.shift d))
  let X := Syn.shift (Syn.shift (Syn.shift x))
  let Δ := ((Γ.map Fm.shift).map Fm.shift).map Fm.shift
  have c : Δ ⊢[PRAAx] coherence A D X := by
    simpa only [Δ,D,X,Fm.shift,RationalCubeMinimum.subst_coherence,Syn.shift] using hc.shift.shift.shift
  have t : Δ ⊢[PRAAx] continuity A mu D X := by
    simpa only [Δ,D,X,Fm.shift,RationalCubeMinimum.subst_continuity,Syn.shift] using ht.shift.shift.shift
  have h := RationalValueBounds.upper_congr
    (congrAp3 A (point_at A mu D (var 2) X).eqSymm (.eqRefl _) (.eqRefl _))
    (RationalCubeInfimumName.name_at A mu D (var 1) X).eqSymm (.eqRefl _) (.eqRefl _)
    (RationalCubeInfimumName.approximate_attainment A mu D (var 2) (var 1) (var 0) X c t)
  simpa only [attainedAt,sample,Δ,D,X,Syn.shift,RationalCubeInfimumName.subst_data] using h

/-- Original source hypotheses alone return the actual regular value and
actual approximate points with both defining infimum properties. -/
theorem source_infimum (A : PR 3) (mu : PR 2) (d x : PTm n) (hc : Γ ⊢[PRAAx] coherence A d x)
    (ht : Γ ⊢[PRAAx] continuity A mu d x) : Γ ⊢[PRAAx]
    RationalCubeInfimumName.regular (RationalCubeInfimumName.nameF A mu) (data d x) ⋏
      lowerBound A (RationalCubeInfimumName.nameF A mu) d x (data d x) ⋏
        cubePoints (pointF A mu) d (data d x) ⋏
          attainment A (RationalCubeInfimumName.nameF A mu) (pointF A mu) x (data d x) (data d x) :=
  .andI (RationalCubeInfimumName.name_regular A mu d x hc ht) (.andI (source_lower_bound A mu d x hc ht)
    (.andI (source_cube_points A mu d x) (source_attainment A mu d x hc ht)))

theorem source_value_unique (A : PR 3) (mu : PR 2) (g b : PR 2) (d x z y : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hL : Γ ⊢[PRAAx] lowerBound A g d x z) (hP : Γ ⊢[PRAAx] cubePoints b d y)
    (hA : Γ ⊢[PRAAx] attainment A g b x z y) : Γ ⊢[PRAAx]
    equivalent (RationalCubeInfimumName.nameF A mu) g (data d x) z :=
  value_unique A (RationalCubeInfimumName.nameF A mu) g (pointF A mu) b d x (data d x) z (data d x) y
    (source_lower_bound A mu d x hc ht) hL (source_cube_points A mu d x) hP (source_attainment A mu d x hc ht) hA

theorem actual_lower_bound_below_attained_name_closed (A : PR 3) (f g b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (lowerBound A f (var 0) (var 1) (var 2) ⟶ cubePoints b (var 0) (var 4) ⟶ attainment A g b (var 1) (var 3) (var 4) ⟶
      namedLE f g (var 2) (var 3)) :=
  closeUniv 5 (.impI (.impI (.impI (lower_le_attained A f g b (var 0) (var 1) (var 2) (var 3) (var 4) Prf.hyp1.wk Prf.hyp1 Prf.hyp0))))
theorem actual_named_infimum_uniqueness_closed (A : PR 3) (f g b c : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (lowerBound A f (var 0) (var 1) (var 2) ⟶ lowerBound A g (var 0) (var 1) (var 3) ⟶
      cubePoints b (var 0) (var 4) ⟶ cubePoints c (var 0) (var 5) ⟶
        attainment A f b (var 1) (var 2) (var 4) ⟶ attainment A g c (var 1) (var 3) (var 5) ⟶
          equivalent f g (var 2) (var 3)) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (.impI (value_unique A f g b c (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)))))))))
theorem actual_cube_approximate_point_program_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (ap2 (pointF A mu) (var 1) (data (var 0) (var 2)) ≐ RationalCubeMinimum.minimizer A mu (var 0) (var 1) (var 2)) :=
  closeUniv 3 (point_at A mu (var 0) (var 1) (var 2))
theorem actual_cube_approximate_points_presented_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (cubePoints (pointF A mu) (var 0) (data (var 0) (var 1))) := closeUniv 2 (source_cube_points A mu (var 0) (var 1))
theorem actual_source_cube_infimum_name_closed (A : PR 3) (mu : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶
      RationalCubeInfimumName.regular (RationalCubeInfimumName.nameF A mu) (data (var 0) (var 1)) ⋏
        lowerBound A (RationalCubeInfimumName.nameF A mu) (var 0) (var 1) (data (var 0) (var 1)) ⋏
          cubePoints (pointF A mu) (var 0) (data (var 0) (var 1)) ⋏
            attainment A (RationalCubeInfimumName.nameF A mu) (pointF A mu) (var 1) (data (var 0) (var 1)) (data (var 0) (var 1))) :=
  closeUniv 2 (.impI (.impI (source_infimum A mu (var 0) (var 1) Prf.hyp1 Prf.hyp0)))
theorem actual_source_cube_infimum_unique_closed (A : PR 3) (mu : PR 2) (g b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶
      lowerBound A g (var 0) (var 1) (var 2) ⟶ cubePoints b (var 0) (var 3) ⟶ attainment A g b (var 1) (var 2) (var 3) ⟶
        equivalent (RationalCubeInfimumName.nameF A mu) g (data (var 0) (var 1)) (var 2)) :=
  closeUniv 4 (.impI (.impI (.impI (.impI (.impI (source_value_unique A mu g b (var 0) (var 1) (var 2) (var 3)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))


theorem named_le_at (f g : PR 2) (z u q t : PTm n) (h : Γ ⊢[PRAAx] namedLE f g z u) :
    Γ ⊢[PRAAx] namedAt f g z u q t := by
  simpa [namedLE,Syn.subst_shift,Syn.shift_subst,Syn.shift,Syn.subst_subst,Function.comp_def] using (h.allE q).allE t

/-- The uniqueness conclusion is actual scalar-name metric equality at
every pair of independent query precisions. -/
theorem equivalent_radius (f g : PR 2) (z u q t : PTm n) (h : Γ ⊢[PRAAx] equivalent f g z u) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 f q z) (ap2 g t u) (scale q+scale t) (scale q*scale t) :=
  RationalValueBounds.radius_of_upper _ _ _ _ (named_le_at f g z u q t (.andE₁ h))
    (RationalValueBounds.upper_congr (.eqRefl _) (.eqRefl _) (add_comm _ _) (mul_comm _ _)
      (named_le_at g f u z t q (.andE₂ h)))

theorem source_unique_radius (A : PR 3) (mu : PR 2) (g b : PR 2) (d x z y q t : PTm n)
    (hc : Γ ⊢[PRAAx] coherence A d x) (ht : Γ ⊢[PRAAx] continuity A mu d x)
    (hL : Γ ⊢[PRAAx] lowerBound A g d x z) (hP : Γ ⊢[PRAAx] cubePoints b d y)
    (hA : Γ ⊢[PRAAx] attainment A g b x z y) : Γ ⊢[PRAAx]
    RationalValueBounds.radius (ap2 (RationalCubeInfimumName.nameF A mu) q (data d x)) (ap2 g t z)
      (scale q+scale t) (scale q*scale t) :=
  equivalent_radius _ _ _ _ _ _ (source_value_unique A mu g b d x z y hc ht hL hP hA)

theorem actual_source_cube_infimum_unique_metric_closed (A : PR 3) (mu : PR 2) (g b : PR 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (coherence A (var 0) (var 1) ⟶ continuity A mu (var 0) (var 1) ⟶
      lowerBound A g (var 0) (var 1) (var 2) ⟶ cubePoints b (var 0) (var 3) ⟶ attainment A g b (var 1) (var 2) (var 3) ⟶
        RationalValueBounds.radius (ap2 (RationalCubeInfimumName.nameF A mu) (var 4) (data (var 0) (var 1))) (ap2 g (var 5) (var 2))
          (scale (var 4)+scale (var 5)) (scale (var 4)*scale (var 5))) :=
  closeUniv 6 (.impI (.impI (.impI (.impI (.impI (source_unique_radius A mu g b (var 0) (var 1) (var 2) (var 3) (var 4) (var 5)
    (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp)) (.hyp (by simp))))))))

end LeanProofs.IPRA.Analysis.RationalCubeInfimumComparison
