import IPRADerivations.Analysis.Polynomials.Elimination.GaussianSuperellipticSubspaceWitness
import IPRADerivations.Foundations.FiniteCoverAssignment

/-!
# Superelliptic point predicates on each actual cover group

The increasing indices of a first-cover group preserve distinctness of
the original field points. Each original curve equation is transported
through equality of the retained raw point code.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianSuperellipticCoverPoints

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.FiniteCoverAssignment
  (group indices group_length group_lookup index_bound indices_increasing subst_group)
open LeanProofs.IPRA.Foundations.MasterCertificate (entry)
open LeanProofs.IPRA.Foundations.SequenceComposition (length subst_length)
open GaussianRationalCurveFibers (pointDistinct pointDistinctFrom point_distinct_at)
open GaussianRationalFiberGrouping (abscissa ordinate subst_abscissa subst_ordinate)
open GaussianRationalValueEquality
  (valueEqual subst_valueEqual recode_equal_of_equal_values equal_values_of_recode_equal)
open GaussianTranslatedNonconstant (recode_congr)
open GaussianSuperellipticNormDegree (pointPowers point_power_at)
open GaussianSuperellipticSubspaceWitness (points)
open GaussianRationalReciprocal (power powerF subst_power)
open GaussianRationalHorner (evaluate subst_evaluate)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem group_power_at (test : PTm 3) (f m P M data g i : PTm n)
    (h : Γ ⊢[PRAAx] pointPowers f m P) (hi : Γ ⊢[PRAAx] lt i (length (group test P M data g))) :
    Γ ⊢[PRAAx] power (ordinate (group test P M data g) i) m ≐
      evaluate f (abscissa (group test P M data g) i) := by
  have bound := lt_congr (.eqRefl i) (group_length test P M data g) hi
  have eq := group_lookup test P M data g i bound
  have original := point_power_at f m P _ h (index_bound test P M data g i bound)
  have py := congrAp2 powerF (.eqRefl m) (congrSnd eq)
  have px := GaussianRationalMonicReduction.evaluate_congr (.eqRefl f) (congrFst eq)
  exact py.eqTrans (original.eqTrans px.eqSymm)

theorem group_powers (test : PTm 3) (f m P M data g : PTm n) (h : Γ ⊢[PRAAx] pointPowers f m P) :
    Γ ⊢[PRAAx] pointPowers f m (group test P M data g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointPowers (Syn.shift f) (Syn.shift m) (Syn.shift P) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  refine .allI (.impI ?_)
  simpa only [Syn.shift, subst_group, subst_power, subst_evaluate, subst_ordinate, subst_abscissa] using group_power_at test (Syn.shift f) (Syn.shift m) (Syn.shift P)
    (Syn.shift M) (Syn.shift data) (Syn.shift g) (var 0) hs.wk Prf.hyp0

theorem group_distinct_at (test : PTm 3) (P M data g i j : PTm n) (h : Γ ⊢[PRAAx] pointDistinct P)
    (hi : Γ ⊢[PRAAx] lt i (length (group test P M data g)))
    (hj : Γ ⊢[PRAAx] lt j (length (group test P M data g))) (hij : Γ ⊢[PRAAx] lt i j) :
    Γ ⊢[PRAAx] neg (valueEqual (abscissa (group test P M data g) j) (abscissa (group test P M data g) i) ⋏
      valueEqual (ordinate (group test P M data g) j) (ordinate (group test P M data g) i)) := by
  let G := group test P M data g
  let I := indices test P M data g
  have size := group_length (Γ := Γ) test P M data g
  have bi := lt_congr (.eqRefl i) size hi
  have bj := lt_congr (.eqRefl j) size hj
  have ei := group_lookup test P M data g i bi
  have ej := group_lookup test P M data g j bj
  have original := point_distinct_at P (entry I i) (entry I j) h
    (index_bound test P M data g i bi) (index_bound test P M data g j bj)
    (indices_increasing test P M data g i j hij bj)
  refine .impI (.impE original.wk (.andI ?_ ?_))
  · exact equal_values_of_recode_equal _ _
      ((recode_congr (congrFst ej.wk)).eqSymm.eqTrans
        ((recode_equal_of_equal_values _ _ (.andE₁ Prf.hyp0)).eqTrans (recode_congr (congrFst ei.wk))))
  · exact equal_values_of_recode_equal _ _
      ((recode_congr (congrSnd ej.wk)).eqSymm.eqTrans
        ((recode_equal_of_equal_values _ _ (.andE₂ Prf.hyp0)).eqTrans (recode_congr (congrSnd ei.wk))))

theorem group_distinct (test : PTm 3) (P M data g : PTm n) (h : Γ ⊢[PRAAx] pointDistinct P) :
    Γ ⊢[PRAAx] pointDistinct (group test P M data g) := by
  have hs : Γ.map Fm.shift ⊢[PRAAx] pointDistinct (Syn.shift P) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  refine .allI (.impI ?_)
  let G := group test (Syn.shift P) (Syn.shift M) (Syn.shift data) (Syn.shift g)
  let Δ := lt (var 0) (length G) :: Γ.map Fm.shift
  have hg : Δ ⊢[PRAAx] lt (var 0) (length G) := Prf.hyp0
  have hD : Δ ⊢[PRAAx] pointDistinct (Syn.shift P) := hs.wk
  have inner : Δ ⊢[PRAAx] pointDistinctFrom G (var 0) := by
    refine .allI (.impI (.impI ?_))
    let i := Syn.shift (var 0 : PTm (n + 1))
    have hgs : Δ.map Fm.shift ⊢[PRAAx] lt i
        (length (group test (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift M))
          (Syn.shift (Syn.shift data)) (Syn.shift (Syn.shift g)))) := by
      simpa only [i, G, Fm.shift, Fm.subst_eq, subst_lt, subst_length, subst_group, Syn.shift] using hg.shift
    have hDs : Δ.map Fm.shift ⊢[PRAAx] pointDistinct (Syn.shift (Syn.shift P)) := by
      simpa [Fm.shift, Syn.shift] using hD.shift
    simpa only [i, G, Syn.shift, subst_group, subst_valueEqual, subst_abscissa, subst_ordinate, Fm.subst_and] using
      group_distinct_at test (Syn.shift (Syn.shift P)) (Syn.shift (Syn.shift M))
      (Syn.shift (Syn.shift data)) (Syn.shift (Syn.shift g)) i (var 0)
      hDs.wk.wk hgs.wk.wk Prf.hyp1 Prf.hyp0
  simpa only [Δ, G, Syn.shift, subst_group, subst_length] using inner

theorem group_points (test : PTm 3) (f m P M data g : PTm n) (h : Γ ⊢[PRAAx] points f m P) :
    Γ ⊢[PRAAx] points f m (group test P M data g) :=
  .andI (group_distinct test P M data g (.andE₁ h)) (group_powers test f m P M data g (.andE₂ h))

theorem actual_group_points_closed (test : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    (points (var 0) (var 1) (var 2) ⟶
      points (var 0) (var 1) (group test (var 2) (var 3) (var 4) (var 5))) :=
  closeUniv 6 (.impI (group_points test _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianSuperellipticCoverPoints
