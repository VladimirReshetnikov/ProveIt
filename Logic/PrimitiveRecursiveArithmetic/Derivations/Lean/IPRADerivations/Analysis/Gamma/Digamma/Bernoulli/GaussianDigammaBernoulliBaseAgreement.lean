import IPRADerivations.Analysis.Gamma.Digamma.Bernoulli.GaussianDigammaBernoulliName

/-!
# The quantified base approximation for the digamma recurrence

A base proof supplies the actual mesh-prefix error at every internal
clock and every sufficiently large mesh. The mesh demand is a
primitive-recursive function of the clock and the rational input.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliBaseAgreement

open_ipra
open GaussianCoefficientNameBounds (unit subst_unit)
open GaussianDigammaBernoulliName (nameF nameData radius requiredMesh base_le_requiredMesh)
open GaussianDigammaBernoulliRecurrence (prefixAt subst_prefixAt)
open GaussianEuclideanDistanceName (pointCN)
open GaussianRationalMetric (distanceBounded subst_distanceBounded)
open GaussianStirlingNames (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def agreement (initial : PR 2) (demand : PR 3) (A B x cost : PTm n) : Fm PTm n :=
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  .all (.all ((le one (var 0) ⋏ le (ap3 demand (var 1) (sh A) (sh B)) (var 0)) ⟶
    distanceBounded (prefixAt 0 (sh A) (sh B) (var 0) (var 1)) (ap2 initial (var 1) (sh x))
      (sh cost) (unit (var 1))))

ipra_subst agreement [Syn.subst_shift, Syn.shift_subst, one]

theorem agreement_at (initial : PR 2) (demand : PR 3) (A B x cost p Q : PTm n)
    (h : Γ ⊢[PRAAx] agreement initial demand A B x cost)
    (hp : Γ ⊢[PRAAx] le one Q) (hQ : Γ ⊢[PRAAx] le (ap3 demand p A B) Q) :
    Γ ⊢[PRAAx] distanceBounded (prefixAt 0 A B Q p) (ap2 initial p x) cost (unit p) := by
  let sh (v : PTm n) := Syn.shift v
  have first : Γ ⊢[PRAAx] .all ((le one (var 0) ⋏ le (ap3 demand (sh p) (sh A) (sh B)) (var 0)) ⟶
      distanceBounded (prefixAt 0 (sh A) (sh B) (var 0) (sh p)) (ap2 initial (sh p) (sh x))
        (sh cost) (unit (sh p))) := by
    simpa only [agreement,sh,Fm.subst_all,Fm.subst_imp,Fm.subst_and,subst_le,subst_distanceBounded,
      subst_prefixAt,subst_ap2,subst_ap3,subst_unit,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.up_zero,Syn.up_one,Syn.up_succ,Syn.inst_zero,Syn.subst_inst_shift,
      Foundations.BoundedFormulas.subst_up_shift',Syn.shift_var] using h.allE p
  have bound : Γ ⊢[PRAAx] (le one Q ⋏ le (ap3 demand p A B) Q) ⟶
      distanceBounded (prefixAt 0 A B Q p) (ap2 initial p x) cost (unit p) := by
    simpa only [sh,Fm.subst_imp,Fm.subst_and,subst_le,subst_distanceBounded,subst_prefixAt,subst_ap2,subst_ap3,
      subst_unit,one,ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ,
      Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using first.allE Q
  exact .impE bound (.andI hp hQ)

theorem prefix_from_agreement (initial : PR 2) (demand : PR 3) (m : ℕ) (A B Q p x cost : PTm n)
    (hs : Γ ⊢[PRAAx] source A B) (hx : Γ ⊢[PRAAx] pointCN initial x)
    (base : Γ ⊢[PRAAx] agreement initial demand A B x cost)
    (hp : Γ ⊢[PRAAx] le one Q)
    (hq : Γ ⊢[PRAAx] le (requiredMesh m A B p (ap3 demand p A B)) Q) :
    Γ ⊢[PRAAx] distanceBounded (prefixAt m A B Q p)
      (ap2 (nameF initial m) p (nameData m A B x)) (radius m B cost) (unit p) :=
  GaussianDigammaBernoulliName.prefix_distance initial m A B Q p x (ap3 demand p A B) cost hs hx hq
    (agreement_at initial demand A B x cost p Q base hp (le_trans (base_le_requiredMesh _ _ _ _ _) hq))

end LeanProofs.IPRA.Analysis.GaussianDigammaBernoulliBaseAgreement
