import IPRADerivations.Analysis.Names.GaussianNameEquivalence
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder

/-!
# Select a regular name with a fixed numerical branch bit

The bit is part of the input data and is shared by every observation.
Once its value is proved, the selected name represents exactly the
corresponding original name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNameBranch

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalDistanceOrder (distance_congr)
open RationalArithmetic (select select_zero select_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (b x y : PTm n) : PTm n := pairT b (pairT x y)
def body (F G : PR 2) : PTm 2 :=
  select (fstT (var 1)) (ap2 F (var 0) (fstT (sndT (var 1)))) (ap2 G (var 0) (sndT (sndT (var 1))))
def nameF (F G : PR 2) : PR 2 := PTm.toPR (body F G)

@[simp] theorem subst_data {m : ℕ} (σ : Fin n → PTm m) (b x y : PTm n) :
    Syn.subst σ (data b x y) = data (Syn.subst σ b) (Syn.subst σ x) (Syn.subst σ y) := by simp [data]

theorem sample_at (F G : PR 2) (p b x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF F G) p (data b x y) ≐ select b (ap2 F p x) (ap2 G p y) := by
  let v := data b x y
  have e : Γ ⊢[PRAAx] ap2 (nameF F G) p v ≐ select (fstT v)
      (ap2 F p (fstT (sndT v))) (ap2 G p (sndT (sndT v))) := by
    have given := toPR_eq (Γ := Γ) (body F G) ![p,v]
    change Γ ⊢[PRAAx] ap2 (nameF F G) p v ≐ Syn.subst ![p,v] (body F G) at given
    simpa [body] using given
  have d := Prf.eqCongr (Γ := Γ) (Ax := PRAAx)
    (select (var 1) (ap2 F (var 0) (var 2)) (ap2 G (var 0) (var 3)) : PTm 4)
    (σ := ![p,fstT v,fstT (sndT v),sndT (sndT v)]) (σ' := ![p,b,x,y]) (fun i => by
      fin_cases i
      exact .eqRefl _
      exact fst_pair _ _
      exact (congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)
      exact (congrSnd (snd_pair _ _)).eqTrans (snd_pair _ _))
  exact e.eqTrans (by simpa using d)

theorem select_left (F G : PR 2) (b x y : PTm n) (hb : Γ ⊢[PRAAx] b ≐ zero)
    (hf : Γ ⊢[PRAAx] pointCN F x) : Γ ⊢[PRAAx] crossEquivalent (nameF F G) F (data b x y) x := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have eq : Δ ⊢[PRAAx] sh b ≐ zero := by simpa [Δ,Fm.shift,Syn.shift,sh] using hb.shift.shift
  have fx : Δ ⊢[PRAAx] pointCN F (sh x) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hf.shift.shift
  have read := (sample_at F G (var 1) (sh b) (sh x) (sh y)).eqTrans (select_zero _ _ _ eq)
  simpa only [crossEquivalent,Syn.shift,sh,subst_data] using
    distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (point_at F (sh x) (var 1) (var 0) fx)

theorem select_right (F G : PR 2) (b x y : PTm n) (hb : Γ ⊢[PRAAx] b ≐ one)
    (hg : Γ ⊢[PRAAx] pointCN G y) : Γ ⊢[PRAAx] crossEquivalent (nameF F G) G (data b x y) y := by
  refine .allI (.allI ?_)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  let sh (v : PTm n) := Syn.shift (Syn.shift v)
  have eq : Δ ⊢[PRAAx] sh b ≐ one := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using hb.shift.shift
  have gy : Δ ⊢[PRAAx] pointCN G (sh y) := by simpa [Δ,Fm.shift,Syn.shift,sh] using hg.shift.shift
  have read := (sample_at F G (var 1) (sh b) (sh x) (sh y)).eqTrans (select_one _ _ _ eq)
  simpa only [crossEquivalent,Syn.shift,sh,subst_data] using
    distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) (point_at G (sh y) (var 1) (var 0) gy)

end LeanProofs.IPRA.Analysis.GaussianNameBranch
