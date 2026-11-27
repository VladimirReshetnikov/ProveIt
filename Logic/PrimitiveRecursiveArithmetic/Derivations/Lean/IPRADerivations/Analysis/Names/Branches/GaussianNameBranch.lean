import IPRADerivations.Analysis.Names.Arithmetic.GaussianNameEquivalence
import IPRADerivations.Analysis.RationalArithmetic.Distances.GaussianRationalDistanceOrder

/-!
# Select a regular name with a fixed numerical branch bit

The bit is part of the input data and is shared by every observation.
Once its value is proved, the selected name represents exactly the
corresponding original name.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNameBranch

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameEquivalence (crossEquivalent point_at)
open GaussianRationalDistanceOrder (distance_congr)
open RationalArithmetic (select select_zero select_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def data (b x y : PTm n) : PTm n := pairT b (pairT x y)
def body (F G : PR 2) : PTm 2 :=
  select (fstT (var 1)) (ap2 F (var 0) (fstT (sndT (var 1)))) (ap2 G (var 0) (sndT (sndT (var 1))))
def nameF (F G : PR 2) : PR 2 := PTm.toPR (body F G)

ipra_subst data

theorem sample_at (F G : PR 2) (p b x y : PTm n) :
    Γ ⊢[PRAAx] ap2 (nameF F G) p (data b x y) ≐ select b (ap2 F p x) (ap2 G p y) := by
  simpa [nameF, body, data, pairVector, pairVectorField] using
    (toPR_pairVector_eq (Γ := Γ) (k := 2)
      (select (var 1) (ap2 F (var 0) (var 2)) (ap2 G (var 0) (var 3))) p ![b, x, y])

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
