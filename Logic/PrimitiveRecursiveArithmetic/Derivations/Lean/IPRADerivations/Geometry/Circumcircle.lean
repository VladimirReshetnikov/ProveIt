import IPRADerivations.Geometry.TriangleFormulas
import IPRADerivations.DiophantineNumberTheory.Coprime

/-!
# The circumcircle and the extended law of sines (`triangle_formulas_ipra`)

Theorem `thm:sine` of `triangle_formulas_ipra.tex`: `a/sin A = b/sin B = c/sin C = abc/h = 2R`, where
`R` is the radius of the explicitly constructed circumcircle. Its algebraic content, for the
vertices `(0, 0)`, `(x, y)`, `(z, w)` with `U = x² + y²`, `V = z² + w²`,
`W = (x − z)² + (y − w)²` and `D = 2(xw − yz) = 2h`, is that the point
`O = (wU − yV, xV − zU)` (the circumcentre scaled by `D`) satisfies

* `|O − D·(x, y)|² = |O|²` and `|O − D·(z, w)|² = |O|²` (equidistance from the three vertices);
* `|O|² = U V W`, i.e. `(2R)² h² = a² b² c²` with `R = |O|/D`.

Also Lemma `lem:square-compare`: `(u − v)² ≤ |u² − v²|` for `u, v ≥ 0`, in natural-number form
`(u ∸ v)² ≤ u² ∸ v²` (both orders).
-/

namespace LeanProofs.IPRA.Geometry.Circumcircle

open_ipra

/-! ## The circumcentre -/

section Centre

abbrev x : ZT 8 := .var2 0 1
abbrev y : ZT 8 := .var2 2 3
abbrev z : ZT 8 := .var2 4 5
abbrev w : ZT 8 := .var2 6 7

abbrev U : ZT 8 := ZT.sq x + ZT.sq y
abbrev V : ZT 8 := ZT.sq z + ZT.sq w
abbrev W : ZT 8 := ZT.sq (x - z) + ZT.sq (y - w)
abbrev D : ZT 8 := ZT.natLit 2 * (x * w - y * z)
abbrev Ox : ZT 8 := w * U - y * V
abbrev Oy : ZT 8 := x * V - z * U

def equidistBFormula : Fm PTm 8 :=
  ZT.eq (ZT.sq (Ox - D * x) + ZT.sq (Oy - D * y)) (ZT.sq Ox + ZT.sq Oy)

def equidistCFormula : Fm PTm 8 :=
  ZT.eq (ZT.sq (Ox - D * z) + ZT.sq (Oy - D * w)) (ZT.sq Ox + ZT.sq Oy)

def radiusFormula : Fm PTm 8 := ZT.eq (ZT.sq Ox + ZT.sq Oy) (U * V * W)

theorem equidistB_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] equidistBFormula := by
  unfold equidistBFormula; ipra_ring

theorem equidistC_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] equidistCFormula := by
  unfold equidistCFormula; ipra_ring

theorem radius_open : ([] : List (Fm PTm 8)) ⊢[PRAAx] radiusFormula := by
  unfold radiusFormula; ipra_ring

/-- The constructed centre is equidistant from the origin and `(x, y)`. -/
theorem equidistB : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 equidistBFormula := closeAll 8 equidistB_open

/-- The constructed centre is equidistant from the origin and `(z, w)`. -/
theorem equidistC : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 equidistCFormula := closeAll 8 equidistC_open

/-- `|O|² = U V W`: `(2R)² h² = a² b² c²`. -/
theorem radius : ([] : List (Fm PTm 0)) ⊢[PRAAx] allN 8 radiusFormula := closeAll 8 radius_open

end Centre

/-! ## Finite square comparison -/

section SquareCompare

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- `(u ∸ v)² ≤ u² ∸ v²`. -/
theorem square_compare (u v : PTm n) : Γ ⊢[PRAAx] le (monus u v * monus u v) (monus (u * u) (v * v)) := by
  refine .orE (lt_or_le u v) ?_ ?_
  · have h0 : (lt u v :: Γ) ⊢[PRAAx] monus u v ≐ zero := le_of_lt Prf.hyp0
    refine le_of_eq_add (d := monus (u * u) (v * v)) ?_
    have e := natEq h0
    apply deriveNat; ipra_simps
    linear_combination -(Groth.ι (IPRA.Q.mk _ (monus u v))) * e
  · have e := eq_add_of_le (Prf.hyp0 : (le v u :: Γ) ⊢[PRAAx] le v u)
    have hd : (le v u :: Γ) ⊢[PRAAx] monus u v ≐ monus u v := .eqRefl _
    have hsq : (le v u :: Γ) ⊢[PRAAx] monus (u * u) (v * v) ≐
        monus u v * monus u v + two * v * monus u v := by
      refine (congrMonus (?_ : (le v u :: Γ) ⊢[PRAAx] u * u ≐ v * v + (monus u v * monus u v + two * v * monus u v))
        (.eqRefl _)).eqTrans (add_monus' _ _)
      have e' := natEq e
      apply deriveNat; ipra_simps
      linear_combination (Groth.ι (IPRA.Q.mk _ u) + Groth.ι (IPRA.Q.mk _ v) + Groth.ι (IPRA.Q.mk _ (monus u v))) * e'
    exact le_congr (.eqRefl _) hsq.eqSymm (le_of_eq_add (d := two * v * monus u v) (.eqRefl _))

/-- `lem:square-compare`, variables `0 = u`, `1 = v`. -/
abbrev squareCompareFormula : Fm PTm 2 :=
  le (monus (var 0) (var 1) * monus (var 0) (var 1)) (monus (var 0 * var 0) (var 1 * var 1)) ⋏
    le (monus (var 1) (var 0) * monus (var 1) (var 0)) (monus (var 1 * var 1) (var 0 * var 0))

theorem square_compare_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 squareCompareFormula :=
  closeUniv 2 (.andI (square_compare _ _) (square_compare _ _))

end SquareCompare

end LeanProofs.IPRA.Geometry.Circumcircle
