import IPRADerivations.Geometry.SphericalHalf

/-!
# Differential variation formulas (`spherical_trigonometry_ipra_2026-11-15`, `thm:differential`)

Packet: `geometry/spherical_trigonometry_ipra_2026-11-15`, theorem `thm:differential`:
`da = cos C db + cos B dc + sin b sin C dA` (9.2), with cyclic companions (9.3), (9.4). Proof:
"Differentiate the cosine law for `a` ... The cyclic five-part identities give
`sin a cos C = sin b cos c - cos b sin c cos A`, `sin a cos B = cos b sin c - sin b cos c cos A`.
The sine law gives `sin b sin c sin A = sin a sin b sin C`. Substitution yields
`sin a da = sin a (cos C db + cos B dc + sin b sin C dA)`."

The substitution step is derived for arbitrary integer terms: the symbols `da, db, dc, dA` are
four further values (the derivative names at the fixed parameter), and the hypotheses are the
relations of the finite core that the step uses together with the differentiated cosine law

`sin a da = (sin b cos c - cos b sin c cos A) db + (cos b sin c - sin b cos c cos A) dc
            + sin b sin c sin A dA`   (D)

* `variation_ring`: the certificate over a commutative ring;
* `variation`: from the core relations and (D),
  `s_b s_c (s_a da) = s_b s_c (s_a (c_C db + c_B dc + s_b s_C dA))`.

The factor `s_b s_c` replaces the guards of the two five-part identities; the packet's final
cancellation of `sin a` is under its apartness witness and is not performed. (9.3) and (9.4)
are the same statement after the cyclic relabelling of the terms. That (D) holds for the
derivative names of a differentiable family (the product and chain rules for real names) is
analysis and is not derived here.
-/

namespace LeanProofs.IPRA.Geometry.SphericalVariation

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The substitution step of `thm:differential` over a commutative ring. -/
theorem variation_ring {R : Type*} [CommRing R]
    {x y z τ sa sb sc cA cB cC sA sC da db dc dA : R}
    (h2 : sb * sb + y * y = 1) (h3 : sc * sc + z * z = 1)
    (h5 : sb * sc * cA = x - y * z) (h6 : sc * sa * cB = y - z * x)
    (h7 : sa * sb * cC = z - x * y) (h8 : sb * sc * sA = τ) (h10 : sa * sb * sC = τ)
    (hD : sa * da = (sb * z - y * sc * cA) * db + (y * sc - sb * z * cA) * dc +
      sb * sc * sA * dA) :
    sb * sc * (sa * da) = sb * sc * (sa * (cC * db + cB * dc + sb * sC * dA)) := by
  linear_combination sb * sc * hD + sc * db * (z * h2 - y * h5 - h7) +
    sb * dc * (y * h3 - z * h5 - h6) + sb * sc * dA * (h8 - h10)

variable {x y z τ sa sb sc cA cB cC sA sC da db dc dA : ZT n}

/-- `thm:differential`, (9.2), times `s_b s_c`: the differentiated cosine law and the core
relations give `s_a da = s_a (c_C db + c_B dc + s_b s_C dA)`. -/
theorem variation
    (h2 : Γ ⊢[PRAAx] ZT.eq (sb * sb + y * y) (ZT.natLit 1))
    (h3 : Γ ⊢[PRAAx] ZT.eq (sc * sc + z * z) (ZT.natLit 1))
    (h5 : Γ ⊢[PRAAx] ZT.eq (sb * sc * cA) (x - y * z))
    (h6 : Γ ⊢[PRAAx] ZT.eq (sc * sa * cB) (y - z * x))
    (h7 : Γ ⊢[PRAAx] ZT.eq (sa * sb * cC) (z - x * y))
    (h8 : Γ ⊢[PRAAx] ZT.eq (sb * sc * sA) τ) (h10 : Γ ⊢[PRAAx] ZT.eq (sa * sb * sC) τ)
    (hD : Γ ⊢[PRAAx] ZT.eq (sa * da)
      ((sb * z - y * sc * cA) * db + (y * sc - sb * z * cA) * dc + sb * sc * sA * dA)) :
    Γ ⊢[PRAAx] ZT.eq (sb * sc * (sa * da))
      (sb * sc * (sa * (cC * db + cB * dc + sb * sC * dA))) := by
  have e2 := ZT.toZ_eq h2
  have e3 := ZT.toZ_eq h3
  have e5 := ZT.toZ_eq h5
  have e6 := ZT.toZ_eq h6
  have e7 := ZT.toZ_eq h7
  have e8 := ZT.toZ_eq h8
  have e10 := ZT.toZ_eq h10
  have eD := ZT.toZ_eq hD
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_sub, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_one]
    at e2 e3 e5 e6 e7 e8 e10 eD ⊢
  exact variation_ring e2 e3 e5 e6 e7 e8 e10 eD

end LeanProofs.IPRA.Geometry.SphericalVariation
