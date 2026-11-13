# Independent review: trace75 conditional roots and signed squares

Both frozen accepted packets support their conditional Lean statements. `check.py` rehashes the source and copied source, runner, recorded pinned inputs, Lean binary, output objects and logs; resolves their direct and selected support modules through the recorded search paths; and checks the exact axiom reports. The selected paths and hashes are in `check-output.txt`. These are post-hoc file checks, not an independent Lean replay or complete transitive producer/companion audit.

## Root extraction with representatives

`Trace75Root.roots_of_representatives` quantifies over an `ORingStructure V` model of IΣ₁, **arbitrary** ports `p : Fin 4 → DiffRing V`, and `v : Fin 10 → V`. It does not assume the coordinates of `v` positive. It assumes strictly positive `delta`, `U`, `E`, `M` and `V0` in `V`; equalities identifying the actual trace75 registers `Delta`, `U`, `E`, `M` with their respective `ι` images; equalities `Vreg*Vreg = ι(V0*V0)` and `Zreg*Zreg = ι(Z0*Z0)`; and `value75 p (ι ∘ v)=0`. No positivity of `Z0` is required. It concludes positive `tau,f : V` with `E=tau*tau` and `1+delta*U*U*E=f*f`.

The proof sets `a=delta*U*U*E`, `G=E*(1+a)`, `Q=delta*(4*a*(1+a))`, rewrites the actual Lean trace75 registers, and obtains in the difference ring `(Q−1)Z0²=M²G(Q*V0²−1)`. It casts the subtractions back under the proved positivity bounds and calls `TenPositiveProductRoot.doubled_product_roots`. This is conditional extraction; the equalities and positivity of the registers are not established from graph witnesses by this packet.

## Elimination of signed-square assumptions

`Trace75RootNonzero.roots_of_positive_representatives` retains precisely the positive representatives and image equalities for `delta`, `U`, `E`, `M` and the same trace75 zero. It removes both signed square-representative premises, with no `v`-positivity or natural-port assumption. `square_rep` uses the sign representation of an arbitrary difference-ring element to obtain a natural representative of its square; if the ring element is nonzero, its natural representative is positive.

`V_nonzero` obtains `Q>0`, `G>0` and `M>0`. Assuming the signed `V` register is zero, the zero equation yields `(Q−1)*Z² + M²*G = 0` in the ordered difference ring. The first summand is nonnegative and the second strictly positive, a contradiction. This gives positive `V0`; a square representative for `Z` needs no positivity. The result then applies the first packet with the same ports and valuation. The four positive register representatives remain explicit; deriving them from a zero or connecting them to the external 74/75 rows is separate work. Neither result proves halting equivalence or an iPRA endpoint.

## Receipts and provider selection

Accepted `root-attempt02` yields object `bf8d56a7526a5324d04c7178d8265e619a15aa624d117d11ba8b864831624958`. Its three direct imports first resolve to the fresh trace75 provider `1ae82441c7023e9675c5cc532d4026da6a3ee77e906996d67c315e4f693b079c`, `ModelDifferenceRing` `d0fb8f9664675190dbfc25915a687cef203b8362681d9256606f1022a6dbde74`, and `ProductRoot` `92dbb47e969d3603f6f496f53c7995493a989293a37e5272c308ff79d3fb09d5`. Accepted `nonzero-attempt02` imports that exact root object and produces `35e467ec9e32fb7e0e0b02f917c576811341e89d4a593ccc8dcd8603a5474802`.

Post-hoc first resolution in both runs selects the **root run's** overlay for the trace75 and model modules: the nonzero run's path puts the root provider directory first, before its own newly created overlay. The selected underlying files match the pins; this check does not prove the full serialized import ancestry or package/dynamic consistency. Both exact captured reports are `[propext, Classical.choice, Quot.sound]` with empty stderr. The runners enforce resource limits and reject coded warnings/errors and `sorryAx`, but do not enforce a named axiom whitelist; we inspected the reports. The first root and nonzero attempts had nonzero Lean exits and no objects. Both accepted terminal receipts precede final runner assertions, and no separately retained outer-exit receipt was found.
