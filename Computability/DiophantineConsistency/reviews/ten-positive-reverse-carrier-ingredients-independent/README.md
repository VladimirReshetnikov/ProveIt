# Independent review: scaled reverse-carrier ingredients

This review checks the theorem statements and selected successful author receipts for `ScaledAuxiliarySeed`, `ScaledKappaGeneric`, `ScaledOffsetGeneric`, and `ReverseCarrier`. `check.py` independently hashes current source, author runner, copied source, logs and output objects, compares pre/post receipt pins, parses each runner's hardcoded direct-import table, resolves the first object on the recorded `LEAN_PATH`, and verifies its current path and bytes. Its result and exact source, runner, receipt, object and all eight direct provider hashes are in `check-output.txt`. It did **not** invoke Lean; it reads the author's guarded receipts. Full transitive provider selection, package/dynamic-library and source-object ancestry remain inherited. Each reported theorem depends on Lean axioms `[propext, Classical.choice, Quot.sound]`; none of these reports is a syntactic proof in iPRA.

## Scope and witness dependencies

All four theorems quantify over `ORingStructure V` satisfying `IΣ₁`. Their conclusions concern elements of the **same chosen model** when instantiated; the four separate declarations have not been joined into one graph theorem.

* `TenPositiveScaledAuxiliarySeed.scaled_auxiliary`, source `research/ten-positive-scaled-auxiliary-seed-prototype/ScaledAuxiliarySeed.lean`, takes arbitrary `a,R,L`, assumes `R%4=3` and `0<tau`, and sets `c=ycoord R a`, `D=delta a`. It returns one tuple `m,i,f,T,u,y` with `L<m`, `L<f` and positive `i,T,u,y`, with `U=i*c*c`, `A=D*U*U*tau*tau`, `F=1+2*A`, `I=D*(U*(2*tau*f))`. **That same** tuple satisfies `f*f=1+A`, `xcoord (2*m) a=F`, `ycoord (2*m) a=U*(2*tau*f)`, `F*F*c*T=u+c+F*F*R`, and `I*I*u*u+y*y=1+I*I*y*y`. The proof derives positive `c` and `I≥2` and supplies the norm, exact divisibility and congruence witnesses required by the generalized auxiliary theorem. Its accepted object hash is `c6f3f4c9da7cbbf712d41d021af204e1fc7ef243838fa4c5f21d30370a152c82`.
* `TenPositiveScaledKappaGeneric.positive_kappa` assumes `X=Exp.exp R` and `X<ycoord R a`. It returns positive κ with `X*(3*C-2*X)+2=(4*a+3)*κ`, where `C=ycoord R a`. The size hypothesis establishes `2*X<3*C`, so the cast of natural subtraction is legitimate; the proof derives signed divisibility using the Pell norm and projection and transfers it back to the natural model. It does not produce the needed size bound. Object `947e0b19ed344707c91897947e6b75f2e62ca61fadbaf968e1c3d0656b5d8007`.
* `TenPositiveScaledOffsetGeneric.scaled_offset` assumes strictly positive `X`, `Y`, and `mu` and arbitrary `r`. For `P=X*(mu*Y)*(mu*Y)` and `K=2*ycoord (r+1) (2*(P-1)+1)`, it returns a natural ρ such that `K=(2*r+1)+1+(mu*mu)*ρ`. Positivity of `P` justifies its natural subtraction. No positivity of ρ is claimed. Object `0b1b5c7eddec9074d267105c57590279518d71dd545daf2f5b35c20eb1d02b8e`.
* `TenPositiveReverseCarrier.positive_carrier` assumes only `Kpos=H*κ`, `0<tau`, `0<y`, and `κ<f`. It returns a positive natural `n` with `n+κ=tau*f*y+u*u*(b*t)+t+ρ`. In the model difference ring, using `ι` for the natural embedding, it proves the exact identity

  ```text
  (ιb * ιmu * ιmu) * (ιH * (ιn - ιu*ιu*(ιb*ιt)) + ιKpos)
    - ιH * ((ιmu*ιmu)*(ιb*ιt) + ιb*((ιmu*ιmu)*ιρ))
  = (ιb*ιmu*ιmu*ιH) * (ιtau*ιf*ιy).
  ```

  The proof takes `n=total-κ`, justified positive by `κ<f≤tau*f*y≤total`; the signed identity uses the same `n` and κ. It assumes no positivity of `b`, `mu`, `H`, `Kpos`, `t`, `ρ`, or `u`. Object `614ce881139dbf86b9080fa156e87f2c84d0b19eceabc522b008f44b8c9ebbaa`.

In a future composition, κ can be constructed first from `a,R,X`, then supplied as the arbitrary bound `L` of the auxiliary theorem, producing the **same** `f` used in its Pell equations with `κ<f`; its positive `tau` and `y` then meet the generic carrier's corresponding hypotheses. The remaining parameter identifications, positivity/size conditions and graph-expression equality must still be established. In particular, the generic carrier identity is an expression in the difference ring; this packet does not itself identify it with an 80-factor, establish an 80 zero from a 90 zero, bind the external kernel coefficients, or give a syntactic iPRA proof.

The precise accepted observation paths and hashes are recorded by `check-output.txt`; attempt failures and the broader inherited boundary are described in the four author READMEs. This review did not stage or commit files.
