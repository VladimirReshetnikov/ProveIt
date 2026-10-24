# Same twelve-positive polynomial, 98 operations

The active ordinary-unit-products endpoint at ProveIt commit
`85ae4070019efd66ea3e58e9a67d287528094e8b` has twelve positive unknowns,
100 live binary arithmetic operations, and exact degree 70. The supplied
evaluator gives exactly the same polynomial in 98 operations.

This is a small arithmetic optimization, not a new semantic encoding,
variable bound, degree improvement, or novelty claim. The repository already
uses norm polarization; this note applies it to the saturated ordinary
twelve-positive evaluator.

In the unchanged parent formulas, set `d=c^4`, `e=1-Q`, `v=V+n`,
`Ea=Q*V^2-1`, `h=e*v^2+Ea`, and `b=e*Q`. Then

    (d*h+b)^2-d*Q*(2*e*v)^2 = (d*h-b)^2+4*d*b*Ea.

Indeed the difference of the two squared terms is `4*d*h*b`, and
`h-Ea=e*v^2`, so cancellation is exact in the polynomial ring over Z.
The new evaluator reuses `Ea` both in `h` and the final norm tail. All
positive zero sets, ordinary proofs, fixed coefficient bindings, and the
attained degree are therefore unchanged. The degree-70 certificate is
retained in `PARENT_PROOF.md`.

The twelve coordinates are `j,F,alpha,t,T,X,Y,r,eta,zeta,n,gamma > 0`.
The four coefficient ports are the complete compact44 tuple
`beta,K0,MC,MF`, with `beta=2^590069-1` and `MF` already shifted.
They are fixed numerals, not additional unknowns. The exact four payloads,
the finite reconstruction recipe, literal machine/tiles, whole binding and
notices are retained under `native/`; `native/ACTIVE_BINDING.json` maps
the circuit's K0 to K and MF to MF_source. These are the compact44
coefficients, separately bound from the enclosing primary twelve-integer
construction's source34 tuple. No other tuple can be substituted without
a separate calibration theorem.

Run `python3 build.py` and `python3 check.py` (Python standard library only). The checker
proves the free-register identity, matches the complete unchanged prefix,
checks live input/gate counts, and runs finite scalar transcription controls.
Neither finite tests nor identical-polynomial preservation establish the
inherited native/compiler calibration anew. `carrier.py` is an attributed
copy of the parent carrier builder. Its repository-only ancestor lookup is
delayed until the legacy CLI runs, so importing the arithmetic definitions
works at any directory depth. No carrier arithmetic is changed; the norm
schedule change is confined to `build.py`. The additional inherited arithmetic lemmas are copied under
`inherited/`; links in the unmodified parent proofs identify their original
repository locations. Source provenance and copied-file hashes are in
`PROVENANCE.json`.
