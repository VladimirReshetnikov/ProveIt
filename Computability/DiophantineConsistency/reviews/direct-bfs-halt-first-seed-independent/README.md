# Independent review: direct-BFS halt to first-carrier seed

For any `ORingStructure V` model of IΣ₁, `DirectBFSHaltFirstSeed.halt_first_seed` takes an arbitrary model time `T` and assumes only `ArithmeticCantor.first (ArithmeticMachineRun215.run T)=0`. It supplies one Σ₁-definable Boolean pulse `δ` with the stated nonzero-support bounds and the same canonical word `X := cellWord (row T) δ` in its packing, definability, calibrated rank, seed and transport conclusions. The remaining statements are under a quantified Σ₁-function instance for that same `X`, whose existence is separately returned in the conjunction.

With `N=length T`, `s=stride T`, direct-BFS symbolic `K=kernel`, `u=590069*N`, `R=rank K N s X`, `q=Exp.exp u` and `w=Exp.exp (R−u)`, the theorem gives the rank congruence and a positive `z` with `q*w=Exp.exp R` and `(K+w)*C=F+z*(q−1)`, where `C=Cw 590069 N X` and `F=Fw 590069 K N s X`. It then gives **one** positive tuple `sY,n,eta,zeta,gamma` with the same `SeedRelations u R ...`, size bound and `AuxData u R sY` as the prior Pell-seed theorem. `FirstData` uses that same tuple and the **same** transport `z`; it does not introduce an independent transport witness.

Precisely, `FirstData` defines `Y=sY*q³`, `E=Exp.exp R*Y`, `k=eta+zeta`, `ell=E*Y*k`, and model-natural truncated `tau=E*n+k−R`. It asserts

```
(q*K+Exp.exp R)*C = q*F+(q−1)*(q*z),
∃ r>0, (q³*(q−1))*(ell+k+r)+Y*(q−1)
         = (q³*(q−1))*tau+(1+(q−1)*k)*q³*((q−1)*(q*z)).
```

The proof unpacks the one pulse, transport `z`, seed tuple and auxiliary data from the independently reviewed halt-Pell-seed theorem, and applies `CompactFirstTransportSeed.first_from_transport` using the same packing, `sY,n,eta,zeta,gamma`, `w` and `z`. `AuxData` contains its own existential variables named `T` and `w`; these are locally bound auxiliary coordinates, distinct from the external halt time and the separately defined transport `w`. The first-carrier `tau` here is an expression; the conclusion does not assert a separate `tau>0` premise.

This theorem is not yet a construction of a graph valuation, a graph/model equivalence, an external coefficient-file equality or iPRA derivability. It uses the direct-BFS symbolic kernel, not the distinct original-order symbolic kernel.

`check.py` rehashes the source/copies, runner, Lean binary, selected direct providers, object and logs; verifies both recorded direct-import snapshots and first resolution; and rehashes 59 chunk receipts. The direct objects are reviewed `DirectBFSHaltPellSeed` `8d9892b6ff938f9766c042609e1a4bdd78da4769b6b2bd946fb7c275ddcd7762` and `CompactFirstTransportSeed` `0361b27d675a978705be3e5a4ecda7191acf249e4e4625d7db3cff3182040ca5`; the endpoint object is `0b2e073e622c771e5c52a0ef1ef6ceeaeb69c6c402451d076a6479c70fe82fd4`. Its named axiom report is exactly `[propext, Classical.choice, Quot.sound]`, with empty stderr; the runner enforces the named whitelist and rejects coded diagnostics. The terminal precedes final assertions; the author reports outer exit 0 but no separately retained actual outer-exit receipt was found. No Lean replay or full historical/project/package/dynamic producer audit was performed.
