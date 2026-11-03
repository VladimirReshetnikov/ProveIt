# Source review: outer and auxiliary Pell seeds for compact packing

This is a **source-only** review: I did not replay Lean or independently audit
the complete provider closure. The final reviewed source
`compact44-outer-pell-seed-prototype/CompactOuterPellSeed.lean` has SHA-256
`d4a9fbfbf729dd2f44b264f29e8be215687070e4add0bdea7eb03530ce5e4963`.
I also read the repository sources for the invoked
`ArithmeticOuterSeed.outer_seed_with_size` and
`ArithmeticPellAuxiliarySeed.auxiliary_seed`, with respective SHA-256
`cc45baaa9dd7782afad29edbbcb8199926b4d2b8161ff4cb71204eda8eb897dc`
and `c20a64d1587b74dc7f18c208ba6f96052cbcfbf29da8c0e2567551055501f773`.
The already-reviewed rank/residue join has SHA-256
`82dd9d3feb27fecce93173ded53e0903208b7706223cf213567e360c97bdaf64`.
Source hashes do not independently authenticate the objects or the complete
provider ancestry used in the author's compilation.

In any `ORingStructure` model of `IΣ₁`, for any `K,N,s` and any
model-Σ₁-definable `X`, `seeds` assumes the full
`PackingInput 590069 K low high N s X` for the symbolic compact masks. It
sets `u=590069*N` and `R=rank K N s X`, and obtains positive
`sY,n,eta,zeta,gamma`, the full `SeedRelations u R sY n eta zeta gamma`, and
the size bound `sY*Exp.exp u^3 ≤ power (Exp.exp R+1) R`. It then sets
`Y=sY*Exp.exp u^3`, `a=Exp.exp R*Y+Y`, `c=ycoord R a`, and obtains
positive `f,i,T,w,y` satisfying the exact auxiliary Pell, divisibility,
quotient, absolute-difference and norm relations displayed in the theorem.
The `T` here is an auxiliary witness, not a previously supplied machine
halting time.

The construction uses `properties h` for the exact rank population and
phase. `N_pos h` and the positive width supply `0<u`. `phase_indices`
provides the odd-rank witness, so the generic outer seed's actual hypotheses
are met. The same phase supplies the generic auxiliary seed. Its parameter
`a` is exactly the outer seed's `a=E+Y`, since that seed defines
`E=Exp.exp R*Y`; its `c=ycoord R a` is exactly identified with the outer
seed's `(eta+zeta)*Y+eta` by the corresponding conjunct of `SeedRelations`.
No additional inequality, divisibility, controller or halt hypothesis is
suppressed in the source theorem. The result is conditional on the full
packing and concerns the constructed rank and symbolic masks.

The theorem does not by itself connect the rank to a calibrated halt witness,
derive the required transport quotient or adaptive gamma lift, construct a
positive zero of the exact free-J graph, bind symbolic quantities to retained
coefficient or displayed PDF bytes, or establish an iPRA derivation. The
author's successful compiler run and direct guards are separate evidence;
this review neither repeats that run nor establishes a matched paired replay
or the full transitive, package and dynamic provenance of its inputs.
