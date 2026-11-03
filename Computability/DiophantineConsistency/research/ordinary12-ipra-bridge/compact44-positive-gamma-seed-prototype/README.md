# Positive adaptive gamma from the exact compact seed

`CompactPositiveGammaSeed.positive_gamma` constructs the positive adaptive
graph coordinate from a *given* outer seed, without selecting another one.
It works in every model of `IΣ₁`, for a model-Σ₁-definable `X`, from:

- the full symbolic compact `PackingInput` for `K,N,s,X`;
- particular outer-seed parameters `sY,n,eta,zeta,gammaOld`, with
  `sY>0`, `gammaOld>0` and the exact `SeedRelations` at the constructed
  rank `R` and `u=590069*N`; and
- a particular `w` satisfying `Exp.exp R = Exp.exp u*w`.

The last equality is supplied by the positive shifted-transport conclusion
of `CompactHaltPellTransport`. With `q=Exp.exp u` and `Y=sY*q^3`, the
client proves

```
∃ t gamma, 0 < gamma ∧
  eta+zeta = R+1+(Y*q^2)*t ∧ gamma+w = gammaOld+t.
```

The theorem requires positivity only of `gamma`, not of `t`. It uses the
packing to obtain `R % 4 = 3`, then applies the generic
`ArithmeticAdaptiveConstructionCorrectionSeed2011.positive_correction_of_seed`.
Despite its module name, that theorem and the three sources rebuilt with it
contain no 2011-specific masks or numeric width. The underlying argument
uses the outer seed's Pell ordinate to obtain the exact quotient, proves it
large enough to cover `w`, and constructs the strictly positive natural
`gamma=gammaOld+t-w`. No gamma witness, divisibility assumption or positivity
of `w` is added to the statement. All seed variables are explicit inputs, so
this theorem applies pointwise to the same seed used by a first-carrier
construction. The graph-evaluation identity for this gamma, complete positive
graph valuation, retained-byte/PDF binding and iPRA derivation remain
separate tasks.

The four exact source files in `observations/rebuild-attempt02` were rebuilt
in dependency order against the compact seed project overlay. All four Lean
children actually exited 0. Their exact source snapshots, hashes, compiler
logs, direct dependency/companion guards and provider inventory are retained
there. The preflight also checked the selected fallback project overlaps for
conflicts. `rebuild-attempt01` stopped before any Lean compilation because a
runner typo pointed to a nonexistent provider; attempt02 corrected the path.

The compact client single-author `observations/attempt01` then actually
exited 0 without warnings or `sorryAx`. The named Lean axiom report contains
exactly `[propext, Classical.choice, Quot.sound]`, which are metatheory
assumptions rather than axioms added to the encoded object theory. Its source
SHA-256 is
`13dc3c1e4b78ea42a15f9d6e17bebcbf37336d9ac038fd21ee6450b86072774d`; its
object SHA-256 is
`a314435319e56f5f97104443ec6a742da3fcf151f5008547b49c18dea6dc2386`.
The gamma-rebuild and seed project overlays had 539 matching file names, and
the seed and halt overlays had 531 matching names, at preflight. Direct
imports and companions, selected project inventories and other recorded
roots were unchanged at the final checks; full records are retained.

These are mixed-provider, single-author exploratory builds. Point-in-time
guards and comparisons do not authenticate the full transitive, package or
dynamic ancestry, establish continuous filesystem/resource monitoring,
or constitute a matched paired replay or independent artifact audit.
