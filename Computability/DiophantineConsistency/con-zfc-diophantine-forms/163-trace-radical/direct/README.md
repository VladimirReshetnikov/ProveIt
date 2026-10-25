# Direct C222 quartics by simultaneous quadratic-radical projection

Prepared for Vladimir Reshetnikov and ProveIt, 25 October 2026, with AI assistance.

Each listed equation is the sum of the squares of all residuals in its
`equation.json`. The domain is **unrestricted integers**. All coefficients
are fixed, explicit integers. A residual term `[c,[i,j,...]]` means
`c*x_i*x_j*...`; an empty list denotes a constant. Repeated indices are
repeated factors. Every residual has degree at most two.

| Endpoint | Variables | Residuals | Degree | Collected monomials | Height |
|---|---:|---:|---:|---:|---:|
| `equations/self_power236` | 236 | 172 | 4 | 4,992 | 10,722 |
| `equations/self_power235` | 235 | 171 | 4 | 10,536 | 10,730 |
| `equations/shared_error234` | 234 | 171 | 4 | 21,385 | 44,800 |

The first two change the inherited factorial-free growth base from
`2(t+1)` to `t`, giving the simpler proof-label size parameter `F=t^t`.
The third retains the prior shared-factorial-error semantics unchanged.
All three then remove six coordinates by integral shears along directions
in the common kernel of all quadratic Hessians, followed by monic
quadratic substitutions. Each of these six final steps is a bijection of
integer zero sets. No extra unquantified coefficient or integer search
appears in the delivered polynomial.

By the ordinary proofs in `PROOF.md` and the identified inherited C222,
Pell, CRT, and syntactic-refutation calibrations, ZFC proves that each
equation has an integer zero if and only if a finite ZFC refutation exists.
Negating gives the requested equivalence with Con(ZFC). This is an
ordinary proof formalizable in ZFC, not a newly compiled end-to-end
Lean/Rocq development or an encoded object-language ZFC derivation.

The 234-coordinate point improves the dimension of its 240-coordinate
matched source; coefficient height increases. The sparse 236-coordinate
point is a different semantic branch and trades one extra coordinate for
much smaller support than 235. The repository also has few-variable
constructions with large fixed coefficients. No global simplicity minimum
or literature-wide priority claim is made.

## New arithmetic and algebra

For a certificate with at most `t` conclusions and labels in `[0,t]`,
the evaluation point `F=t^t` already authenticates the complete label
multiset. The original proof used the stronger `F>(t+1)^t`. The refined
coefficient-by-coefficient argument is proved in `PROOF.md`; zero labels
and unequal factor counts are explicitly covered. Completeness selects an
even horizon from the existing cofinal family `t=16+h^2`, preserving the
required 2-adic divisibility and every subsequent parity construction.

For quadratic residuals `f_r=c_r+L_r+Q_r`, a common Hessian-kernel
direction `d` satisfies `f_r(x+s*d)=f_r(x)+s*L_r(d)`. When a coordinate
of `d` and one row slope are units, integral triangular shears expose a
monic coordinate. This combines several graph wires that occur only
through the same quadratic linear combinations. No division by a
nonunit, positivity assumption, or saturation step is used.

Every final simultaneous Hessian has full column rank over the field with
101 elements. The supplied rank certificates therefore prove that its
common kernel over the rationals is zero. This only rules out further
projection by this particular simultaneous-radical mechanism in the
current charts; it is not a lower bound for arbitrary constructions.

## Verify and reconstruct

Python 3.10 or later and its standard library suffice.

```sh
python3 -B code/verify.py --full
python3 -B -O code/verify.py --full
python3 -B code/rebuild.py
```

The independent new checker uses exponent-pair monomials rather than the
producer's repeated-index implementation. It checks the literal source
edit; inherited Horn identities and projection certificates; all affine
maps; every new common-radical direction, shear inverse, monic restoration
and coordinate map; every collected quartic coefficient; all exact
metrics; and terminal finite-field rank certificates. Five deliberately
corrupted new artifacts must be rejected.

`--full` also invokes scoped, retained predecessor checkers. The bundled
predecessors are dependency subsets: historical PDFs and temporary visual
files are omitted, so their old whole-release manifests are documentary
records, not entry points for this release. The new driver and root
manifest are authoritative for the delivered subset. Full proof-assistant
dependency trees were not rebuilt. Finite checks support the literal
artifacts; they do not replace unbounded mathematical proofs.

`code/rebuild.py` uses a disposable copy, rebuilds the self-power source,
replays the fixed affine maps, recomputes the common-radical reductions,
and compares all selected mathematical JSON files byte for byte. Original
files are left unchanged. `code/evaluate.py ENDPOINT tuple.json` evaluates
one concrete integer tuple exactly; it is not a solver for existential
solvability.

## Provenance

The inspected repository is ProveIt commit
`b7e35224c04fe1031c0a53f80a395e9b32205022`.
The immediate prior archives are the incoming
`ConZFC_Factorial_Free_Binomial_CRT_2026-10-25.zip` and
`ConZFC_Shared_Factorial_Error_2026-10-25.zip`.
Their exact archive hashes, inspected source identities, retained-file
hashes, and licenses are included. The underlying numerical proof calculus
and source compiler are credited to ProveIt and the named predecessor
packages. This component does not use K215 simulation or Jones's universal
polynomial.

The mathematical interfaces inherited at the logical endpoint are
`KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`, as documented in
the retained source proofs. The primary novelty is the measured new
composition and the explicit projection certificates, not a new claim
about those inherited interfaces.
