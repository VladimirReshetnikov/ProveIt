# Checked affine source equivalence for the 443-operation branch

[`GapSource66.lean`](Lean/DiophantineConsistency/GapSource66.lean) formalizes
the source-coordinate change used by package 66's H2082 layout and the
separate [`gap2082-compact54`](candidates/gap2082-compact54/README.md) candidate.
It defines the 22 literal new rows independently from the pinned 85-record
source JSON, SHA256
`e4f50dbede42c421defa2d7d36268413351dd1e023763c584ea34f3b9a827957`.
The old source is the authoritative old-z source already bound by
`SplitCertificate59`, SHA256
`1c336ba0b3c9827ffddcf7ce895cad9dca2907f907cde7484c7f387bb2cb1287`.

The explicit maps change only two coordinates:

```
q = beta*J+1
toOld:   P_old=P_new+eta+zeta,  N_old=N_new+q
fromOld: P_new=P_old-eta-zeta,  N_new=N_old-q.
```

The transport coordinate is retained exactly. `fromOld_toOld` and
`toOld_fromOld` prove that these are inverse maps over every commutative
ring. Each of 22 scalar identities is checked separately, with an explicit
scalar `change` before reducing the finite-vector definitions. They identify
the new rows with the old transformed rows: `rho14=r14+r2` and
`rho15=r15+r3`. The existing inverse-shear theorem then proves the exact
common-zero correspondence in `zero_iff_toOld` and `zero_iff_fromOld`.

The positive domain requires more than those polynomial identities.
`old_positive_gaps` uses only old rows 0, 1, 3, 5, and 6, positive source
coordinates, and `beta>0`. The defining equations give

```
a-E = s*N > 0
c-eta = (eta+zeta)*(a-E) > 0
P_old-eta-zeta = E*(c-eta) > 0
N_old = q^3,  q>1,  N_old-q = q*(q^2-1) > 0.
```

Thus `fromOld_positive` is proved before any Pell classification, native
rank bootstrap, compiler interpretation, or calibration. Restoring the
old coordinates is positive directly. `positiveZeroEquiv` supplies an
explicit equivalence between the entire positive common-zero subtypes;
its forward and inverse functions are the literal affine maps, with no
choice of witnesses. `exists_positive_zero_iff` is its existence version.
`exists_positive_nat_zero_iff` exports the same result on positive natural
tuples with integer evaluation, so the old-source arithmetic APIs can be
applied to the new branch.

[`generate_gap_source66.py`](tools/generate_gap_source66.py) regenerates the
literal rows and their scalar identities from the SHA-pinned inert source
and parent files. It reuses the existing repository's expression printer.
Lean checks the generated identities; the generator is outside the
mathematical trust boundary. The frozen candidate and delivered package 66
are unchanged.

Regression checks preserve the transport coordinate, expose both new gap
coordinates, and show why inverse positivity cannot be asserted for an
arbitrary positive tuple: the all-one tuple maps to inverse gaps -1.
The changed N-q row is also checked at that boundary. Main module and
regressions pass; all ten audited declarations use only Lean's standard
axioms. This module closes the elementary affine source bridge. It does
not prove the new literal circuit, its kernel extraction certificate, native
payload calibration, or an internal object-language ZFC equivalence.
