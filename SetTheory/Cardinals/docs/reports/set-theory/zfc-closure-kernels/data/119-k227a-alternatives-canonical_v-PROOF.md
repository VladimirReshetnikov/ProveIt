# Canonical formula vacuity inside the retained classical bundle

## Status

This is an uncompiled source-level research result, derived before the user supplied the K230 repository. It is retained as an appendix. It is not a machine smaller than 235 states, and it is not incorporated into the K230 proof endpoint.

The new source leaves all eight original logical rows, CP, native GIC, membership vacuity, GEN/MP, the parser, and the gate unchanged. Only the equality-vacuity conjunct changes:

- old: `Eq(a,b) -> All_c Eq(a,b)`;
- new: `dec(a) -> All_a dec(a)`.

The changed occurrence still lies inside the bundle gated by `c != a` and `c != b`. Keeping rho8 is essential: its existing classicality proof permits projection of the negative conjunction before the new vacuity row is needed.

## Uniform logical comparison

For every numerical formula code m, instantiate the gate with `(a,b,c)=(m,0,m+1)`. The gate is enabled, and projection yields

`V(m): dec(m) -> All_m dec(m)`.

Thus the bundled placement supplies every canonical V instance. In particular, for `m = weq(x,y) = 4P(x,y)+3`, it supplies the exact equality helper

`Eq(x,y) -> All_{weq(x,y)} Eq(x,y)`.

The existing surgical equality-vacuity theorem in the pinned equality checkpoint therefore applies to the weaker theory embedded in this new one. If the new theory is consistent, so is the surgical theory, hence ZFC is consistent at the ordinary mathematical scope established by that checkpoint.

For the converse, every positive code m has every variable label of `dec(m)` strictly below m. This follows by induction on m: the unpaired fields are at most floor(m/4), all positive formula children are smaller than m, and the special zero child contains only label 0. Consequently canonical V is an ordinary valid vacuity instance for m>0. For m=0 the native decoder gives the truth alias `F -> F`; its universally quantified version is a theorem at every binder, including binder 0. Thus V(0) is derivable as well. All new rows are theorems of the original calibrated calculus, so ZFC consistency implies consistency of the new theory.

The same argument works with the scalar b or c used throughout the new V row. For V(b), use `(a,b,c)=(0,m,m+1)`; for V(c), use `(a,b,c)=(m+1,m+1,m)`.

## Exact source construction

Against the 235 source SHA-256 `c17ab40e032e79dca03eaa955a78dbcd65bd030795ecc232dc504aff1551cb20`, replace three closed subtrees at:

1. `111010010011011011111`: the first Eq(a,b) scalar builder, 82 primitive occurrences;
2. `1110100100110111000`: scalar c push, 26 primitive occurrences;
3. `1110100100110111001`: the second Eq(a,b) scalar builder, 82 primitive occurrences.

Replace each by the existing 26-primitive a-push subtree at `111010010011011011111000`. Every source path outside these three subtrees stays literal-identical. The surrounding All and implication builders remain intact. The builder records the before/after trees and boundaries.

The source loses 112 primitive occurrences, from 6,455 to 6,343. Maximum zero run stays 6 and maximum depth stays 48. Its unoptimized hash-consed tree has 225 nodes, versus 224 in the baseline: the shorter macro word does not by itself imply fewer binary states. The scalar-b and scalar-c alternatives have the same counts.

## Remaining implementation boundary

An exact macro-level AX binding and parser completeness proof can follow the ordinary source-binding argument in the equality checkpoint: the row count and parser arity have not changed, and every source slice outside the three closed pushes is retained. The present builder does not replay that entire binding. A modified literal binary table, its runtime invariant, and a newly compiled proof-assistant endpoint have not been supplied.

Source: the supplied `zfc_equality_reduction_20261019/source.tex`, Sections 2, 10 and Appendix B, plus `source_binding/ORDINARY_PROOF.md`. These are the existing equality theorem and source-binding inputs, not newly proved Lean declarations.
