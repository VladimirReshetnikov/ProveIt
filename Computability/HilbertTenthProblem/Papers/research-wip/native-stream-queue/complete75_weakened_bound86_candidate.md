# Refuted86-operation weakened-bound proposal

**REFUTED on actual compiled program slices.** The
[all-input collapse theorem](complete75_weakened86_all_input_collapse.md)
proves that the unchanged86=48M+38A polynomial, with19 positive supplied
coordinates and exact degree203, has infinitely many complete positive
zeros at every positive input for every actual modified compiler slice.
The [explicit rejecting compiler](complete75_weakened86_rejecting_compiler.md)
has empty language and therefore gives a false positive at x=1.

This refutes this particular weakening, not the possibility of a different
86-operation universal polynomial. The established75 certificate and
[normalized87 polynomial](complete75_normalized_strong87.md) are unchanged.
The proofs specify exact finite compiler and Pell recipes; huge constants
and full witness integers need not be materialized for the existence result.

The [source](complete75_weakened_bound86_candidate.py) and
[receipt](complete75_weakened_bound86_candidate.json) retain the original
arithmetic circuit. The following signed parent identity, conditional
positive inverse and outer-only obstruction remain valid historical
results. Their original fixtures are not full zeros; the later theorem
supplies the complete false-input witnesses.

## 1. The literal saving and exact signed identity

Retain all normalized87 coordinates and constants, both ratio slacks,
the complete normalized strong factor, positive F, and the ordinary input
norm. Write `T=q-F`. The parent evaluates

    V=T-Z, C=V-alpha_old-2d*x, W=C-Z,
    G=(q-1)*T+V=q*(q-F)-Z.

The candidate instead evaluates

    C=T-alpha-2d*x, W=C-Z,
    G=q*T-Z.

The ordinary input-width subtraction `2d*x` remains. Only the *additional
strengthening by Z* in the bound is removed. The packed index is still
the same literal expression in G, q and the compiler masks:

    R=G*(q^2-1)+(MC+q*(MF+B-1))*J.

In this formula MC and MF are the original masks. The historical source
adapter replaces its register constant MF by `MF+B-1`; the checker uses
that exact convention.

The private register `q_minus_FZ` has only two consumers. Delete it,
feed `q_minus_F` into `C_after_alpha`, and replace the two packing gates
by `gap_product=q*q_minus_F`, `gap=gap_product-Z`. The source loses
one addition/subtraction and no multiplication. All other 82 gates in
the parent certificate remain literal rows; three retained rows change.
The candidate certificate has 85=48M+37A and one comparison, followed by
the final subtraction giving 86 operations.

For arbitrary integer supplied values there is the exact identity

    P_candidate(x,...,alpha,...,Z,...)
      = P_87(x,...,alpha-Z,...,Z,...).

Each of the eight individual factors agrees under this substitution,
not merely the final product. Topological reordering, hidden divisions
or extra comparisons are not needed.

## 2. What follows positively, and what does not

Starting with a positive parent tuple, set

    alpha_candidate=alpha_old+Z.

This is positive and preserves the complete polynomial value. Hence
every input accepted by the universal87 construction has a positive
candidate zero. It also proves equality of the two positive projections
when candidate tuples are restricted by `alpha>Z`: the inverse
`alpha_old=alpha-Z` is then strictly positive and all other coordinates
are unchanged.

The candidate source does **not** impose that restriction. If
`0<alpha<=Z`, its exact parent image has a nonpositive supplied alpha,
so the parent positive theorem cannot be invoked. Neither the signed
polynomial identity nor canonical completeness fills this gap. The later
all-input theorem proves that false accepted inputs do occur in this
region on actual compiler slices.

The earlier [bounded projection](complete75_bounded_projection_elimination99.md)
uses the extra Z in C to infer `F,Z<q` after transport gives C>0. This
makes G positive and restores a positive packed index before applying
the native theorem. With the weaker C definition, C>0 bounds F but
does not bound Z. The next family shows that the remaining outer
transport and input-width expressions alone do not repair this loss.

## 3. A positive outer family with negative packed index

Take the following positive scalar data:

    B=q=16, J=1, d=4, x=1, F=1, alpha=3,
    w=11, DC=3, DR=5, MC=10, MF=12,
    zplus=12038, Z=265+4j,  j>=0.

Set every other supplied coordinate to one. The masks satisfy
`MC=2 mod4`, `MF=4 mod8`, and
`popcount(MC)+popcount(MF)=4`. This statement concerns those scalar mask
conditions, not an assertion that DC and DR instantiate a particular
exported universal program.

Direct evaluation of the actual candidate source gives

    C=4, X=w*q^3=45056, K0=DC+B*DR=83,
    (K0+X)*C+q-F-zplus*(q-1)=1,
    G=-25-4j, mask=(10+16*27)*1=442,
    R=-5933-1020j<0, R=3 mod4,
    alpha_old=alpha-Z=-262-4j<0.

Thus even the exact positive transport unit, a positive C and all the
retained outer supplied coordinates permit an arbitrarily negative R.
The transport coefficient is `K0+X`, with X=wq^3; replacing X by an
already typed exponential in R before establishing the native hypotheses
would be circular.

These fixtures do not satisfy the full native norms. The receipt checks
that their complete candidate polynomial is nonzero. Accordingly the
family refutes only the old proposed bootstrap, and supplies no full
counterexample or lower bound. The later all-input collapse resolves
soundness negatively using full positive zeros in the R<0,mu<0 branch.

## 4. Degree and replay

The signed substitution is linear. The parent's exact highest form stays
nonzero after replacing its

    C_top=(B-1)J-F-Z-alpha_old-2d*x

by `(B-1)J-F-alpha-2d*x`. All eight factor degrees remain
`14,22,42,64,9,5,38,9`, so the exact total degree remains 203. This is a
degree assertion about the candidate circuit, not a universality claim.

The checker audits the private consumers, literal M/A counts and unique
topological register order. It compares every factor and the full
polynomial under the exact substitution on 512 assignments, including
128 signed cases; 384 positive cases also check the forward map. It
tests both positive and nonpositive inverse-alpha regions, three exact
weighted degree/highest-coefficient specializations, and 64 members of
the outer family above.

```sh
/tmp/diophantine-research-venv/bin/python complete75_weakened_bound86_candidate.py
```

Author receipt generation and fresh default replay pass. No parent packet or navigation file
is changed. This original bounded result preserved a concrete candidate and its
then-missing implication. The later refutation establishes no improvement below87.

Independent scoped proof/source review and fresh default replay pass
without findings. A separate literal executor verified 192 signed
eight-factor/full-output identities at B=16,32,128,512 under the exact
alpha-Z substitution. The review confirms only the stated conditional
projection and outer obstruction, not full candidate soundness.

The subsequent [positive-index theorem](complete75_weakened86_positive_index.md)
extends conditional soundness to every candidate zero with computed R>0,
including alpha<=Z. It proves R=0 impossible and supplies necessary
restrictions in the R<0 branch. The subsequent all-input theorem proves
that this specific proposal is unsound on actual compiler slices.
