# Restricting the weakening parameter of rho8

Write the exact classical row as

```
L(A,B,C,U) = ((C→U)→A) → ((A→C)→(B→C)).
```

Two four-valued calculations give different conclusions. The first blocks
one proposed full native reduction. The second only limits a purely
propositional proof strategy; it does not settle the same restriction in
the retained native calculus.

## B=C: a model of the full restricted native calculus

Use values {0,1,2,3}, with 0 the sole designated value. Truth code zero has
value 0. Every membership atom has value 1; every equality atom also has
value 1. Thus the exact falsity code `F=R(0,0)=1` has undesignated value 1.
Every binder has the same quantifier operation Q.

| I | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 3 | 3 | 3 |
| 1 | 0 | 2 | 0 | 2 |
| 2 | 3 | 3 | 0 | 3 |
| 3 | 0 | 0 | 0 | 0 |

```
Q(0)=0,   Q(1)=Q(2)=Q(3)=3.
```

The table satisfies the exact zero alias I(0,0)=0. MP preserves the sole
designated value because row 0 has a 0 only in column 0. GEN preserves
designatedness because Q(0)=0. Exhaustive operation checks validate all
instances of `L(A,C,C,U)`, all of rho1 through rho6, merged equality G, and
the literal original seed bundle. Bundle validity is checked for every
possible matrix value, so in particular for every instance allowed by the
original gate `c≠a,b`. Its nested quantifiers and relative negations are
kept exactly; no Boolean negation assumption is imposed on this algebra.

The standalone checker evaluates the actual retained repository's
`req/clos/nks` constructor trees, copied as part of the attributed upstream
Hilbert checker. It checks 64 restricted rho8 instances and 512 evaluations
of the eight retained row constructors. The result is recorded in
`fixed_b_countermodels_receipt.json`.

To pass from the finite checks to all native proofs, define the value of a
natural code by strong recursion. At zero use value 0. At a positive code,
unpair its quotient by 4 and use its remainder tag: I uses its two recursive
values, R and E use constant value 1, and Q uses the recursive body value
and the displayed unary operation, ignoring its binder. Every recursive
formula component is strictly smaller than the positive code. The operation
equation for a native implication also holds at its exceptional zero output
because both the native zero interpretation and I(0,0) are 0.

The finite operation checks now cover every actual axiom instance. Induction
on a native proof, using MP and GEN preservation, proves that every derivable
code has value 0. The falsity code 1 has value 1 and is therefore not
derivable. The evaluation and induction are ordinary arithmetical arguments
formalizable in ZFC. No hypothesis Con(ZFC) or model of ZFC is used.

Accordingly, replacing rho8 by B=C is a **provably consistent weakened
calculus**. Assuming ZFC is consistent, it cannot have a ZFC-provable
consistency equivalence with ZFC: that equivalence together with this
consistency proof would prove Con(ZFC), contrary to the second incompleteness
theorem. This is a full native obstruction, not merely a failure of a chosen
classical semantic interpretation.

## B=truth: only a propositional obstruction

For the proposed restriction B=0, keep 0 designated and use this different
implication algebra:

| I | 0 | 1 | 2 | 3 |
|---|---:|---:|---:|---:|
| 0 | 0 | 1 | 2 | 1 |
| 1 | 0 | 0 | 2 | 0 |
| 2 | 0 | 1 | 0 | 1 |
| 3 | 2 | 2 | 2 | 2 |

It validates truth zero, I(0,0)=0, MP, and all 64 instances of
`L(A,0,C,U)`. It fails K: for example, at A=0,B=3,

```
I(A,I(B,A)) = I(0,I(3,0)) = I(0,2) = 2.
```

Thus that restricted rho8 row, truth, and the zero alias alone do not derive
K for all codes. **No Q, R, E interpretation for the remaining native rows
is supplied by this second table.** It does not rule out recovery of
classicality using the retained quantifier rows or seed theory, and it does
not establish consistency of the full B=0 replacement calculus. That
calibration remains open in this contribution.

Both tables were first located by a bounded SMT search and then checked by
`check_fixed_b_countermodels.py`, which has no SMT dependency. The discovery
search is not needed to reproduce or justify these explicit matrices. No
proof-assistant verification or machine construction is claimed here.
