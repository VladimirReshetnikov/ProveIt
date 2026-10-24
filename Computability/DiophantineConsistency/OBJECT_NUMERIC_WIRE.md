# Literal checker primitives over the entire internal omega

This checkpoint extends the internal sharp pairing bijection to the actual
predecessor, tree projections and zero-test quartics already used by the
direct checker's shared-register graph. These are statements about all
internal naturals of any `ZFAxioms` model, including nonstandard elements.
External `Nat` correctness is not used as a transfer principle.

`ObjectQuadraticSystem` interprets the residual sum of squares of any
supplied shared-register quadratic system. It proves exact conjunction
semantics, preserves instantiated port maps, and removes the empty register
block of a gate-free system by a literal expression rename. Its
`inputExpression_degree` proves degree at most four for the stored result.
The generic theorem says that all residuals vanish; it does not assume that
arbitrary stored registers already contain their intended values.

`ObjectPredecessor` constructs predecessor on the internal carrier from
zero/successor decomposition and proves the exact two-row certificate

```
n*(out+1) = n*n,     out*(out+1) = out*n.
```

These equations force `out=pred(n)`, including the branch `n=0`.
`ObjectPredecessorSyntax` binds this certificate to the actual two
`QuadraticTreeCodeGraphs.predRows` and their stored sum-of-squares expression.
Its quartic uses the two visible coordinates and no auxiliary coordinate.
The displayed object graph has exact semantics, and its totality sentence
has an unconditional derivation in the existing sealed ZFC calculus.

`ObjectNumericWire` supplies the exact predecessor/unpair tree operations
and successor-pair list constructor on all internal codes. It checks the
atom/fork equations, zero-or-cons decomposition and cons injectivity.
The guarded list head maps a found value `a` to `a+1`, while nil maps to
zero; list tail handles nil separately. The tree projections agree with
the actual external checker's operations at every numeral input.

`ObjectTreeCodeSyntax` uses the actual preallocated seven-coordinate
`leftSystem` and `rightSystem`, with their original port maps. It proves
that each stored quartic represents its corresponding tree projection,
with exactly five existential internal-natural auxiliary coordinates.
Both soundness and completeness cover every internal input and output,
including zero. The polynomial degree is at most four.

`ObjectZeroTest` binds the actual three zero-test rows to their natural-part
equalities. Its Boolean row forces the bit to be zero or one over the
entire internal carrier. The resulting literal quartic has one auxiliary
coordinate and represents `bit = if n=0 then 1 else 0`. Completeness chooses
the internal predecessor as the positivity slack, including at zero.

The dedicated check file imports these actual expressions, checks their
universal semantics and audits their dependency axioms. These results do
not complete the full checker interpretation. Internal formula/context
coding, bounded scanner execution, axiom dispatch and correspondence with
the chosen internal proof-code consistency sentence remain required.
