# Literal current object-language equation: author receipt

This packet supplies the current fourteen-variable polynomial as finite
integer expression syntax, shifts its positive domain to natural variables,
and defines its closed set-theory no-solution sentence. Its semantics ranges
over every internal natural tuple of an arbitrary model, including
nonstandard tuples. It does **not** prove that this sentence is internally
equivalent to the model's consistency statement.

This is an author receipt by the circuit-reduction agent. No independent
review is claimed here. Existing mathematical sources, displayed equation,
dependency objects, and shared documentation were not modified.

## Frozen files and fresh checks

Paths below are relative to `Computability/DiophantineConsistency/`.

| File | Lines | SHA-256 |
| --- | ---: | --- |
| `Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean` | 218 | `897872f31299a8faddbf1eee65c4e029d238ad47957e8c5f6cab68ff0b04ea8c` |
| `Lean/DiophantineConsistency/ObjectCurrentEquation2011Checks.lean` | 81 | `a3d9e87b83ba4a1a6bb5b8ce874ff2c0d7303ac3dabc24109edcf41be84a0db1` |

Both final sources were read completely. Both direct fresh builds passed
with `lean -M6000 -j1`; the sources set `Elab.async false`. The final main
log is empty. The checks report ten axiom audits containing only
`propext`, `Classical.choice`, and `Quot.sound` as applicable. There are no
`sorry`, new axioms, or `native_decide` calls. No resource caps were raised.

```sh
lake env bash -c 'export LEAN_PATH="/tmp/object-current-deps-_hgxk1r0:$LEAN_PATH"; lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ObjectCurrentEquation2011.lean -o /tmp/object-current-deps-_hgxk1r0/DiophantineConsistency/ObjectCurrentEquation2011.olean'
lake env bash -c 'export LEAN_PATH="/tmp/object-current-deps-_hgxk1r0:$LEAN_PATH"; lean -M6000 -j1 Computability/DiophantineConsistency/Lean/DiophantineConsistency/ObjectCurrentEquation2011Checks.lean -o /tmp/object-current-deps-_hgxk1r0/DiophantineConsistency/ObjectCurrentEquation2011Checks.olean'
```

The main object hash is
`51fd52822cf4f819afef683820c453dd53c370fe5084a4533362ff9c918d1b45`;
the checks object hash is
`b6c0a2d4c2803cf5d31e87a115d32388450aef83028842e09bec1bc5afa6a2a5`.
They remain in the private overlay. The final logs are
`/tmp/object-current-main-stage5.log` and
`/tmp/object-current-checks-stage2.log`; their hashes, exact commands,
dependency sources, object hashes, and preparation drivers are preserved in
`reviews/object-current-equation2011-dependency-replay.json`, SHA-256
`afdd946ecf76e6c31da7badf138fffc378080b82f0c2e66b8e33b5fd059edddd`.

## Literal polynomial and domain binding

`expressionAt p` mirrors every let block of `Carrier65.core` and its final
`P*Q*U*W*Z-delta`, with independent coordinate order
`J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma` and the four ports
`beta,K,MC,MF_source`. The four integers are constant leaves; neither their
binary expansion nor the eventual split-natural tree is materialized.

The generic `evalRing_expressionAt` works in every commutative ring.
Specializing it in the multivariate polynomial ring proves
`polynomial_expressionAt`, an equality of the entire polynomials rather
than merely their zero sets. `expression` specializes the ports to exactly
`CurrentWindowCarry2011.ports`; `polynomial_expression` identifies it with
`CurrentPolynomialWindow2011.polynomial`.

The focused checks explicitly bind width 94517 and every port. In
particular the fourth port is the natural sum `highPort+beta` cast to the
integers, retaining exactly one source-mask shift. The literal source pins
are:

| Source | SHA-256 |
| --- | --- |
| `Carrier65.lean` | `be2f2cb6833d190818541a57bb9b7c148c5975864d6af518f511b67f80fb1154` |
| `CurrentMasks2011.lean` | `72ec99ac052c4d244f22f2590fb5645cebbe9ffe3a18fd89fe1cb8db7248fe06` |
| `CurrentKernel2011.lean` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| `CurrentWindowCarry2011.lean` | `94f9ec318d90b66200757bba8992eb6560e283dbdceeac877e48eee80ade3d06` |
| `CurrentPolynomialWindow2011.lean` | `db64a1e9130d09d606f3262781be9a4c0d70db1a9cdb7482cd74ecc0ddf0b730` |

`naturalExpression` substitutes `var i+1` for each of the fourteen original
variables. `eval_naturalExpression` proves its exact evaluation, while
`natural_zero_iff_positive_zero` gives both directions between natural
zeros of the shifted expression and the actual positive integer zeros.
The reverse direction explicitly uses `(v i-1).toNat`; positivity proves
that no truncation is lost. Small controls check that the shift changes
zero to one and that a negative coefficient is retained by the natural
balance interpretation.

## Arbitrary-model semantics

The generic `split_positiveShift` is proved by induction on expression
syntax over any commutative semiring. It commutes the entire positive and
negative natural-expression pair with the substitution. Thus the proof
does not unfold millions of nodes of the specialized split-natural tree.

`internal_positive_iff_successor` applies the previously proved discrete
order theorem on `ObjectOmegaSemiring.Natural H`. Every strictly positive
internal natural, not just an external numeral, has an internal predecessor.
`no_shifted_zero_iff_positive` applies this to every coordinate.

`unsolvabilitySentence` is exactly
`ObjectPolynomial.noZeroForm naturalExpression`, and
`sentence_unsolvabilitySentence` proves it closed. The principal semantic
theorem is:

```
sat_unsolvabilitySentence_iff (H : ZFAxioms mem) :
  (forall ee, Sat mem ee unsolvabilitySentence) <->
  forall v : Fin 14 -> Natural H,
    (forall i, 0 < v i) -> not (InternalZero expression v).
```

`InternalZero` is equality of the two natural-coefficient sides of the
literal signed expression. `equationRel_numerals_iff` additionally checks
the exact current polynomial on standard shifted tuples, and
`no_positive_zero_of_sat` derives the external no-positive-zero consequence.
There is deliberately no converse from only standard tuples to all-model
satisfaction, and no `ConZFC`, machine, or refutation hypothesis in any of
these semantic statements.

## Dependency provenance and scope

The object-language custom import closure has 45 modules. The final overlay
uses 19 existing shared objects, 20 missing objects copied from the 62ff cache
only after byte-for-byte source and toolchain/manifest comparison, and six
fresh current-source builds:

1. `ObjectPolynomial`;
2. `ObjectNaturalSemiring`;
3. `SyntaxCoefficients`;
4. `QuarticSyntax`;
5. `ObjectResidualSquares`;
6. `ObjectNaturalDiscrete`.

Every fresh source and preparation driver was read before execution. An
upstream merge changed two proof sources during development; the entire
affected six-module portion was then freshly rebuilt from the final merged
snapshot. The final object-language source hashes were rechecked at freeze.
The superseded pre-merge overlay is recorded, not used by the final builds.

The separate native import side reuses previously accepted objects, with
root's explicit authorization and exact object pins. Its current source
graph has 91 custom modules; `QuadraticFiber` and `TotalDegreeBound` are new
source-graph dependencies absent from that previously accepted object
closure. Their absence is recorded. **This receipt does not claim a fresh
current-source replay of the whole native chain.** Another agent owns that
post-merge closure refresh. All actual sources and reused object hashes in
the recorded snapshot were checked again at this packet's freeze. No
existing shared object was overwritten, and no absent native dependency was
silently supplied.

Early authoring failures were limited to numeral-cast simplification, one
namespace name, and elaboration unfolding of a closed large expression.
The final source uses generic shift identities and local irreducibility to
avoid that expansion. The completed packet makes no new operation-count,
degree, optimality, or internal consistency-equivalence claim.
