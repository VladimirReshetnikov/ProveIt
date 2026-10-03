# Review of the exact auxiliary quotient block

**PASS within the stated local model.** The [author proof](complete_auxiliary_quotient_block_scout.md)
establishes a three-multiplication, two-addition minimum for the exact polynomial
`V=c(Tf−1)−Rf²`, with independent c,T,R,f,Delta and the listed paid square ports.
Root and a separate mathematical reviewer read the entire proof and helper.
Both independently ran fresh normal and optimized receipt replays from `/`.
This note records those reviews; it does not supply a second circuit checker.

The reviewed frozen artifacts have SHA-256 values:

| Artifact | SHA-256 |
|---|---|
| [Helper](complete_auxiliary_quotient_block_scout.py) | `e447bde6b54d3f05336602af201553572defcd13c95d7602146660cd41ad2c95` |
| [Receipt](complete_auxiliary_quotient_block_scout.json) | `967b425d74dcc68472596029bf5aa986ce1546372f8b215cfdf02401b060c6bc` |
| [Proof](complete_auxiliary_quotient_block_scout.md) | `c2ca67fdc69931bad905c65fb3d3bee7db2eee50b34c89d5d442bcba8c5cd3b3` |

The two-product normal form allows arbitrary additions, paid quadratic ports,
and cancellation between intermediates. Its high-degree cases are correctly
excluded by degree, and two independent products cannot produce the missing
cTf cubic monomial even when their quartic parts cancel. In the remaining
dependent case the necessary quadratic factor has determinant 1/16 for every
choice of the two square coefficients. Thus it cannot factor into two linear
forms. The separate one-addition argument uses the irreducibility of V and
the monomial-times-binomial-power normal form. Specializing independent Delta
to zero is legitimate for this lower bound; it does not describe the actual
compiler's constrained Delta value.

The positive-gap chart is valid for the normalized parent. Its full positive
zero theorem supplies `f²−Delta*t²=1`, which forces `g=f−(a+1)t>0`; the inverse
`f=g+(a+1)t` is positive for every positive new tuple. Substituting the inverse
through the complete source gives the asserted bijection. The ordinary strong
equation differs, so extending that chart to it would require a new argument.

The helper authenticates seven predecessor files and only reads their saved
data. It verifies private consumers before each replacement, preserves every
other source row, and retains both uses of restored f: its paid square and Tf.
Exact cut identities therefore propagate to the whole polynomial, including
its finalizer. Eight complete arrays contain 692 live gates. Replays verify
384 signed evaluations, of which 192 are rational, and 32,016 retained-register
equalities. The 48 positive Pell examples check only the strong component;
they are not full positive zeros of the compiler.

Horner and flat reassociations retain the 85/86 operation counts and exact
degrees 175/131 because they compute identical polynomials. The two normalized
gap charts cost 88/91 operations; their degree claims are only upper bounds
247/241. Neither yields a new operation frontier.

The local minimum excludes additional paid core registers, algebraic relations
between actual ports, and zero-equivalent replacements. It cannot be added to
the separate auxiliary-norm lower bound to obtain a whole-circuit minimum.
The reviewed universal polynomial bound remains 85 operations; cross-block
sharing and other representations remain open.
