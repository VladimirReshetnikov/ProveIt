# A conditional two-operation coordinate tradeoff

**This is not a valid smaller consistency equation.** The rewritten graph
has fewer binary operations, but an equivalence for unrestricted positive
inputs has not been proved. In particular, two strict inequalities needed
to recover the old positive coordinates are not enforced by the graph.
An [independently reviewed symbolic counterexample](../double-gap-uniform-counterexample/README.md)
shows that the reverse inequalities fail for a positive zero at auxiliary
ports with `beta = 0`; it does not settle the actual fixed-port case.

Write the old coordinates and shared quantities as

```text
q = 1 + βJ,  h = q−F,  C = q−F−α,
q2 = q²,  g28 = Fq,  G = α + h(q−1).
```

Replace the two inputs `F, α` by two inputs `h, C`, so the inverse change is
`F=q−h` and `α=h−C`. Delete the old rows defining `h` and `C`; move the
shared row `g44=q·h` before `g28`, and use

```text
g28 = q2 − g44
G   = g44 − C.
```

The two local identities are exact in every commutative ring:

```text
(q−h)q = q²−qh
(h−C)+h(q−1) = qh−C.
```

The old inputs `F` and `α` occur only in the replaced rows. Every other row
is unchanged, so induction through the graph gives the exact original output
after the displayed substitution, for arbitrary integer inputs and ports.
Both rewritten DAGs retain 13 live input coordinates and four live ports:

| Parent | Original operations | Conditional rewrite | New `× / + / −` |
| --- | ---: | ---: | --- |
| Sum of squares | 87 | 85 | 47 / 20 / 18 |
| Product | 86 | 84 | 46 / 20 / 18 |

There is an exact positive-domain bijection **with conditions**. Old positive
tuples for which the computed `C` is also positive map to positive new tuples
with `q>h>C>0`; the inverse recovers positive `F=q−h` and `α=h−C`. The
rewritten graph requires only positive input coordinates, however. Its
positive zeros have not been shown to satisfy either `h<q` or `C<h`. For
example, with `q=2`, the positive pairs `(h,C)=(3,1)` and `(1,2)` separately
violate those bounds. These are domain examples, not asserted zeros.

After fixing `β` as an integer, the replacement is an invertible affine
change of the 13 variables, with integer inverse. It therefore preserves
total degree exactly, as does the later positive shift. With all four ports
fixed as in the existing certificates, the parent degrees 36 and 56 are
unchanged. No corresponding degree conclusion is asserted when `β` is treated
as an additional variable, because `βJ` is then not affine in all inputs.

`check.py` pins both source DAGs, proves the two local identities by exact
sparse integer polynomial arithmetic, rejects sign mutations, checks the
only old `F,α` consumers, verifies topology and liveness of all 13 coordinates
and four ports, and checks the operation counts. It also compares 50 signed
assignments for each graph; those finite checks supplement the structural
identity and are not the reason it holds for all assignments. Normal Python
actually exited 0 and optimized Python was rejected. No new Lean literal,
internal proof, fixed-port unrestricted transport, or published display is
claimed. The earlier one-gap proposal and its missing reverse bound are
discussed in `../adaptive-gap85-normalization/`.
