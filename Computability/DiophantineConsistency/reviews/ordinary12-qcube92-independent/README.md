# Independent audit of the 92-operation q-cube candidate

The pinned 92-operation graph is exactly the complete pinned 94-operation
parent DAG after replacing the witness `Y` by `q³*s`, factoring `q³` from the
first residual, and leaving the other nodes and square-sum tail unchanged.
A separate node-by-node reconstruction verifies all inputs, ordering,
operations, and output reachability. All 92 operations are live: 51
multiplications, 24 additions, and 17 subtractions. The positive witness `s`
replaces `Y`; the other 11 witnesses and four fixed ports are unchanged. The
count is for this positive-coordinate DAG and excludes a later `x+1` shift.

Write `Q₃ = q³`, `b = qm`, `W = folded_g31`, `B = Bt`, and `H = g41`.
After substituting `Y = Q₃*s`, the old and new first residuals satisfy

```
Z_old = Q₃ * (b * (W+s) - B) = Q₃ * Z_new
A0_old = Z_old² - (Q₃*b)²*H = Q₃² * A0_new.
```

The checker verifies these identities by exact sparse integer polynomial
arithmetic with independent indeterminates; it also verifies the full graph
and checks 400 positive input examples. The polynomial calculation proves
the displayed identities in every commutative ring; it is external and is not
a Lean theorem relating either JSON graph to the Lean expressions.

## Candidate degree

For the fixed coefficient payloads, the exact total degree is **164**. The
independent upper-bound propagation uses the exact identity
`h=(V+n)²-1-Q*n*(2V+n)`, with the graph's existing `Q` (not `Q₃`). It verifies
`deg Q ≤ 12`, `deg V ≤ 8`, `deg h ≤ 21`, `deg den ≤ 20`,
`deg polarT ≤ 24`, `deg polarA ≤ 41`, `deg polarCorrection ≤ 72`, and
`deg N ≤ 82`; the resulting output degree is at most 164.
For the lower bound, the checker hashes and decompresses the four retained
fixed coefficient payloads, substitutes witness number `i` by `(i+2)*t`,
and computes the output over the integers modulo 1,000,000,007. Its degree
is 164 with nonzero leading coefficient 311486212. Thus the integer
polynomial also has total degree at least 164. These degree computations and
coefficient-file bindings remain external.

## Scope of the model proof route

A complete Lean proof has not yet been checked. The following route uses
existing model theorems and requires all the indicated hypotheses:

1. In any `IΣ₁` model, let the port tuple consist of natural numerals and
   assume `J > 0` and the model value of `beta` is positive. The original
   first factor at zero forces `q³ ∣ Y` by
   `FreeJRootBinding.first_factor_forces_Y_divisible`. The previously checked
   `FreeJSumSquares.zero_iff_literal` converts a zero of the 94-operation
   square-tail expression to the literal-zero hypothesis of that theorem.
2. If the old valuation is strictly positive, choose `s` from that
   divisibility witness. Since `Y > 0`, `s` cannot be zero and hence is
   positive in the model's natural order. The other coordinates are
   unchanged. Existing `CompactFixedBeta.bounds` supplies positivity of the
   fixed symbolic beta from `J > 0`; transport to the intended byte recipe
   additionally needs the existing port-binding theorem and a coherent
   provider. Other arbitrary port tuples need an explicit beta-positive
   assumption.
3. At a valuation related by `Y = q³*s`, use the above identities in the
   ordered difference ring, rather than truncated natural subtraction. Since
   `q = 1 + J*beta > 0`, `q³` is nonzero and can be canceled in the integral
   domain. Consequently the old first residual vanishes iff the new one
   does; the other two residuals agree. The three-square argument then gives
   equivalent zeros at the related valuations.
4. Conversely, a positive new valuation maps directly to a positive old one
   using `Y = q³*s`. Both directions together give equivalence of existence
   of positive zeros, not a same-valuation equivalence in the original
   coordinates. This must still be formalized and compiled in a coherent Lean
   build; its file/PDF bindings and eventual internal iPRA endpoint are
   separate obligations.

Run `python3 -I -S -B check.py` from this directory, or provide its path from
any directory. The run captured in `observations/stdout` exited zero with empty
stderr. It pins the old and new JSON graphs, coefficient binding and compressed
payloads by SHA-256, checking them again after the computations. It does not
launch Lean or authenticate imported object/source ancestry.
