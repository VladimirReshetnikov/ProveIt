# Independent source review: 84 large-k and actual main carrier

This bounded source/mathematical review covers
`research/ordinary13-unscale84-large-k-model-draft/`. It does not run Lean,
builds, staging or provider replay. Its receipt pins the actual 84 JSON,
reverse-graph source, source-only scaled-root and large-k interfaces, compact
port definitions and the author receipt.

The exact 84 graph's main root is built from

```
U=Y*q², a=X*Y+Y, H=3+4*a, c=eta+Y*k,
Dstar = U*(X+a*c) + H*(U*gamma + X*Y*q - k + R + 1),
A1 = Dstar² - U²*(1+Delta*c²).
```

Here R is the **signed literal rank**, not automatically a model-natural
truncated-subtraction expression. The checker pins the graph's actual rank,
shift and main-residual rows, and verifies the displayed shift identity in a
free integer polynomial ring. Its formal negative control confirms that
omitting the `X*Y*q` term changes Dstar by `H*X*Y*q`; it is not presented as a
graph-zero counterexample. The discriminant identity
`(a+2)²=Delta+1` is also checked symbolically.

The proposed `norm_roots` works with the **same positive 84 graph valuation**
and the same natural port tuple for both first and main equations. A positive
J and represented positive beta make b positive; positive input s makes
`Y=q³*s` positive, hence U positive. From the common output's first and main
squares, it applies the source-only `root_of_scaled_ring_square` to the
actual signed first root with scale b and the actual signed main root with
scale U. The resulting natural tau and d satisfy the two stated Pell norms;
neither signed root is assumed positive or identified with the other.

The proposed `large_k` passes those same natural norms, positive
X/Y/eta/zeta, and the discriminant identity to the separately unelaborated
`FirstMainLargeKDraft.first_main_large_k`. The resulting large-k bound and
compact-beta source are used by `compact_reverse_inputs` to propose exactly
the reverse graph's `ReverseInputs` cut. The final positive-zero equivalence
combines that reverse cut with the separate 87 first-norm forward binding.
The two natural-to-integer port wrappers use definitionally identical
pointwise casts in the inspected source; their Lean elaboration is untested.

This review does not establish the actual graph-to-ring rewrites, positivity
and magnitude extraction tactics, the underlying Pell/strict-margin proofs,
the two graph maps, transitive model providers or axiom reports. The compact
positive-zero equivalence is a source proposal, not a checked all-model
bridge, parent `PolynomialBridge`, physical PDF binding or iPRA/ZFC endpoint.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-unscale84-large-k-actual-main-independent/check.py
```
