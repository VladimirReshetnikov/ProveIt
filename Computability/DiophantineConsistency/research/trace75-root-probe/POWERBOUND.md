# Trace75 exponential height bound

`Trace75PowerBound.graph_power_bound` proves `2^rankNat < Y` in every IΣ₁
model with β≥31, `MC<β`, `MF<2β`, and a positive trace75 zero. `K0` is
arbitrary. It uses the exact first/main index relation and the actual
unscaled graph parameter `P=XY²`: the generic scaled-Pell growth theorem is
instantiated with scale `S=Y` and main parameter `Y*(X+1)−1`. The proof
derives the necessary `X≥16` and first-index bound; it does not assert that
`X=2^rankNat`, machine halt, or an iPRA equivalence.

`run-powerbound.py`, `observations/powerbound-attempt01/`: Lean exit 0,
no warning/error; object `/tmp/trace75-powerbound-hz8vjnsk/Trace75PowerBound.olean`,
SHA-256 `b4e6a42fc8abe23e8282d6ad12c354f5938d99ce10e0918222e1d54ce4447271`.
The selected direct imports are pinned. Historical provider/transitive and
package ancestry and external graph/file binding remain inherited limits.
