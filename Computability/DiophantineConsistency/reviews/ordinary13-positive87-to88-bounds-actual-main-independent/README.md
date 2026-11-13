# Independent source review: 87/88 strict auxiliary bounds

This reviews `research/ordinary13-positive87-to88-bounds-model-draft/`
against both exact literal graphs and the fact-level norm/bounds interfaces.
No Lean, build, staging or provider replay was performed. The receipt checks
all named 87/88 literal rows against their JSONs and reproduces the author's
checker.

For the same positive valuation and represented natural ports, both graph
sources have the same first, main and strong fields, independently of the
changed auxiliary coordinate. The proposed client uses the actual first
scale `M=q³*(J*beta)` and main scale `U=Y*q²`. The receipt pins their graph
rows and verifies the exact signed main shift

```
U*gamma + X*Y*q - k + R + 1.
```

The `X*Y*q` term is present. A free-ring calculation confirms that omitting
it changes the shift by that term; this is a formal expression comparison,
not a graph-zero counterexample. R is the actual signed graph rank. The
source does not require a natural representation or sign of R for these
field identities.

`common_zero` proposes extracting the common first, main and strong zeros
from either output's four squares. Given positive J and represented beta,
positive Y and the common graph zero, `bounds_of_zero` uses the separately
unelaborated `root_of_scaled_ring_square` twice: once with scale M and the
actual signed first root, and once with scale U and the actual signed main
root. This proposes natural first/main Pell roots without orienting either
signed root. The strong residual supplies its natural equality and the
signed identity `Q=(i*c*c)²`; the actual auxiliary field uses
`V+c=f²*(T*c−R)`. The receipt also checks that latter identity in the free
ring; no natural representation or sign of V is assumed.

The `aux_bounds_of_natural_norms` source interface takes those two natural
norms, the positive X/Y/eta/zeta/i coordinates, discriminant identity, strong
norm, Q and signed-V binding as explicit premises. It proposes the exact
strict conclusions `1<Q` and `1<V²` required by the 87/88 auxiliary witness
client. `PositiveBeta p` is an explicit all-model positivity assumption for
the natural port cast; `bounds_cut` packages it and the proposed graph proof
into the prior `BoundsCut`. It does not itself establish compact beta
positivity, the inherited norm/geometry proofs, a zero-equivalence bridge,
model/provider compatibility, an axiom report, or an iPRA endpoint.

All Lean scripts, signed casts, graph evaluations, magnitude/divisibility
extraction, positive-coordinate witnesses and transitive providers remain
unelaborated. The finite controls and symbolic checks are not proofs in the
intended nonstandard models.

Reproduce from `Computability/DiophantineConsistency`:

```
python3 -I -S -B reviews/ordinary13-positive87-to88-bounds-actual-main-independent/check.py
```
