# Independent review: eta-natural unit/norm adapter

The adapter's conditional factor equations and the pinned bridge's proposed
signed norm outputs agree after the explicit graph-to-natural representation
steps listed below. The two arithmetic cut identities check as free
commutative polynomial identities, and the cited signed-norm and early-index
source signatures match. No missing eta-positivity assumption or extra
`X*Y*q` term was found. This is not Lean elaboration or a theorem that those
representations hold at a graph zero.

For the first factor, the bridge proposes
`z²=b²*(1+ell*(ell+k))` in the difference ring. The adapter assumes its
unit form with model naturals `b,X,Y,k` and
`ell=ι((X*Y²)*k)`. The identity

```
((X*Y²)*k)*(((X*Y²)*k)+k) = (X*Y²)*(X*Y²+1)*k²
```

holds without subtraction or positivity. The cited
`first_natural_norm` source requires the signed equation and **`b>0`**;
it then proposes a natural tau with the exact first Pell norm. The bridge
does not supply either the natural representation of its signed b or b's
positivity.

For the main factor, the prototype has `kbase=k−1` as a signed-ring
identity because `k=kbase+1`. Thus its literal root satisfies

```
Dstar = U*(X+a*c) + H*(U*gamma+R+1−k) = P−N
P = U*(X+a*c)+H*(U*gamma+R+1),  N=H*k.
```

There is no extra `X*Y*q` term. The pinned bridge proposes
`Dstar²=U²*(1+Delta*c²)`. After proving the exact representation
`Dstar=ιP−ιN` and cast equalities for U, Delta and c, this supplies the
adapter's unit premise. The pinned `main_pair_norm` source takes precisely
that signed squared equation, and `main_natural_norm` additionally requires
`U>0`; it returns a natural root with the stated norm. These are fact-level
source interfaces, not a checked graph-to-model cast or a proof of the
resulting quotient.

The `rank_congruence_of_main_unit` call retains `q>0`, `Y=q³*s`, `Y≥8`
and `k>0`; its argument order and magnitude norm match the pinned
eta-natural early-congruence source. Both sources use arbitrary model-natural
eta, including zero. The result is only divisibility of the stated magnitude
by `q⁴`; it does not by itself supply the first index, positivity of the
actual graph inputs, or the final contradiction. The two remaining adapter
lemmas operate on signed strong/auxiliary equations and do not infer natural
subtraction or positive roots.

To compose the bridge with this adapter, a future client must prove the exact
embeddings of the prototype's b, ell, k, U, Delta, c and root into the
adapter's model-natural data, including `Dstar=ιP−ιN`. The prototype
port expressions are arbitrary integers in the bridge; the adapter's named
ports and rank must be represented by model naturals. In particular,
identifying the signed rank with a natural expression requires the relevant
truncated-subtraction bounds. These port, rank, cast, positivity and provider
obligations are not discharged by either packet.

Run from this directory:

```
python3 -I -S -B check.py > /tmp/eta-unit-adapter-independent.json
cmp result.json /tmp/eta-unit-adapter-independent.json
```

The checker pins both drafts and relevant fact-level sources, verifies the
two free polynomial identities, and checks 200 bounded prototype
valuations, half with eta zero. The controls are not an all-model
representation theorem. Both drafts and their transitive providers remain
unelaborated; graph-zero extraction, zero maps, and the iPRA endpoint remain
open. No reviewed source was modified.
