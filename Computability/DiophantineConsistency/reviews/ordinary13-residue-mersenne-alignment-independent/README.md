# Independent source review: Mersenne cancellation and alignment

The reviewed draft's stated fact-level interfaces agree with the pinned source
signatures. No missing arithmetic premise was found in the proposed
composition. This is a **source review only**: neither the client nor the
imported sources have been elaborated or rebuilt here, and no graph, model
port, provider closure, or iPRA endpoint is certified.

`cancel_three` requires all of `4≤d`, `q=(2^d−1)*J+1`, and
`q ∣ 3*2^R`. The client additionally assumes `X=2^R` to rewrite the
supplied `q ∣ 3*X` into that exact divisibility. Its positive-J assumption is
not needed by this cancellation theorem. The imported source derives its
factor-three nondivisibility and Bézout certificate under the **combined**
hypotheses, including the divisibility by `3*2^R`; it does not show all
Mersenne-form values are coprime to three.

For example, `d=5,J=2` gives the represented-form integer `q=63`, which is
divisible by three. Taking `X=21` gives `q ∣ 3X` but `q ∤ X`: this is a
scalar control outside the required power hypothesis, not a graph zero.
Another scalar control, `d=1,J=2,q=3,X=1`, satisfies the form, power, and
three-divisibility but not cancellation, showing why one cannot simply
drop the stated lower-bound interface. It does not show that `d≥4` is the
optimal possible bound.

For alignment, the source theorem requires `2≤d`, `J>0`, and the exact
factorization `2^R=w*((2^d−1)*J+1)`. The client derives its stronger
`4≤d` premise, gets the divisor witness from the preceding conditional
cancellation, rewrites `X=2^R`, and commutes factors to supply the needed
factorization. The source concludes `w>0` and a positive `N` with the
stated aligned base and quotient; the client drops the unused `w>0`
conclusion and uses the original divisor-witness equation for `X=q*w`.
The orientation and `hq.trans hqn` are consistent at source-statement level.
The `J>0` premise is substantive for positive `N`: when `J=0`, `q=1`, and
for positive `d` there is no positive `N` with `q=2^(d*N)`.

`check.py` pins the reviewed draft, its two direct provider sources, the
nearby sign-free power draft, and the reviewed README; it checks the exact
provider statements and runs independent bounded integer controls, including
`J=0` cases. The scalar controls and sampled successes are not proofs over
arbitrary `IΣ₁` models and do not validate Lean syntax or tactics. Reproduce
from this directory using

```
python3 -I -S -B check.py > /tmp/independent-mersenne-alignment.json
cmp result.json /tmp/independent-mersenne-alignment.json
```
