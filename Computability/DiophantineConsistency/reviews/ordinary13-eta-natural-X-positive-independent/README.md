# Independent review: eta-natural X positivity

The draft applies the pinned `xzero_impossible` fact-level source with the
same signed main root and the required `q≥2`, `Y≥q³`, shape and squared-norm
hypotheses. The actual prototype carrier at `v6=0` has the stated shape and
no extra `X*Y*q` term. No mathematical mismatch was found in those displayed
interfaces. This is not Lean elaboration, a provider build, a verified graph
zero theorem, or an iPRA endpoint.

The theorem's `p : Fin 4 → ℕ` gives the represented natural port tuple; it
separately assumes its beta cast `(p 0 : V)>0`. The imported, unelaborated
`J_positive` draft applies to the same generated prototype zero and this
natural tuple. Its proof relies on the first signed factor/norm and the
natural K0 cast; it does not assume eta positivity. From `J>0` and beta
positive, the client obtains `q=1+J*beta≥2`. The actual shifted scale input
gives `s=v7+1≥1`, hence `Y=q³*s≥q³`. These are the exact inequality
premises of `xzero_impossible`.

Under the contradiction assumption `v6=0`, the prototype's `X=q*v6=0`,
`a=Y`, `U=Y*q²`, and `H=3+4Y`. Its own signed rank may be negative; the
client correctly leaves it in `DiffRing V` inside the actual signed shift
`t=U*gamma−(eta+n_zeta−rank)`. The resulting graph-root shape is
`z=U*(Y*c)+H*t`, and the proposed unit/norm bridge supplies
`z²=U²*(1+(H+Y²)*c²)` at the same graph valuation. The finite graph controls
check these identifications at the pinned literal, including eta zero, but
are not a model evaluation proof.

The imported arithmetic source uses nonzero U and signed square divisibility
to write `z=U*d`, with signed d. Its norm gives
`(d−Y*c)*(d+Y*c)=1+H*c²`, and the root shape gives
`H ∣ U*(d−Y*c)`. The explicit ring identity in `cancel_modulus` then gives
`H ∣ U`. The source reflects the resulting signed divisibility to model
naturals, uses `4U=(H−3)q²` to get `H ∣ 3q²`, and contradicts
`0<3q²<H`: since `q≥2`, `q²≤q³≤Y`, and `H=3+4Y`.
The imported `sq_dvd_sq` and signed-to-natural divisibility reflection are
substantive model-source dependencies, not consequences of the finite
controls; their provider/axiom closure must be checked separately.

The client first concludes `v6>0`, then obtains positivity of the exact
prototype X by multiplying by positive q. Eta, the signed rank, gamma,
and c need no positivity in the arithmetic lemma. The zeta shift remains
present in this prototype. Fixed compact-port casts, all source elaboration,
factor-unit extraction, eta-zero contradiction, zero maps and the internal
endpoint remain open.

From this directory reproduce the independent receipt with

```
python3 -I -S -B check.py > /tmp/eta-X-positive-independent.json
cmp result.json /tmp/eta-X-positive-independent.json
```

The checker pins the draft and principal sources, checks their exact
interfaces, and runs 400 finite prototype-root controls and 1,326 size and
divisibility controls. Those checks are not all-model proofs or Lean
verification. No reviewed source was modified.
