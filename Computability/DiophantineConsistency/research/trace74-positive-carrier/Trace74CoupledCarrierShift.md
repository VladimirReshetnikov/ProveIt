# One shift for both positive coordinates

`Trace74CoupledCarrierShift.positive_T_and_carrier` joins the checked Pell
congruence construction and the positive carrier lemma. It explicitly chooses
`s = f*(N+c)+P+1` and uses the **same** auxiliary quotient `Q` to construct
positive `T` and `v7`. Their equations are

`Q+c=f*(c*T+N)` and
`M*(v7-Q*Q*B)+(C-G)=M*tau*phi*y` in the model's difference ring.

The theorem retains explicit Pell norm, seed/index congruences, divisibility
of the signed carrier constant `(C-G)/M`, and `B≥1`. Its linear lower bound
for the auxiliary quotient discharges the separate size requirements for both
coordinates. This is a model-level conditional construction, not yet a
binding of the actual graph registers or a proof of a graph zero. Its import
chain is a captured-provider check, not a clean canonical rebuild.

Lean 4.32.0 session 2856 exited 0 without warnings, with metatheory axioms
`[propext, Classical.choice, Quot.sound]`:

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74CoupledCarrierShift.lean \
  -o /tmp/Trace74CoupledCarrierShift.olean
```

Source SHA-256 `42866d0759af81a49bbcdd30055731299c37e6fb3d408a6168ffa863da119525`;
object SHA-256 `22733cfeb9a1300b86392b0a3965fadaf95d2c1856b2fee71cbeaa5e21947aa8`.
