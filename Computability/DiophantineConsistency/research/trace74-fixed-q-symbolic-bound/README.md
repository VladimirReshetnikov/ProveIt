# Full symbolic exponential lower bound for the fixed trace74 first port

`Trace74FixedQSymbolicBound.fixed_q_symbolic_lower` proves in any model of
`IΣ₁` that `p 0 = CompactFixedBeta.betaNat` and `v 0 > 0` imply

```text
Exp.exp ((67:V)*8807) ≤ q p v.
```

The exponential is the model's represented power of two; the exponent is
the cast of the fixed natural number `590069`. The proof uses the existing
`CompactFixedBeta.beta_identity` and `q=betaNat*(v 0)+1`, without evaluating
the enormous natural number. It requires no graph-zero premise and leaves
the other ports and witnesses arbitrary. It does not relate the symbolic
port to the external displayed payload, discharge any index window or
reverse guard, or establish an iPRA endpoint.

An author check used Lean 4.32.0, `-M3000 -j1 -DElab.async=false`, a
120-second subprocess timeout and this directory as `--root`. `LEAN_PATH`
was the `lean_path` field of
[`trace74-fixed-q-large-draft-v2/observations/attempt01/terminal.json`](../trace74-fixed-q-large-draft-v2/observations/attempt01/terminal.json).
The output object was `/tmp/Trace74FixedQSymbolicBound.olean`. Actual outer
tool session 14486 exited 0, with the sole axiom report
`[propext, Classical.choice, Quot.sound]`.

```text
Trace74FixedQSymbolicBound.lean  beeed44149dcba4dcdfe298acd3edd66a1bc25d3d8f62d561c751b19220a5706
Trace74FixedQSymbolicBound.olean b4b0963e952ec4c290c69d1d1a3edb7b35cd59848c34946457f15c135a57de2d
Trace74FixedQLarge.olean         a3546f8f243a65227121743490aa0156bd1e7adffd71f64c5d846e05d2171343
Lean executable                  e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550
```

This is an author check using temporary captured providers, not an
independent replay or current-source rebuild. Full transitive, package,
dynamic and search-path ancestry remain unauthenticated in this check.
