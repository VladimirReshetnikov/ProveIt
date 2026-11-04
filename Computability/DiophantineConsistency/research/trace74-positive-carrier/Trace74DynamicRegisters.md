# Literal dynamic-register identities

`Trace74DynamicRegisters.components` exposes c, rank, the trace coefficient f,
the B register and the signed carrier offset from the actual 74-row chart.
Over any commutative ring and any ports and tuple, `V_formula` and `Z_formula`
prove the exact identities

`V+c=f*(c*T-rank)` and `Z=M*(n-V*V*B)+offset`.

These theorems have no graph-zero or positivity hypotheses. They reduce the
remaining dynamic binding work to proving that the relevant components of the
candidate base tuple equal the intended c, negative rank, f, B, M and signed
offset; those candidate identities and all CRT premises remain open. The
literal graph module comes from the captured-provider chain.

Lean 4.32.0 session 48291 exited 0 without warnings; axiom reports are
`[propext]` for `V_formula` and `[propext, Quot.sound]` for `Z_formula`. An
earlier attempt expanded the whole circuit during ring normalization and hit
the 3 GB memory cap; the checked source first proves a small general ring
identity and then specializes it without expanding the circuit.

```sh
LEAN_PATH=/tmp:/tmp/trace74-direct-four-block-1zltaw2f/lib:/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib \
  timeout 120 lean -M3000 -j1 -DElab.async=false \
  --root=research/trace74-positive-carrier \
  research/trace74-positive-carrier/Trace74DynamicRegisters.lean \
  -o /tmp/Trace74DynamicRegisters.olean
```

Source SHA-256 `7f04da3671e130609a29aa6a66627d4b6e8299458d9f2ac77f714a8bd96cc623`;
object SHA-256 `7ac639b7f868106fb0d9fd30ae0f816817c237c52eb21eaeb01bed1a967f8743`.
