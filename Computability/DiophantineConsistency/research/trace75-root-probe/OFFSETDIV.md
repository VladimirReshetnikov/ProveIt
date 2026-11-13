# Trace75 signed offset divisibility

`Trace75OffsetDiv.graph_offset_divisible` proves, in every model of IΣ₁,
that a positive trace75 zero with positive β has `q⁴ ∣ e` in the model's
difference ring. The port `K0` is arbitrary; no fixed-mask bounds, parity,
or rank-alignment assumption is used. The conclusion is signed divisibility:
it does not assert a positive quotient or identify the rank.

The proof uses the same carrier witnesses returned by `graph_carrier_bound`.
Its square equation yields one signed factor `Z=M*z`; the exact graph
identity then gives `D ∣ h*H*e`, where `D=XY`, `q⁴ ∣ D`, and `h*H≡1 mod q`.
A finite geometric inverse cancels `h*H` modulo `q⁴` without dividing in
the model. This is a necessary property of trace75 zeros, not a halt or
iPRA equivalence and not an unguarded trace74 reduction.

Accepted `run-offsetdiv-v2.py`, `observations/offsetdiv-attempt02/`:
Lean exit 0, no warning/error, object
`/tmp/trace75-offsetdiv-m1wthwir/Trace75OffsetDiv.olean`, SHA-256
`994ed10ffec11931a4231a88100ab14fdb45cc0acd1eb92715c9a7c56ea99cde`.
Attempt 01 is retained: Lean returned 0 but its four unused simp-argument
warnings caused the strict runner to reject it. The accepted revision removes
only those arguments. The selected direct import is pinned; historical source
ancestry, other transitive/package providers and external graph/file binding
remain inherited limitations, not established by this check.
