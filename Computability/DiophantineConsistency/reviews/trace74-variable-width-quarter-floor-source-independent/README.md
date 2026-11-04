# Independent source review: model division by four

The reviewed source has SHA-256
`3d04a75a690c881328ddff5bec3dfd3362ed1cc1e08fb38add1791be7c85c898`.
Its division argument is sound for the model's natural arithmetic: putting
`w=n/4`, `mul_div_le` supplies `4w≤n`; if `w=0`, the division algorithm
`4w+n%4=n` and `n%4<4` contradict the explicit premise `n≥4`. Thus `w≥1`.
The existing quarter-width theorem applies to this `w`, yielding
`n+n/4<r` by the model's linear order.

The result concerns supplied first and main ordinate indices for one
positive graph zero at the fixed symbolic first port. The assumptions
`n≥4` and `8n≤67·8807` remain explicit. It does not establish the bound
outside that range, exclude all graph zeros, prove a reverse guard, or
give an iPRA endpoint.

This is a source-level mathematical review; it is not an independent Lean
replay or an audit of transitive provider/package ancestry.
