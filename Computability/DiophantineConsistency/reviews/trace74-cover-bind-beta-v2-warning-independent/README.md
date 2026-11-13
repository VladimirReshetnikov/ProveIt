# Independent factual audit: beta-bind v2 warning rejection

Attempt01 is policy-rejected and excluded. The author reports actual outer session 60394 exited 1 and was reaped. Child result SHA-256 `3e78e42d67e6ee8c0d0b350bffc5b97e4d00eacb35e784a8cf51ca214e732a64` records Lean exit 0 and null monitor reason, but stdout contains the exponent-8807 threshold warning and a `[propext]` theorem report; strict runner rejects the warning. Outer terminal SHA-256 `390267e991d9db12481adc22353153b0a84e1478d29334ea9c9e430e638e0166` records child exit 1/FAILED with stable inputs/wrapper. Independently verified stage and outer log hashes; no Lean replay was run.

The local irreducibility changes in v2 did not suppress the displayed warning in this attempt. The warning reports the exponentiation was not evaluated; it does not identify a timeout or invalidate previously accepted component theorems. No beta-bind theorem, actual mask cover, graph guard or iPRA result is accepted from this attempt.
