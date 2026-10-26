# Correction addendum to the independent thirteen-variable review

Reviewer: `/root/complemented47_review`.

The original review, SHA256
`e5dbb38bf08ba18f1a5add628ba56e4295bed59312ee4fda4f65fcdb1b9b9cdf`,
missed an incorrect recurrence initialization in section4 of the reviewed
proof `3eb77199b3961be024ec1f170d843f939ecbabb8b2af33adad6d6f66bb181af1`.
The second independent reviewer found it. I acknowledge that omission;
the original receipt remains preserved as a historical review, not an
assertion that its literal initialization was correct.

For the signed odd ordinate sequence
`v_j=(-1)^j*psi_A(2*j+1)`, the initial pair is

```
v_0=1, v_1=1-4*A^2.
```

Indeed `psi_A(3)=4*A^2-1`. Also the claimed polynomial sequence has
`Q_1(u)=4*u-3`, so `Q_1(1-A^2)=1-4*A^2` directly. Its recurrence coefficient
is `2-4*A^2`, agreeing with the signed odd ordinate recurrence. The former
text's second initial value `3-4*A^2` was wrong. The corrected value
establishes the intended identity at both initial indices and then by
induction for every index.

I read the corrected passage and verified that replacing its one corrected
initial value back reconstructs the exact prior proof hash above. The
complete corrected proof now has SHA256
`d2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8`.
There are no other byte changes. The correction makes the stated identity
valid; it does not change the polynomial, witness formulas, variable count,
operation counts or degree claims. My prior full review of those arguments,
together with this checked correction, yields PASS for the corrected proof
within the same retained ordinary-calibration boundary. All subsequent
literal graphs and deterministic audits must bind this corrected hash.

This addendum reviews the correction and the ordinary proof. It claims no
completed graph materialization or new formal-kernel replay.
