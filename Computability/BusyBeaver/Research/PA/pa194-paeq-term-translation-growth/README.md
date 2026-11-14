# Arithmetic-to-PAeq term-translation output growth

In every IΣ₁ arithmetic model, `termCode_le` proves the actual numeric
arithmetic-to-PAeq term translator satisfies

```
termCode t ≤ tau (t + fixedAllowance + 8) (20*t + 20).
```

`fixedAllowance` is the explicit constant `1000^6`, written using
multiplication, which covers the fixed output codes for zero and one.
`termVector_le` bounds the translated vector by a repeat vector of the same
term bound. The results cover nonstandard inputs; malformed individual terms
and vectors use the recursor's zero-output policy.

These are numeric output bounds. They complement, but do not replace, the
previous term-translation graph witness bounds. Bounds for the translated atom
and formula outputs and the formula-translation graph remain open, as do
substitution compatibility, PA proof-code transport, and machine calibration.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-term-translation-growth/check.sh
```

The final module passed a fresh Lean suffix check against the independently
checked translation-validity and retained PA196 arithmetic-growth objects,
plus audited project/Foundation prerequisites; printed dependencies omit
`sorryAx`. The wrapper's syntax is checked, but its full prerequisite-prefix
replay remains pending.
