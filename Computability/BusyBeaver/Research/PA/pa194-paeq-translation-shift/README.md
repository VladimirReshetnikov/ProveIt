# Arithmetic-to-PAeq term shift and substitution compatibility

This package proves that the current-Foundation arithmetic-to-PAeq term and
term-vector translations commute with free-variable shift, bound-variable
shift, and simultaneous term substitution. It also proves the exact qVec
lifting equation. The theorems apply to internally well-formed source terms
and vectors in every IΣ₁ arithmetic model, including nonstandard codes.

These results are prerequisites for formula-level substitution agreement;
they do not prove that agreement, PA proof-code transport, or a machine
reduction. The adaptation includes an explicit current-Foundation proof that
bound-variable shift preserves source term-vector validity. Upstream hashes
identify the adapted PA196 input files.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-translation-shift/check.sh
```

The four modules passed ordered Lean suffix checks against the checked PAeq
translation-validity module and retained project/Foundation prerequisites;
printed dependencies omit `sorryAx`. The full standalone replay remains
pending.

An independent ordered suffix replay rebuilt all four shift, qVec and
term-substitution compatibility modules against separately checked PAeq
prerequisites. It passed without `sorryAx`; this was not a full nested replay.
