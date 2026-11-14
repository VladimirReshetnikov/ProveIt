# Target validity of arithmetic-to-PAeq syntax translation

This package proves that the current-Foundation numeric syntax translation
maps each well-formed source arithmetic term, term vector, atom, and formula
to well-formed PAeq target syntax at the same bound-variable depth. The
formula theorem uses internal structural induction in arbitrary IΣ₁ arithmetic
models and applies to nonstandard source codes.

These are syntactic validity results; they do not prove numeric output or
graph-witness bounds for the formula translation, substitution compatibility,
PA proof-code transport, or a machine/consistency implication. The upstream
hashes identify the adapted PA196 input proofs.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-paeq-translation-validity/check.sh
```

The standalone script passed against the audited project/Foundation objects.
It checked the upstream pins and rebuilt the full local syntax/validity chain;
all printed dependencies omit `sorryAx`.

An independent complete standalone replay rebuilt the term, atom and formula
validity chain from the pinned audited overlays and passed without `sorryAx`.
