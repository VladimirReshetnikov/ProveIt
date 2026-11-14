# PA195 diagonal-freshness prerequisite

The diagonal calculus uses the numeric code `4 * Cantor(a,b) + tag` for
formula constructors. `PA195FreshBound.candidate_pra_fieldBound` is a Lean
proof of an actual theorem of candidate classical PRA: if that code is
positive, each of its two decoded Cantor fields is strictly smaller than the
code. The statement uses the bounded arithmetic graph of the literal Cantor
pairing, not Foundation's distinct pairing convention. Its model proof holds
in every model of IOpen, hence in every candidate-PRA model, including
nonstandard models; first-order completeness supplies the PRA derivation.

This proves only the immediate-field bound. It does not yet encode the
recursive occurrence predicate, prove the code is absent from its own decoded
formula, verify any generated proof template, or connect a PA refutation to
PA195 halting. The arithmetic needed to verify a primitive-recursive generator
must be distinguished from the possibly unrestricted PA induction instance
that generator inserts inside a PA proof.

To check from the repository root, set `IPRA_LEAN_OVERLAY` to the matching
audited project object directory and `IPRA_FOUNDATION_OVERLAY` to the matching
Foundation object directory, then run:

```sh
Computability/BusyBeaver/Research/PA/pa195-calibration/check.sh
```

The script verifies source and direct object hashes and rejects `sorryAx` in
the printed theorem dependencies. It uses the supplied audited object
directories; it does not rebuild their transitive dependencies.
