# The translated source axiom `0 < 1` in PAeq

Foundation's PeanoMinus contains `0 < 1`. Its PAeq translation defines `<`
through a positive additive difference. The constructive target certificate
instantiates the fixed PAeq axiom `0 + x = x` at `S(0)` and introduces the
existential witness `0`, yielding the exact translated source sentence.

`internal_zeroLtOne_proof` quotes that actual Foundation proof object and
establishes internal provability of the numeric translation in every
arithmetic model satisfying IΣ₁. This supplies one standard finite source
arithmetic axiom. Other finite source axioms, the arbitrary internal
induction-schema supplier, and the PAeq-proof-to-PA194-machine link remain
open.

From the repository root with matching audited Lean 4.32 overlays:

```sh
IPRA_FOUNDATION_OVERLAY=/path/to/foundation/package-lib \
IPRA_LEAN_OVERLAY=/path/to/project/lib \
  bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-paeq-zero-lt-one/check.sh
```

The complete standalone script passed against the audited project and
Foundation overlays, rebuilding the local chain and checking the upstream
pins. The exported theorems' axiom audits contained no `sorryAx`.
An independent complete replay also passed without `sorryAx`.
