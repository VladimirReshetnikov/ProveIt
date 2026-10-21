# Formalism-side contribution: self-vacuity and fixed-B obstructions

This packet contains an ordinary calibration proof for a new numerical
formalism, finite Hilbert proof certificates, exact source-size measurements,
and two explicit four-valued diagnostics. It does not contain a newly
certified Turing machine with 217 or fewer states.

The baseline and inherited theory are pinned to ProveIt commit
`9adcaff0a72486ecc81242e0eca86e428c74879e`.

## Mathematical findings

- Replacing unrestricted rho8 by K, S, and the single-parameter schema
  `A → Q_A A` preserves consistency strength. The numeric formula code
  itself supplies a fresh binder, using the inherited `D_fr_self` property.
  The weaker `NN(A→Q_A A)` also suffices.
  See `self_vacuity_note.md` for both consistency directions, the native
  zero alias, and the inherited decoded-theory interpretation.
- The finite lower proof recovers unrestricted rho8. The upper direction
  is a decoded-theory proof interpretation. Equality of the old and new
  native theorem sets is not claimed.
- A four-valued model validates the complete native calculus when rho8's
  weakening parameter B is fixed to C. That weakened calculus is provably
  consistent, so it cannot yield the desired ZFC-provable calibration if
  ZFC is consistent.
- A separate four-valued table shows that fixing B to native truth zero,
  together with truth, its zero alias, and MP alone, does not derive K.
  This second table makes no claim about the remaining native quantifier
  and set-theory rows. The full B=0 calibration remains open here.
- A 16-element Heyting algebra blocks a proposed K/S joint-induction step:
  a persistent, stable atom can have a negation which is not persistent and
  a quantified negation which is not stable, even with normality, seriality,
  commutation and rho6. This is only a logical-fragment counterexample;
  `logical_induction_obstruction.md` explains its exact scope.

## Reproduction

Python 3.11 or later with its standard library is sufficient. No network,
SMT solver, proof assistant, or installed ProveIt checkout is needed for
these replay commands. Keep assertions enabled.

```sh
python3 check_self_vacuity.py
python3 check_fixed_b_countermodels.py
python3 check_persistent_negation.py
python3 measure_self_vacuity.py --output reproduced_measurement
```

The source measurement examines 1,944 distinct layouts per variant and
usually takes about one minute. It uses the pinned copies in `inputs/`.
To measure against a local copy of the same repository inputs instead:

```sh
python3 measure_self_vacuity.py --repo /path/to/ProveIt --output reproduced_measurement
```

The script rejects changed input hashes. Its measured best source files
should be byte-identical to `sites_KSSV.json` and `sites_KSNNSV.json` here.
The receipt's elapsed time is expected to differ.

The proof replay produces 1,110 proof nodes and five closed endpoints.
`self_vacuity_proof_receipt.json` lists the exact axiom schemas in each
endpoint's dependency graph. The independent serialized rule reader checks
MP/GEN and open assumptions, but shares axiom-formula constructors with the
builder. This is finite executable proof checking, not a Lean or Rocq theorem.

The countermodel replay produces `fixed_b_countermodels_receipt.json`;
the associated note supplies the unbounded native-code and proof inductions.
Its matrices were found with SMT, but discovery is unnecessary to validate
the supplied explicit witnesses.

The Heyting-fragment replay produces `persistent_negation_receipt.json`
using only finite set operations. It checks all 4,096 S instances, 256 K
instances, 256 normality instances and 16 rho6 instances. It does not model
the full native membership/equality rows or the set-theory bundle.

## Measurements and limitations

| Source | Distinct source subtrees | Primitive occurrences | Maximum zero run |
|---|---:|---:|---:|
| Existing K218 | 205 | 4,744 | 6 |
| K + SV + S | 212 | 5,003 | 6 |
| K + NN(SV) + S | 214 | 5,097 | 6 |

Source subtrees are not Turing-machine working states. These source
alternatives have no binary compilation, startup, runtime, or machine
calibration certificate. Their direct measurements are larger than K218.
The input `k218.native.tm` is a pinned baseline used to identify the old
source macros; it is not a new machine produced by this contribution.

`manifest.json` records the SHA-256 hashes and sizes of the packet's
non-manifest files. The attributed upstream files and the copied source
helpers retain their original bytes; see `ATTRIBUTION.md`.
