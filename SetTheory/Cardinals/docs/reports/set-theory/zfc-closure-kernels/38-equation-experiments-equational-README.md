# Cyclic-algebra research artifacts

These files accompany a proposal for a small consistency-search frontend.
They are **not a new Turing-machine state record**. The ZFC-specific target term
and a compiled blank-tape binary machine are not present.

## Contents

- `cyclic_proposal.md`: mathematical derivation of the seven equations, exact
  validity-query construction, premise counterexample, and missing work.
- `cyclic_algebra.py`: standard-library-only ground rewrite witness kernel.
- `test_cyclic_algebra.py`: finite algebra, translation, adversarial certificate,
  codec, and deep-term checks.
- `basis.json`: exact seven axiom trees and the 88-symbol syntax count.
- `demo.json`: a small accepted equality and a rejected altered target.
- `verification.json`: captured test result.
- `independent_audit.md`: a separate agent's mathematical and implementation
  audit; this is not a proof-assistant certificate.
- `literature_notes.md` and `literature.bib`: primary references and status
  distinctions for integration into the main report.

## Reproduce

Use Python 3.10 or later. No additional packages are required.

```sh
python3 cyclic_algebra.py basis
python3 cyclic_algebra.py demo
python3 test_cyclic_algebra.py
```

The programmatic entry points are `check`, `check_code`, and `search`. The first
two check finite fully specified certificates. An unbounded `search` enumerates
all natural certificate codes and returns the first accepted one. A bounded
search returning `None` establishes only that its budget was exhausted.

The CLI `check` subcommand accepts a JSON object with ground `source` and
`target` term trees and a natural `certificate_code`. For example, the object
in `demo.json` contains the needed fields and additional descriptive fields
that are ignored by the checker:

```sh
python3 cyclic_algebra.py check demo.json
```

Finite checks support the executable implementation, while the general
algebraic proofs are written in `cyclic_proposal.md`. Neither establishes that
an unprinted ZFC-specific query was compiled, loaded, or simulated.
