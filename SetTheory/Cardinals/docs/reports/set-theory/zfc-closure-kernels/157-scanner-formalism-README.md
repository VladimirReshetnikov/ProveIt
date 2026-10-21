# Formalism evidence packet

This packet does **not** establish a valid 217-state machine. It contains
portable positive and negative results from the attempt, with their exact
scope stated in the report.

- `formalism-results.tex` is an include-only report fragment, including the
  complete clean-seed argument. It requires `amsmath`, `amssymb`, `amsthm`,
  `hyperref`, and `theorem`/`lemma` environments. `formalism-standalone.tex`
  supplies a small standalone wrapper.
- `matrices/check_restricted_L.py` independently checks two explicit
  three-valued native-code matrices. They refute recovery of S from the
  retained logical rows plus `U=A`, and of K from the retained logical rows
  plus the union `U in {B,C,0,1}`. The full gated set-theoretic bundle is
  excluded and explicitly fails in both matrices. The full-calculus
  equiconsistency question is not settled by these examples.
- `seed/` proves the unchanged abstract source can start with current
  formula `3=E(0,0)`, zero stack/cache, and arbitrary finite candidate
  cutoff and additive parameter. It includes the 79-node closed proof and
  independent checker. The shortened-scanner binary table fails its later
  source simulation, so the seed theorem does not certify that table.
- `source_counterexample/check_local7_source.py` checks a concrete
  source-level spurious MP caused by the `primary-local-7` helper fold.
  It uses inherited macro contracts and does not prove a physical blank
  run of the changed binary table.

All executable checks use Python 3 and the standard library:

```sh
python3 verify_all.py
```

The portable wrapper may be invoked from any working directory. Its three
underlying checks can also be run separately:

```sh
python3 matrices/check_restricted_L.py
python3 seed/check_seed_reflexivity.py
python3 source_counterexample/check_local7_source.py
```

Saved receipts are generated from these checks. The optional seed builder
uses the copied upstream `hilbert.py`, unchanged and retaining upstream
attribution. No proof-search results are needed to replay the included
certificates.

Repository snapshot: `704b87442afbd571833a628cd558f1d207fd8b2f`.

The goal of at most 217 states remains unfulfilled by this evidence packet.
