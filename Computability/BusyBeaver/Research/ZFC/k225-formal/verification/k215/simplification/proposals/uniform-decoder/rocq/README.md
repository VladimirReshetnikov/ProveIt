# Generic implication proof for the K215 research report

This is a focused proposal against ProveIt commit
`2ca3a5c16f0876d2cab842056353c03a1ed2f5f0`. See `findings.md` for the
mathematical rationale, exact scope, and integration plan.

## Deliverables

- `DominatedImplication.v`: generic 58-step Rocq proof, compiled and independently
  checked with Coq 8.18.0; all three public results are closed.
- `DomRho8Adapter.v`: thin adapter preserving the numerical `DomImp`/`rho8_all`
  API. The complete production Rocq 9.1 machine endpoint was not rebuilt.
- `expanded_proof.json`: explicit instances of the current Lean derivation;
  original source and expander hashes are recorded within.
- `check_and_render.py`: independent structural checker and ordinary Rocq
  proof renderer. It does no unification or search.
- `validate.py`, `checker_validation.json`: the positive check and five rejected
  malformed-certificate controls.
- `coq_core_check.json`, `lean_control.json`: focused check receipts.
- `verify_adapter.py`, `coq818_import_compatibility.patch`, `adapter_check.json`:
  isolated numerical adapter check, including exact dependency hashes and
  the explicit import-only compatibility adaptation for Coq 8.
- `adapter_check_attempt1.json`: retained failed elaboration attempt, repaired
  by supplying the abstract language explicitly to `Build_Restricted`.

## Reproduction

Python's standard library is sufficient for the structural checks:

```sh
python3 check_and_render.py --output DominatedImplication.v
python3 validate.py
```

The generic proof needs only Coq's default prelude:

```sh
coqc DominatedImplication.v
coqchk -silent DominatedImplication
```

The optional Coq 8 adapter check reads two pinned arithmetic modules archived
in the supplied ProveIt checkout. With an installed Coq 8.18:

```sh
python3 verify_adapter.py --repo /path/to/ProveIt --coq-bin /path/to/coq/bin
```

The script builds in `adapter_build`, changes the single modern `Stdlib`
import to the historical `Coq` spelling, records all four source hashes and
compiler outputs, and runs `coqchk` on the adapter's dependency closure.
This check is a portability pilot and is explicitly separate from adopting
the new proof in the full production Rocq 9.1 endpoint.

Original proof formulas and mathematical attribution remain those of the
repository. The new work is the generic Rocq port and explicit-instance audit.
