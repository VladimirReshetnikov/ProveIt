# Combined ten-integer consistency equation

The recommended combined instance is generated/b4_signed10.json, with its
active fixed values in data/INSTANCE.json. It incorporates both new ideas:
B4 additive source coding and the complete nonzero683195 compiler tuple.

| Property | Value |
|---|---:|
| Unknowns | 10 unrestricted integers |
| Exact degree | 107286763576 |
| Binary arithmetic operations | 2204 |
| Native base | 2^683195 |
| Largest native port | 688546 bits |
| Source margin constant | beta_S=2^2743514 |
| Four native payloads, uncompressed | 342269 bytes |
| Four native payloads plus beta_S, uncompressed | 685209 bytes |

ZFC proves that the equation has no integer solution if and only if
Con(ZFC), for the pinned repository's proof predicate. This imports the
same universal K215, ordinary compiler/Pell and Sun2026 theorems as the
comparison construction. It is not a new consistency proof or an
end-to-end formal certificate.

The arithmetic graph is identical to ../ten_integer/generated/b4_signed10.json,
but all four compiler ports and beta_S have been rebound coherently.
These two fixed polynomials are distinguished by their data/INSTANCE.json
bindings. The complete parent transfer, positivity obligations, new
coefficient bounds, exact degree and dependency boundary are in PROOF.md.

## Reproduce

From any working directory, run these scripts using their actual paths;
from this folder, use:

    python3 regenerate_binding.py
    python3 b4_code.py
    python3 build_b4_sun10.py
    python3 verify_b4_sun10.py

Only Python's standard library is required. The first script reads the
sibling ten_integer source parent/recipes and coefficient_backend fixed
payloads. These folders must be present, as they are in the delivered
archive. It regenerates every active coefficient binding and all 402
individual bounds. The native backend can itself be rebuilt first with
its own three documented commands.

The builder emits only the main structural-quintic circuit. The verifier
checks the full tuple byte identity, reconstructs all 402 coefficients
from the literal parent, verifies the B4 code and formal norm identity,
compares the circuit against independent literal formulas, proves its
arithmetic graph matches the comparison instance, and checks nonzero
leading coefficients at three primes. Runtime for all four commands was
about two seconds on the development machine.

Independent audits are in ../review/audit_b4_independent.py and
../review/audit_composed_binding.py, with separate composed receipts.
The first accepts this folder as its first positional argument and a
receipt path as its second. The second resolves this folder from its own
location by default and accepts the same two positional arguments.

## Fixed data and conventions

- COMPOSITION_BINDING.json records the complete coherent tuple and exact
  payload hashes, including the new beta_S.
- data/INSTANCE.json is the active instance. The historical tuple metadata
  within the byte-preserved parent JSON is source evidence only.
- data/parent_quartic31.json is the same literal 22-residual parent as in
  the comparison construction.
- data/constants.json gives all 402 factorial-weighted coefficients as
  fixed polynomials in the four ports, with the B4 exponents.
- data/index_bound.json records each independently checkable size bound.
- No unknown parameter, machine index, input digit or witness is hidden
  among these fixed data.
- Parent z is the old transport coordinate z_old=z_new+1. Parent y is
  unchanged. All 31 positive parent coordinates are then shifted by one
  when defining the natural-variable source polynomial.
- Parent i is the ordinary multiplier; it is not P67's normalized
  multiplier. Their canonical relation is i=Delta*i_P67.

Provenance is recorded in SOURCE_PINS.json and NOTICE.md. The retained
source proofs and their original licenses are included.
