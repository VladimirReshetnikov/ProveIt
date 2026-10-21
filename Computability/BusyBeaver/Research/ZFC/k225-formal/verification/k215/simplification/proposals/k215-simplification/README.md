# Shorter correctness proofs for K215

This packet is pinned to ProveIt commit
`b6c7087477e51c017003bd729e712c8969733223`.

## Results

1. **A new compiled relative correctness proof for the existing CM215.**
   The exact conditional-marker machine halts iff the exact published K215
   does. The stronger theorem covers every initial binary tape and head
   position, from control 0. The actual `BusyBeaver.Core` and
   `KDense215.machine215` bridges are also compiled. The new proof and
   adapters total 363 lines, with generated table data counted separately.
2. **A smaller source certificate.** Quotienting paths by their implicit
   trailing zeros reduces 2,240 paired checkpoints to 1,426. The new generic
   Lean checker reuses the existing segment-bisimulation theorem. The
   complete concrete certificate, exact program/tree equalities, and
   unchanged public all-register source-equivalence theorem compile.
   Source-normalization receipts record the exact files and axiom reports.
3. **A generic positive-stuttering theorem in both assistants.**
   The Lean version uses only standard logical axioms; the Coq 8.18 version
   is closed under the global context and passes recursive `coqchk`.
4. **A reproducible scoped state-reduction investigation.** Six distinct
   215-state tables are searched for local folds. No verified 214-state
   machine is claimed. The search is not a state-count lower bound.

CM215 itself was already in the repository. This packet contributes its
short formal transfer proof, not a newly discovered machine. The existing
K215-to-ZFC calibration is reused explicitly. A complete fresh rebuild of
the inherited K215-to-ZFC closure is not claimed here.

## Contents

- `report.tex`, `report.pdf`, `results.tex`, `search-results.tex`: complete
  mathematical report and editable LaTeX source.
- `cm215/`: exact table inputs, new Lean proofs, actual repository bridge,
  fresh build records, attribution, and an offline rebuild driver.
- `formal/PositiveStuttering.v`: standalone Coq theorem.
- `source_normalization/`: normalized certificate, shared source data,
  Lean checker and reproduction material; see its README.
- `search214/`: six pinned native tables, local-fold search, independent
  controls, exact receipts, mathematical exposition, and reproduction driver.
- `evidence/`: Coq compiler/kernel logs, independent review notes, baseline
  build attempt, and the combined verification record.
- `manifest.json`: byte lengths and SHA-256 digests for the released files.

## Reproduce

The source and machine finite checks require Python 3.10+ and its standard
library. Keep Python assertions enabled. First check the released identities:

```sh
python3 reproduce.py
```

Recheck the standalone CM215 proof and its Core adapter with Lean 4.32.0:

```sh
python3 cm215/verify.py --lean /path/to/lean --output /new/cm215-check
```

To additionally recheck the connection to the exact published parent,
use the pinned checkout with `BusyBeaver.ZFC.KDense215` compiled:

```sh
python3 cm215/verify.py --lean /path/to/lean \
  --repo /path/to/ProveIt --output /new/cm215-repo-check
```

The retained six-module verification record used this latter command and
checked the repository attachment. The dependency build is separate from
the recorded 27.543 seconds of new-module compilation.

The standalone Coq proof uses only standard library imports and was checked
with Coq 8.18.0:

```sh
(cd formal && coqc PositiveStuttering.v && coqchk PositiveStuttering)
```

See `source_normalization/README.md` for the complete normalized-certificate
build. The longer state search is independently reproducible:

```sh
python3 search214/reproduce.py --search
```

Build the report with two passes, from this directory:

```sh
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

## Integrating the CM215 endpoint

When the existing `KEndpoint215` endpoint is in scope, instantiate the
already compiled parameterized transfer theorem with it:

```lean
CM215.inherit_calibration _
  SetTheory.BusyBeaver.ZFC.KEndpoint215.blank_halts_iff_zfc_refutation
```

The theorem's result is a halting/refutation equivalence for `machineFrom M`,
the exact CM215 table. Negating the equivalence gives the consistency
statement. This composition does not require re-proving the enumerator,
numerical calculus, runtime, or startup for CM215.

The normalized source development supplies a separate replacement of the
primary source-correspondence proof. Follow its integration notes rather
than importing duplicate definitions of the same source program.

## Attribution and scope

The primary K215 machine, CM215 machine, numerical calculus, ZFC calibration,
compiler, and inherited formal libraries remain contributions of their
original authors. Their notices and licenses accompany copied material.
New proof code, generators, search code, and this report may be incorporated
into ProveIt under its existing license. Compiler objects, toolchains,
temporary experiments, and a full copy of the repository are excluded.

`evidence/baseline-lean-attempt.log` records an incomplete broad rebuild.
It is retained to distinguish that attempt from the successful new theorem
checks: it encountered missing registration of an existing local dependency
and a resource failure in the large original source-data module. It is not
evidence that the repository's published endpoint proof is invalid.
