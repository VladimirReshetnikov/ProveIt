# Independent audit dossier

**Accepted with no required mathematical corrections.**

Audited source: `compatible-homogeneous-realization63-20261004`, main proof SHA-256 `31f0db773daa015075e74dabb8955c110288e1c0f9ed2121c647df034773aa67`.

- `REVIEW.md`: full source-bound conventional mathematical assessment and scope
- `independent_static_audit.py`: fresh inspected core checker; 840 assertions with historical originals, 832 in archive mode
- `evidence/`: final core results, independently recomputed LP vertices and translation margins, generic inert 26-rule declaration, source metadata snapshots
- `archive-mode-replay/`: successful portable-mode core replay
- `initial-run/`: preserved initial 836-assertion checker and evidence
- `certificate_audit/`: complete separate independent certificate/DAG audit, including its initial and portable final checker/evidence
- `certificate-parent-replay/`: 737-assertion replay of the inspected portable certificate checker from the assembled dossier
- `MANIFEST.json`: file hashes, byte lengths and source binding

Core replay, writing to a new directory outside the source packet:

    python independent_static_audit.py --source /path/to/source --output /path/to/new-output --archived-source

Omit `--archived-source` only when the historical absolute original paths in the source manifest are present and should be authenticated as well. The portable mode verifies every archived manifest and dependency-copy hash, performs all mathematical checks, and explicitly does not reopen historical originals.

Certificate replay, writing to another new output directory:

    python certificate_audit/check_certificate.py --source /path/to/source --output /path/to/new-certificate-output

The core requires SymPy 1.14.0; the certificate checker uses Python's standard library only. No checker imports or executes the source packet. All source proof/code/JSON artifacts are inert inputs. Neither replay performs physical simulation, next-event selection, saved physical schedule execution, or Lean checking.

The accepted scope is the exact local full-section criterion, its physical construction and strict guards, the rational endpoint decision, examples and conditional clocks, and the native degree-six positive-integer representation. It excludes a global cone or invariant-chamber realization theorem, a polynomial word-size bound, unrestricted repeated validity, finite-foldness, optimal resource counts, novelty or universality claims.
