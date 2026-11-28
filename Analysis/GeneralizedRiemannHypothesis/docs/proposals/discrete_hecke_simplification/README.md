# Discrete local Hecke estimates: two proof simplifications

A source-based mathematical proposal for the readable Lean proof of RH and Dirichlet GRH in ProveIt. The primary change replaces the Pieri-cone volume calculation by signed integer-lattice enumeration; the second counts bad Smith directions by a direct saturation argument over valuation domains. Both recover the existing upper-bound contracts.

## Contents

- `discrete_hecke.tex`, `discrete_hecke.pdf`: paper-level derivations and source integration analysis.
- `LEAN_PLAN.md`: staged implementation contracts, validation and deletion plan. No compiled Lean code is claimed.
- `checks.py`, `checks.txt`: executable dependency-free exact-arithmetic regressions and actual output.
- `source_manifest.tsv`, `verify_sources.py`: pinned Git blob and tree identities, and a verification script for a local checkout.

## Reproduce

```
latexmk -pdf -halt-on-error discrete_hecke.tex
python3 checks.py
python3 verify_sources.py /path/to/ProveIt
```

The source manifest is grounded in GitHub connector retrieval at `cdecfeba5d834fbf2f97de71cc7766b58ec4520e`, including twelve proposal trees. Proposal nonduplication was checked at README scope and selected relevant report sections; a broader automated TeX scan exceeded the connector call budget, so exhaustive full-text nonduplication is not claimed. Selected source blobs were confirmed at the pinned commit. The local checkout verification script was not run because a checkout was unavailable. The Python tests ran successfully. The PDF was compiled and rendered for inspection. No Lean executable was available; the proposed replacements have not been kernel checked and no repository edits were made. Affected source regions are not measured deletions or a net line-saving estimate.
