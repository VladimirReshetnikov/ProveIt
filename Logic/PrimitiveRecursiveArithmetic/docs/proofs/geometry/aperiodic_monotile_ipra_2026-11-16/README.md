# Aperiodic planar monotile in iPRA

This research packet recasts the hat monotile theorem as a finitary theorem of
intuitionistic primitive recursive arithmetic.

## Primary artifacts

- `aperiodic_monotile_ipra.tex` — full human-readable argument.
- `aperiodic_monotile_ipra.pdf` — compiled 17-page report.
- `certificates/` — exact hat, substitution, and coupling constants.
- `tools/verify_hat_certificate.py` — standard-library exact-arithmetic verifier.
- `generated/verification_report.json` and `generated/exact_geometry_stats.csv` —
  verifier outputs.
- `lean/` — detailed Lean/ProveIt formalization scaffold.
- `FORMALIZATION.md` — staged path to a complete kernel proof.
- `VALIDATION.md` — commands run and status of each claim.

## Reproduce the exact checks

```bash
python tools/verify_hat_certificate.py --levels 6
```

Expected first line:

```text
PASS: exact hat and substitution certificate
```

The proof-relevant verifier uses only the Python standard library.  Figure regeneration
also uses Matplotlib:

```bash
python tools/make_figures.py
```

## The internal iPRA statement

Because first-order arithmetic cannot quantify over arbitrary sets of real polygons, the
report proves an arithmetical certificate sentence:

1. one fixed primitive-recursive coherent sequence of exact finite hat patches covers
   every requested lattice ball; and
2. every finite torus code purporting to describe a periodic hat tiling is rejected.

A constructive finite-state lemma turns one period into a finite torus, and the standard
interpretation of the coherent patch stream gives an explicit computable plane tiling.

## Formalization status

The mathematical argument is fully developed at the human/certificate level.  The Lean
files are an outline and intentionally retain `sorry` obligations.  They were not
compiled because Lean was not installed in the artifact-generation environment.  No
kernel-checked iPRA derivation is claimed in this archive.
