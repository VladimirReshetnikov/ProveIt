# Order-Ten Harmonic-Tail Reconstruction and Polylogarithmic Stieltjes Generators

This package is an integration-ready research continuation for the ProveIt polylogarithm program, prepared against repository commit `04bf92d507588a26abadbaee1beb1e7350c8bffb` on 11 October 2026.

At the final repository observation, `main` had advanced to `81d05cb50cf2d302f5e450e46cc18c1def95c8d2`. No file under `Analysis/Polylogarithms` changed in that comparison; one later binary archive, `docs/incoming/ProveIt_Lerch_Selectors_2026-10-11.zip`, was added. The mathematical audit and all local novelty statements therefore remain explicitly pinned to `04bf92d5`.

## Principal result

For every integer `b >= 6`, the exact rational matrix `M_{5,b}` governing the unequal even harmonic-tail pair `(p,q)=(10,2b)` is nonsingular. Equivalently, the first `q=2b` centered moments have full formal rank in the source coordinate space.

The proof combines:

1. the inherited effective theorem covering all `b >= 1920`; and
2. a new exhaustive exact certificate for `6 <= b <= 1919` over the prime field `F_1000003`.

For `b=6,7,8,9` the certificate uses the direct source determinant. For `10 <= b <= 1919` it uses the exactly equivalent retained `5 x 5` determinant. All 1,914 residues are nonzero. Their canonical SHA-256 digest is

```text
3977e54f5b43e8f080c32f2e5b22beac54412cca32ff5d03d84975111836
```

Two implementations replay the entire finite calculation. They use different Bernoulli recurrences and different determinant algorithms.

## Additional exact results

The article also proves:

- ordinary absolutely convergent identities reconstructing every coordinate `zeta(2k)` from products of order-ten and order-`2b` harmonic tails, equivalently products of polygamma functions;
- a fully expanded `(10,16)` identity for `zeta(2)`;
- a depth-two multiple-polylogarithm generating function for products of two Hurwitz tails;
- a bivariate pole-subtracted multiple-polylogarithm kernel generating every product `gamma_r(n+1) gamma_s(n+1)` of generalized Stieltjes constants at integer shifts;
- the closed digamma-square generator and an anchored special value at `z=1/2`.

Novelty is asserted only relative to the inspected ProveIt corpus. The article is an unrefereed research draft and is not proof-assistant formalized.

## Package map

- `article.pdf` — compiled article.
- `article.tex`, `preamble.tex`, `sections/`, `references.tex` — modular LaTeX source.
- `article_singlefile.tex` — expanded standalone LaTeX source.
- `verification/` — exact certificate, independent replay, rational identity derivation, and numerical diagnostics.
- `provenance/` — repository snapshot, source audit, and claim ledger.
- `integration/` — suggested manuscript placement, status updates, and a namespaced integration fragment.
- `BUILD.md` and `Makefile` — complete replay and build instructions.
- `CHECKSUMS.sha256` — integrity manifest for package files.

## Fast replay

```bash
python3 verification/run_all.py
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

Or:

```bash
make all
```

The exact scripts use only the Python standard library. The numerical diagnostics additionally require `mpmath`; the PDF requires a normal TeX Live installation with `latexmk`.
