# An auxiliary shift can be removed

This component supplies two fixed integer polynomials in ten strictly
positive integer unknowns whose absence of positive zeros is provably
equivalent in ZFC to Con(ZFC):

| File | Live binary operations | Exact total degree |
|---|---:|---:|
| `equation77_degree630.json` | 77 | 630 |
| `equation78_degree468.json` | 78 | 468 |

They remove one addition at unchanged degree from the 78/630 and 79/468
equations in the latest inspected incoming certificate-reductions archive.
This is a small arithmetic reduction, not a new variable-count record or a
global optimum. Its new lemma excludes main Pell index three using a shared
divisor of two coordinates. The resulting signed transport argument proves
that the old `T+alpha` shift was unnecessary.

`PROOF.md` gives every formula, the sign-sensitive argument, an explicit
bijection of positive zero sets, and the exact inherited proof boundary.
The full coefficient payloads and their finite reconstruction are included
under `upstream/`; no symbolic coefficient port is left unspecified.

Reproduce using Python 3.10 or newer and its standard library:

    python3 -B build.py --check
    python3 -B verify.py
    python3 -B -O verify.py

The checker proves local polynomial identities and global degree statements,
authenticates and reconstructs fixed coefficients, checks three new algebraic
identities used in the proof, and rejects ten actual circuit corruptions per
equation. These checks do not substitute for the unbounded mathematical
argument. Normal and optimized receipts are included.

The component is pinned to ProveIt commit
`e0c98c629bf10d30b695884f6b1d2ab361bdf513` and does not alter the repository.
No new complete Lean/Rocq or internal-ZFC proof object is asserted. New work
was prepared with AI assistance; inherited notices and licenses remain intact.
