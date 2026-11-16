# Von Mangoldt and Euler totient identities in iPRA

Prepared 2026-11-15 for Vladimir Reshetnikov.

## Main deliverables

- `von_mangoldt_totient_ipra.pdf` - the full human-readable proof development.
- `von_mangoldt_totient_ipra.tex` - LaTeX source.
- `THEOREM_INDEX.md` - compact claim-by-claim map and constructive status.
- `CLAIMS.json` - machine-readable claim ledger.
- `lean/FORMALIZATION_PLAN.md` - staged path to a complete Lean object-theory formalization.
- `lean/VonMangoldtTotientHost.lean` - mathlib-facing specification and host checks.
- `lean/VonMangoldtTotientObjectTheory.lean` - ProveIt/ConciseIPRA object-theory scaffold.
- `scripts/check_identities.py` - exact finite regression checker.
- `verification_report.json` - output of the checker.
- `sources/PROVENANCE.md` - source and revision record.

## Constructive status convention

The report deliberately distinguishes four kinds of result:

- **I** - a literal theorem of natural/integer-coded iPRA after denominator clearing.
- **F** - an exact finite coefficient, polynomial-remainder, or Dirichlet-convolution theorem; this is the iPRA content of an infinite generating-series notation.
- **A** - a constructive-analysis corollary obtained uniformly from finite iPRA certificates, usually rational enclosures for logarithms.
- **O** - not claimed: open problems or results needing a separate substantial analytic development.

The key Mangoldt device is a primitive-recursive prime weight `w`.  The exact arithmetic functions are

```text
L_w(n)      = sum_{p <= n, p prime} v_p(n) w(p)
Lambda_w(n) = w(p) if n = p^a, and 0 otherwise.
```

All divisor, Mobius, lcm, Chebyshev, and formal Dirichlet identities are proved uniformly for `w`.  Setting `w(p)=log p` is then a finite-precision constructive specialization, rather than an illicit real-valued primitive symbol in first-order arithmetic.

## Verification status

`verification_report.json` records **49,047 exact finite cases in 15 groups**, all passing.  The checks include totient product/count definitions, divisor and Mobius identities, Menon's identity, Euler orders, RSA for nonunit messages, the Subbarao composite classification through 5000, weighted Mangoldt identities, lcm quotients, binomial-lcm divisibilities, cyclotomic polynomial remainders, and the finite examples quoted by MathWorld.

This finite checker is regression evidence, **not** a universal proof or a Lean kernel certificate.  The universal proofs are in the report.  The supplied Lean files are scaffolds and specifications; they were not compiled in this execution environment because Lean/Lake was unavailable.

## Rebuild

From this directory:

```bash
python3 scripts/check_identities.py
latexmk -pdf -interaction=nonstopmode -halt-on-error von_mangoldt_totient_ipra.tex
```

The PDF used in the archive was compiled and rendered for visual inspection.  See `build/BUILD_REPORT.md`.

## Scope limitations

The archive does not claim the Riemann hypothesis, explicit formulas over zeta zeros, Carmichael's conjecture, Lehmer's totient problem, or a completed formalization in Lean.  It also does not silently identify host-level mathlib theorems with object-theory iPRA proofs.
