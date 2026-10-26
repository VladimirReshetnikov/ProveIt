# Explicit Pell orientation and projection equations

The principal `integer84_degree2097808` equation is a completely specified
ordinary polynomial in 84 unrestricted integer variables. It has 23 residual
squares, exact degree 2,097,808 and 2351 binary arithmetic operations in the
supplied evaluator. A 2379-operation graph for the same polynomial has literal
integer leaves of magnitude at most 256. The full ordinary proof, composed with
the named inherited C222/ZF/ZFC calibration, proves in ZFC that lack of integer
zeros is equivalent to Con(ZFC).

The construction uses the credited linear orientation lemma of ProveIt
source136, the CRT-index anchor of source173, the incoming Cofinal Pell
Compression five-base pool, and exact unit substitution. The delivered
coefficient and circuit composition is the contribution; no claim of a new
orientation principle, global simplicity minimum, or proof of consistency is
made. See `PROOF.md` and the containing report.

`PROFILES.json` is the authoritative measured table. The matched old-source
control has 85 variables, 24 residuals, the same degree, and 2382 operations.
The source205 and the120-variable degree32 choice provide lower-degree
alternatives within this exact composition. The latter is not a claimed global
degree32 frontier.

## Offline verification

Python 3.10 or later and only its standard library are required:

    python3 -B verify.py
    python3 -B -O verify.py
    python3 -B independent_review.py
    python3 -B build.py --check

The two verifiers import neither the producer nor search code. They bind every
literal expression block and complete sum-of-squares output without expanding
the enormous high-degree polynomial. Search scripts using SciPy are optional
research tools; verification and reconstruction do not require SciPy or network
access.

## Evaluate a supplied tuple

    python3 -B evaluate.py integer84_degree2097808 --variables
    python3 -B evaluate.py integer84_degree2097808 tuple.json --residuals
    python3 -B evaluate.py integer84_degree2097808 --zero --modulus 1000000007

Use `--restore` to obtain all206 modified-source coordinates. High-degree exact
evaluation can produce very large integers. A modular zero is not an integer
solution. The evaluator performs no root search or consistency decision.

## Files

- `equations/`: every literal graph and its degree/input certificates.
- `source206.json`: the complete modified source, with the expanded pool.
- `parent206.json`: byte-exact inherited206 source.
- `factored_pool.json`: a compact complete definition of its final large row.
- `orientation_certificate.json`: the exact old, triangular and affine row
  identities, every shifted coordinate and every pair index.
- `certificates/`: the finite unit-pivot selections; no search is needed to
  reproduce them.
- `PROOF.md`: the proof, source boundaries, comparisons and limitations.

The containing release retains the unmodified dependency archive
`ConZFC_Cofinal_Pell_Compression_2026-10-25.zip` and source136 attribution and
license material. The inherited proof-assistant development was not rebuilt.
