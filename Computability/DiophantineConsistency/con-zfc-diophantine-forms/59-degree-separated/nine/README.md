# Degree-separated nine-variable consistency equation

Primary files: `report.pdf`, editable `report.tex` and `section.tex`, and the
complete mathematical proof `PROOF.md`.

- Nine positive unknowns: `generated/split_116_positive.json`.
- Exact total degree: **2,676,548**.
- Live binary circuit cost: **476** (164 additions, 23 subtractions, 289 multiplications).
- Nonnegative-domain translate: `generated/split_116_natural.json`, same degree, 480 operations.
- Exact diagonal leader: `2^542 a^1337768 c^400`, with `a=2^2134939`, `c=2^17079502`.

The source's new structural feature is degree-separated extraction, not a
claim to eliminate quantified source variables. It combines a certified
89-record source with the sparse +1 carry mask, an even-parameter parity
calibration, exact CRT witness substitution, and the positivity-first Pell
norm. No new consistency proof or global minimum claim is made.

The old package31 whole tuple is intentionally retained for the primary
source. The newer packet52 whole tuple is retained separately only for the
three comparison circuits. The source presentations differ in residual15
by `-beta*J`; this is independently checked, never silently ignored.

## Rebuild and check

Only Python's standard library is needed. From the enclosing package root:

    python3 nine/build_nine.py
    python3 nine/verify_nine.py

The builder regenerates all 16 primary/comparison, positive/natural, and
degree-certificate circuits. The verifier authenticates the two tuples,
checks the exact source expansions and extraction conditions, replays
480 complete modular assignments, and runs the stated algebraic and
finite-boundary audits. The result is `generated/VALIDATION.json`.
The verifier deliberately rejects optimized Python (`-O` and `-OO`).

Each fixed leaf is reconstructed from its circuit's exact coefficient
recipe and the indicated whole tuple. Tuple payloads use unsigned
little-endian encoding; gzip is storage compression, not an arithmetic
operation. All powered coefficients are ordinary fixed integers.

The certified primary degree DAG is a separate, larger evaluator; its cost
is not the primary cost. Known-power reuse only changes the straight-line
evaluation, not the polynomial. The live cost counts all scalar products,
squares, and fixed-power multiplications.

## Remaining frontier

The independently composed `174_interior_regular_positive.json` uses
475 operations but degree 9,336,884. It is a one-operation tradeoff, not
dominated in both metrics. The two other preserved native-tuple comparisons
have degree/cost 6,125,108/577 and 6,339,380/515. None improves on the primary
degree. These are local comparisons, not a complete literature frontier.

## Scope and imported semantics

ZFC proves existence of a zero equivalent to a finite syntactic ZFC
refutation, given the explicitly identified original compiler and Jones
ratio theorems. Taking negations gives no zeros iff Con(ZFC). This is an
ordinary mathematical reduction, not a new end-to-end kernel certificate,
and not a nine-unrestricted-integer theorem.

The polynomial source and full coefficient-adapter proofs are retained
under `data/`, `coefficients/`, and `upstream/`. `SOURCE_PINS.json` binds
them. The finite checks audit implementation and fixed data; they do not
decide consistency or prove the inherited unbounded compiler semantics.
