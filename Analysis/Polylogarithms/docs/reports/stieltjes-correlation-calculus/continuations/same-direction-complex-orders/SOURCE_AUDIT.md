# Source audit and provenance

This is a targeted continuation audit, not an audit of all four manuscript
volumes or all historical incoming packages. Repository reads used the
connected GitHub reader. No remote writes were performed.

## Pinned mathematical sources

Repository: `VladimirReshetnikov/ProveIt`.
Mathematical source pin:
`92f8c8e749e87e7e22779a0d2a12f9f21b2d5583`.

### The preceding integer master

Path:
`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/bilinear-mellin-hurwitz/sections/03-master.tex`

Blob: `b6c43f9e5664e8d910d7df7f3471a9139fb8733b`.
Read at the pin above, including the entire connected-coordinate definition,
shift/stuffle proof, finite transform, two-cone proof, boundary cancellation,
and integer logarithmic example.

This supplies the inherited formula which Theorem 3.4 recovers exactly.
The positive-integer theorem is not treated as an unresolved conjecture.

### The explicit continuation question

Path:
`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/reciprocal-lerch-convolutions/sections/12-research.tex`

Blob: `cf776f3713d5f9fc3ee8a5cc4d0266d2589f7d8f`.
Read at the same pin, in full.

Question 8 asks for a same-direction spectral representation beyond integral
orders, holomorphic in both orders and specializing to the preceding finite
double-Hurwitz master. That representation question is the direct target of
Theorems 3.2, 3.4 and 4.3. Generic finite closure is kept separate.

## Additional contextual reads

Path:
`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/reciprocal-lerch-convolutions/sections/01-scope.tex`

Read through `main`; returned blob:
`c730623eed219a1642cddca0c7a58cdca981a8af`.
The source explicitly distinguishes reciprocal geometry from the
same-direction integral. This paper preserves that distinction.

Path: `Analysis/Polylogarithms/docs/manuscript/README.md`.
Read through `main`; returned blob:
`48700d499f8e0481cddf7eade2bc962fe8eb67ba`.
The canonical README supplied context on integrated versus pending claims,
including the proved S4, conjectural S6 and revised S8, and the distinction
between finite replay and analytic proof integration. Its historical counts
are not used as a current completeness claim here.

The directory `Analysis/Polylogarithms/docs/manuscript` and the directory
`docs/incoming` were also listed. Search excerpts helped locate the two
pinned report files; mathematical conclusions are based on their full reads,
not on snippets alone.

## Incoming contents not inspected

The incoming directory listing returned these six ZIP filenames:

1. `ProveIt_Bernoulli_Tornheim_Digamma_2026-10-11.zip`
2. `ProveIt_Cubic_Tail_Descent_2026-10-10.zip`
3. `ProveIt_Determinantal_Harmonic_Resonance_2026-10-10.zip`
4. `ProveIt_Differential_Polygamma_and_Lerch_Jets_2026-10-11.zip`
5. `ProveIt_Multishift_Reflection_2026-10-10.zip`
6. `ProveIt_Polygamma_Tail_Identities_2026-10-11.zip`

Their compressed contents were not obtained or inspected. The GitHub text
reader does not supply binary downloads, and attempted runtime retrieval
was unsuccessful. A filename is not mathematical evidence of the claims
inside. The October 11 dates above reproduce the returned filenames; no
chronological conclusion is inferred from them.

Therefore this delivery cannot certify non-overlap with those archives or
correctness of their contents. It does not claim to be a comprehensive
review of all material in the two linked directories.

## External literature and conventions

Primary-source pages consulted:

- NIST DLMF §§5.12, 25.11, 25.12, 25.14: beta, Hurwitz zeta, polylogarithms,
  Lerch transcendent, and associated standard conventions.
- Jonathan Sondow, *A Faster Product for Pi and a New Integral for ln(Pi/2)*,
  arXiv:math/0401406; Euler transformations are classical.
- Mark W. Coffey, *Some definite logarithmic integrals from Euler sums, and
  other integration results*, arXiv:1001.1366.
- Michael E. Hoffman and Markus Kuba, *Logarithmic integrals, zeta values,
  and tiered binomial coefficients*, arXiv:1906.08347.
- Hidekazu Furusho, Yasushi Komori, Kohji Matsumoto, and Hirofumi Tsumura,
  *Desingularization of complex multiple zeta-functions*, arXiv:1508.06920.

The arXiv overview/abstract records establish the relevant prior themes and
bibliographic metadata; they are not a substitute for an exhaustive
statement-by-statement comparison with every theorem in those papers.
The article contains its own proofs of its claimed extensions.

No exhaustive priority search has been completed. In particular, the entire
connected family is an explicit difference family with C(A,B;1)=0, not an
unqualified new definition of multiple-zeta desingularization. Classical
transforms and low-weight evaluations are not advertised as global firsts.
