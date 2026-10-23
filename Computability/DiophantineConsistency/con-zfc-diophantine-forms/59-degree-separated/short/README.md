# Short-polynomial frontier synthesis

New fifteen-positive-variable (operations, exact degree) pairs:
67/125, 68/101, 69/91, 70/84, 71/80, 72/74, 73/60, 74/50, 75/46.
New fourteen-positive-variable pair: 79/52 (previously 79/56).

The inherited absolute operation record, 66/157, is unchanged. The included
76/44 reconstruction is explicitly a historical reference, not a new result.
These are bounded improvements among the authenticated repository artifacts,
not global minima or a new theoretical method. They combine the existing
squared-modulus quotient, ordinary strong rank, Pell-root gaps and, for
14 variables, the existing quotient absorber.

Every equation has no positive-integer solution iff Con(ZFC), provably in
ZFC at the ordinary mathematical level of the inherited calibrated compiler.
There is no new end-to-end Lean/Rocq or formal object-language certificate.
Finite tests are not a consistency test or substitute for the semantic proof.

Files:
- report.tex/report.pdf and section.tex: readable compact report.
- PROOF.md: full local reduction, positivity, signs, comparison and degrees.
- circuits/: eleven complete division-free literal JSON evaluators.
- build.py: newly authored deterministic generator, no upstream code import.
- audit.py/AUDIT.json: independent stdlib exact degree, liveness, byte and formula audit.
- COEFFICIENT_BINDING.json and coefficients/: complete Wang943 121×8801 tuple.
- upstream/: authenticated inherited proofs copied as text, never executed.
- SOURCE_PINS.json: archive pin 4b4349064a750ba6347293b55874a7f92abdd0db,
  placement pin 6d375f2d2deac0519e659bbce5b48087023c1430, archive and member hashes.

Reproduce: python3 build.py; python3 audit.py; python3 -O audit.py.
Compile report.tex twice with pdflatex. All arithmetic operations are charged,
including multiplication by fixed constants. There are no hidden unknowns.

All four fixed ports are one coherent tuple with B=2^1064921. MF is already
shifted. Historical relative links in upstream text and original_binding.json
are inert; the active local coefficient adapter path is in the binding above.
No external repository or earlier release was modified.
