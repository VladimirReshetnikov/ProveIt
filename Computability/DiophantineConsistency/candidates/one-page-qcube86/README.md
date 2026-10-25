# An 86-operation comparison equation on one page

[equation.pdf](equation.pdf) and its standalone [TeX](equation.tex) specify
one complete equation in ten strictly positive integer unknowns. Its live
binary evaluator uses **86 operations**:51 multiplications,19 additions
and16 subtractions. Its exact total polynomial degree is **466**. The
four fixed integers,943 indexed tiles,430-action decoder, ordered alphabet
and entire436-character numeral are printed on the same Letter page in
9-point body type. No external table or executable is part of the printed
specification. The extracted page has3,101 nonwhite characters.

This is an operation/degree tradeoff. Against the accepted89/288 alternative
it saves three operations and increases the degree by178. Against the
canonical92/283 page it saves six operations and increases the degree by183.
The canonical equation, PDF and TeX remain unchanged. No degree improvement,
global operation minimum or canonical promotion is claimed.

The [ordinary proof](../../research/ten-positive-qcube-normalization/PROOF.md)
replaces the old input Y by positive s, defines Y=q³s inside the actual
polynomial and removes an integral center contribution. A common q³ factor
then cancels from the whole cleared numerator and denominator. Its identity
with the old equation uses n_old=n_new-s, which can be nonpositive. The new
soundness proof therefore establishes the transport sign directly using
positive n_new before invoking the later rank, congruence, whole-product
projection and native-source arguments. Completeness uses the actual
canonical condition q³|Y and the positive forward map n_new=n_old+Y/q³.
It does not assume generic cofinality or a positive reverse shear.

The degree466 proof applies to the entire polynomial: it binds all front
components, an exact cancellation identity and the full nonzero105-term
leading form. Exact polynomial evaluations on lines supplement that
global argument. The page retains the whole proof packet's86 gates.

The four printed constants form the complete separately calibrated indexed
BFS tuple. The full constant body is copied verbatim from the sealed
[indexed standalone TeX](../../research/indexed-tile-enumeration/equation.tex),
including the entire alphabet, seed, decoder and corrected initializer.
The ordinary source theorem applies uniformly to all four ports and
composes with that same indexed native/selector/controller instance.
Different K specializations are not equated or mixed. polynomial.json
binds all four alternate ports, including their complete raw and gzip
payload hashes and bit lengths. MF_source's shift is retained exactly once.

The printed A is the source register Am1=mu*Y*(X+1); the proof's Pell base
is A+1. E denotes Dtau, b' denotes cTR and M is the reduced denominator
q_minus*mu²*H. Y is an evaluated abbreviation, while s is one of the ten
independent positive inputs. The boxed polynomial is the complete output.
Floors, fixed sums and quotient/remainder occur only in constant definitions.

The [renderer](../../tools/render_qcube86_page.py) authenticates the two
complete closed source inventories and their exact reviewed seals. It
checks all86 live gates against its complete displayed formula schedule
over four free coefficient ports, using exact associative/commutative
arithmetic, and jointly copies the four whole indexed payloads. It verifies
the entire constant body, seed, alphabet, Greek glyphs, one-page size and
absence of overfull boxes. VISUAL_REVIEW.json records the author inspection.
Independent actual-TeX/PDF review and printed counterexample controls are
recorded separately in the PEER_* files before sealing. That work is outside
the renderer author's scope; no peer file is authored by this page's author.

Reproduce from the repository root, keeping stdout outside this packet:

```sh
python -B Computability/DiophantineConsistency/tools/render_qcube86_page.py --render > /tmp/qcube86-page-render.json
python -B -O Computability/DiophantineConsistency/tools/render_qcube86_page.py > /tmp/qcube86-page-optimized.json
```

The ordinary theorem is absence of positive solutions iff syntactic
Con(ZFC); neither side is asserted. This page is a finite specification,
with the proof retained separately. Internal-ZFC formalization and native
calibration remain open in Lean. No Lean command, earlier sealed packet,
canonical page or common document is changed by this comparison.
