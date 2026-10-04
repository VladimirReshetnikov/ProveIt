# Independent review entry points

1. Review `PROOF.md` §§1–4 independently: transverse-flight inverse, event-coordinate identifications, translation quotient, complete-dimensionality assumption, sorted-gap determinant sign, and normalization obstruction.
2. Check the inert `RULES.json` against §5.1, especially the unchanged messenger at rule 4 and the two same-speed but distinct moving-X phase labels.
3. Derive §5.2's seven event rows directly from those speeds; check strict positivity and absence of extra contacts on 0<x<y<D, y<4x. The boundary y=4x consists of simultaneous distant events and is excluded by the stipulated strictly positive separated-flight convention.
4. Verify centering, return J, inverse J^(-1), and the speed-ratio product. `SECTION_AND_GUARDS.json` and `evidence/static_checks.json` are inert comparison data.
5. Review §7's extension using the frozen dependency `dependencies/POSITIVE_COMPILER_PROOF.md`; its original source is the preceding proof packet named in `MANIFEST.json`. Only its already-proved positive determinant construction is imported. No executable from that prior packet is needed.
6. If executing arithmetic, inspect and use only newly authored exact symbolic linear algebra. `static_algebra.py` was inspected before its original run; it imports no prior file and performs no physical collision selection, numerical trajectory simulation, or saved-schedule execution.

The packet's main mathematical dependency is the preceding positive compiler only for Corollary D's existence direction. Theorems A–C are proved directly here. Literature citations are positioning, not proof dependencies. No claim is proof-assistant certified, and no novelty or optimality claim is made.
