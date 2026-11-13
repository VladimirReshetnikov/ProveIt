VERIFIED REFINEMENTS OF iPRA PRESENTATIONS
12 November 2026 — prepared for Vladimir Reshetnikov

STATUS: PARTIAL RESULT. The requested new axiomatization below all current
compact complexity minima was not established. No arithmetic axiom is
deleted. The files contain verified implementations of the existing theory,
explicit interpretation arguments, and an obstruction to an unsafe logical
simplification.

START HERE
  ipra_verified_refinements_2026-11-12.pdf
  ipra_verified_refinements_2026-11-12.tex
  CLAIMS.json

PINNED BASELINE
  VladimirReshetnikov/ProveIt
  42fba2a76aea6eb41a8c4acfe7761620f58956ee
  Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/

Including the three current incoming ZIP archives, the compact coordinate
envelope is 249 significant tokens, 271 AST nodes, and 495 normalized bytes.
Those numbers belong to three different programs. They are observed records,
not a universal impossibility bound.

RESULTS
  Profile       Matched control       Proposed (tokens / AST / bytes)
  Compact       267 / 299 / 495        267 / 298 / 492
  Native        325 / 375 / 641        324 / 374 / 629
  Strict        342 / 391 / 666        334 / 387 / 654

Compact: inherited canonical closed guarded Eq/D public-goal contract, with
finite integer/list certificates. It does not add public grammar validation.

Native: validates the full closed native Eq/D goal. The correctness theorem
uses finite integer/list certificates; unused JSON prefixes may contain other
values. Do not confuse it with the stricter alphabet contract.

Strict: validates the full closed native Eq/D goal AND the entire certificate's
exact integer/list alphabet, including unused prefixes. This is the convenient
interface when submitting JSON directly.

Each checker reads a JSON array from stdin, consumes its last element as the
public goal and earlier proof instructions from right to left, and accepts
only by successful exit with exactly ACCEPT followed by a newline. Instructions
have the inherited four-field format [m,s,u,t]. Consult each profile's argument
and the included inherited_arity_checker.tex for the exact decoder and rules.

OFFLINE REPRODUCTION
  python3 verify_manifest.py
  python3 reproduce.py

Use CPython 3.12.14 to reproduce the frozen AST/token/byte values. The verifier
uses only the standard library and starts the control and candidate in isolated
ordinary and optimized Python processes. There are 452 process checks and no
observed failures. A different Python release may change ast.unparse output.

The verifiers regenerate their receipts. Check the original archive manifest
before regenerating files, especially on another Python/platform version.

PDF REBUILD
  python3 build_pdf.py

A normal TeX Live installation is needed. The helper first tries its installed
pdfLaTeX format. If the installed format/cache is missing, it creates a private
format from installed TeX sources, without downloads or global changes.
It compiles three passes and preserves a build log. Normal latexmk also works
in a conventionally configured TeX installation.

OPTIONAL SOURCE CENSUS
  python3 census/census.py
  python3 census/audit_incoming.py
  python3 census/inspect_exclusions.py
  python3 census/summarize.py

The supplied source manifests pin every download by Git hash. Running the
census may need internet access. It parses sources but never imports or executes
downloaded programs. The recorded audit includes all 1,446 Research Python blobs
(5,935 paths) and every Python member of the three incoming archives.
One docstring-only class creates an invalid empty suite under the shared
normalization convention; its explicit exclusion record is far above the minima.

MATHEMATICS
The report states the complete inherited native rules, reconstructs ordinary
intuitionistic logic, specifies the whole-domain ordinary realization, and
explains both interpretation composites. The internal predecessor, equality-
reflection, primitive-recursion compiler, and bytecode-decoder proof sources
are included with attribution under reference/.

The new rule-level obstruction shows why allowing progressive introduction
at Q-rooted matrices recovers arbitrary-formula induction, even with guarded
Eq/D public goals. The typed hypothesis-only repair is distinguished from an
uncompleted low-level compiler proof.

LIMITS
- This does not meet the full requested new-axiomatization target.
- The 492-byte checker does not beat 249 tokens or 271 AST nodes.
- The two validated interfaces are separate comparison classes.
- Test agreement supplements written proofs; it is not a universal proof.
- No new Lean/Rocq verification is claimed.
- No repository mutation, publication, or pull request was made.

The upstream MIT license and original source attribution are retained.

