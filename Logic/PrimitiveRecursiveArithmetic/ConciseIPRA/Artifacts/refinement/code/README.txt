EXECUTABLES AND CONTRACTS

Run a checker as a complete standalone program:
  python3 code/checker_strict.py < certificate.json
Acceptance means exit code zero and exactly the line ACCEPT on stdout.
Exceptions reject. None of the measured programs uses Python assertions.

checker_compact.py
  The 488-byte complete module refining the upstream 495-byte profile.
  Its public theorem contract is the inherited closed guarded Eq/D language.
  It does not itself validate the full JSON alphabet or public-goal grammar.
  Administrative aliases are interpreted by the inherited sorted decoder.
  The representation of a successful return is True or a nested singleton
  list; proof continuations are evaluated eagerly before a list is returned.

checker_strict.py
  The same core with the published whole-JSON-alphabet test and the guarded
  public-goal validator. All JSON values, including unused prefix data, must
  be arrays or integers. The public goal must be a well-scoped closed guarded
  Eq/D formula. Auxiliary certificate fields still use the inherited
  permissive administrative decoder; this does not type every unused packet.
  The complete module is 855 normalized bytes, versus 862 for the EXACT SAME
  validator attached to the matched 495-byte control, or 869 for the older
  published strict program. Tokens and AST nodes increase in the matched
  862-to-855 comparison. This is not an all-coordinate improvement or a
  strict-checker size record.

checker_readable.py
  A separate readable implementation of the compact program. It preserves
  the major-proof check, context-first evaluation, mode selection before
  allocation, allocation before hypothesis opening, and eager computation
  of the source endpoint. The initial no-image scope scan remains in place.
  Its successful returns have the same recursive singleton-list structure.
  Its source size is measured but is not used for the compact-size claim.

two_field_reference.py
  The 742-byte two-field protocol reference supplied with this report.
  Computation equations are recognized directly as proof leaves. Other
  instructions contain a major formula and one payload. It is tested on
  separate two-field certificates and is not compatible byte-for-byte with
  the four-field fixture streams. The same compact guarded public-language
  qualification remains necessary; this program does not add a whole-JSON
  alphabet or public-goal validator. It is larger than the compact frontier.

BASELINES
The baseline directory includes the 495-byte matched compact control, the
862-byte matched strict adapter, the older published 869-byte strict checker,
the 249-token and 271-AST-node three-field profiles, and the 643-byte native
public-goal checker. The last is included as a measured contextual baseline;
the delivered suite does not claim a fresh audit of its different contract.

REPRODUCIBILITY
From the archive root run:
  python3 reproduce.py
This remeasures every standalone checker and executes the frozen test suite
both normally and with -O. Outputs are evidence/metrics.json and
evidence/validation.json. Measurements use ast.unparse normalization plus one
terminal newline, with CPython 3.12.14 as the reference runtime. The checker
modules import no test, measurement, translator or helper module.

The complete-module compact byte count decreases 495 to 488, while token and
AST counts rise 267 to 271 and 299 to 304. This is a source implementation
refinement. No new mathematical axiom deletion, absolute minimum, or overall
simplicity target is established by this package.

At a fixed interpreter resource limit, the nested return lists can consume
more memory or stack space than the control. The trace-equivalence argument
uses unbounded finite resources, as do the inherited completeness claims.

Attribution and exact source paths are in evidence/source_provenance.json;
the upstream license is baseline/LICENSE-ProveIt.txt.
