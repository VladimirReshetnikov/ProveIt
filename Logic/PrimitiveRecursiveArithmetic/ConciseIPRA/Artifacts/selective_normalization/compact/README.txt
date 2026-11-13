FULL-JSON COMPOSITION OF THE EXISTING FLOOR-PRODUCT REWRITING

Status: a verified implementation composition; not a new mathematical
axiomatization and not a solution of the requested simultaneous size target.

The complete standalone checker code/checker269.py implements exactly the
same raw guarded calculus as controls/checker271.py. It reads the same one
complete JSON array, including multiline JSON, takes its final element as
the public goal, and consumes preceding three-field packets from right to
left. No input framing or success-message change is made.

Measured complete-module sizes (CPython 3.12.14; ast.unparse plus a final LF):

                                  Tokens   AST nodes   UTF-8 bytes
controls/checker271.py                 255         271          606
code/checker269.py                     255         269          605

The candidate is two AST nodes and one normalized byte smaller. It is NOT
below the current R/U envelope 249/271/477 in tokens or bytes. The new local
comparison contributes the upper bound 269 for full-JSON AST size, if this
particular composition was not already counted in a larger uninspected
corpus. No claim of global minimality is made.

This change composes a known rewriting from the repository's fused_iteration
package with the full-JSON three_field checker. The article states the
rewriting as Proposition cert:prop:stream-rewrites(a), applied there to a
line-stream checker. Here it is applied to the same kernel with the original
complete JSON framing. The proof does not depend on framing.

The contract remains R/U: the external numerical data are finite exact
integers and lists and the public goal is assumed to be a canonical closed
guarded Eq/D formula. This small checker does not independently validate the
entire public grammar or exact-integer alphabet. Intermediate raw aliases
are permitted by the inherited protocol. It is not a T/ed typed checker.

Reproduction, from this folder:

    python3 verify.py
    python3 code/checker269.py < tests/local/computation_zero_local.json

The second command prints ACCEPT. The first compares both complete programs
on all 20 inherited fixtures under normal Python and Python -O, yielding
80 process executions, and writes verification.json. It also reports the
complete-module sizes. The source files, comments and imports of the readable
expansion are not the measured candidate; that file is explanatory only.

PROOF.txt supplies the universal operational-equivalence argument, which is
the correctness evidence beyond finite testing. PROVENANCE.json identifies
the exact pinned upstream paths and verifies every inherited fixture by its
Git blob SHA and SHA-256. The pinned revision is
12197d86f63e9ec73b2d91399c4de2a8cb0077ee.

The original theorem-level bi-interpretation with iPRA is inherited. This
composition changes no axiom, no inference rule, no formula translation,
no numerical domain and no equality interpretation. It does not supply a
new proof-assistant verification of the Python implementation.
