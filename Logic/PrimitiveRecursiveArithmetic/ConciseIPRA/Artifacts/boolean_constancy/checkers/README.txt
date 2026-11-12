SMALLER COMPLETE CHECKERS FOR THE INHERITED iPRA PRESENTATION
Pinned source: VladimirReshetnikov/ProveIt
Primary commit: b9aa36102e523213ae956b474ec651bfde3e5665
Later incoming archive checked at commit
7703601c48baf2fb4a051dc74559b0b766ea5a4b (see INCOMING_PROVENANCE.json)
Directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Artifacts

RESULT

The current compact coordinate envelope is 244 significant tokens, 267 AST
nodes, and 479 normalized UTF-8 bytes, attained by different programs. This
package improves the byte coordinate to 478. The token and AST minima are
TIED, not improved. No absolute minimum, no smaller mathematical axiom
inventory, and no single program dominating the old envelope are claimed.

A late check found that the incoming absorbing-predecessor archive already
contains the JSON Lines transformation to 244 tokens and 267 AST nodes. We
credit that stream protocol to the incoming archive. The two stream modules
included here differ from its sources only by importing json's exports with
an asterisk, saving four normalized bytes in each program without reducing
their token or AST counts.

The byte reduction changes a Boolean mode selector from short-circuit
disjunction to an eager two-item any call. It preserves canonical proof
traces and accepts a subset of the old raw certificates. The finite boundary
examples deliberately demonstrate the difference.

Program                         Tokens    AST    Normalized bytes
controls/tokens248.py               248    277                  609
code/checker244.py                  244    272                  604
controls/ast270.py                  254    270                  608
controls/incoming_tokens244.py      244    272                  608
controls/incoming_ast267.py         249    267                  606
code/checker267.py                  249    267                  602
controls/checker479.py              272    304                  479
code/checker478.py                  274    304                  478
controls/checker637.py              344    392                  637
code/checker636.py                  346    392                  636

The fully validating native companion improves 637 to 636 bytes. Its
alphabet and goal validation remain inside the measured complete module.
The compact controls/candidates have the same inherited guarded
Eq/D public-goal contract; they are not public-grammar validators.

Metric: CPython 3.12.14, ast.unparse(ast.parse(whole source)) plus one LF,
significant Python tokens with layout/comment tokens omitted, all AST nodes,
and UTF-8 bytes. Reader and success output are counted. The checkers import
only the Python standard json module. Support and compilation code is not
trusted or imported by a checker.

RUN

  python3 code/checker478.py < fixtures/byte/context/computation_zero_local.json
  python3 code/checker636.py < fixtures/native/proofs/computation_zero_local.json
  python3 to_jsonl.py < fixtures/three_field/global/computation_zero_global.json > example.jsonl
  python3 code/checker244.py < example.jsonl
  python3 verify.py

The AST-profile stream checker requires locally numbered three-field
certificates. Use the fixtures/three_field/local directory for it.
The token-profile stream checker uses global numbering and the global
directory. These protocols must not be mixed. checker478 and checker636
consume the unchanged four-field protocol in a JSON array, from right to
left. Successful acceptance is normal exit and exactly ACCEPT followed by LF;
exceptions reject. Unused array prefixes or stream suffixes are permitted.

VERIFICATION

verify.py verifies every retained Git blob against the pinned repository
tree, checks that each new module has exactly its declared source edit,
reproduces the ten metric vectors, and executes the programs in isolated
ordinary and optimized Python processes. Fixtures include genuine compound
case introduction, implication elimination, guarded induction using its
hypothesis, derived zero-source transport, and zero symmetry. Negative
fixtures cover scope capture, context leakage, scalar false sentinels,
malformed packets and false goals. Sixty additional closed computation
instances are generated together with wrong-endpoint corruptions.

The current evidence records 2,576 isolated executions with zero failed
expectations. These finite checks support implementation review; the
universal results are the written arguments in PROOFS.txt and the inherited
theory-to-iPRA bridge described in the main report. No new Lean/Rocq proof
of these Python programs is claimed.

IMPORTANT CONTRACT BOUNDARIES

1. A JSON Lines certificate is the old array in reverse order, with one
   independently valid JSON value per physical line. This copies the public
   goal literally to the first line. Parsed values and their consumption
   order agree. The new reader does not parse unread trailing text; the old
   whole-array parser validates the syntax of its unused prefix. An explicit
   malformed-suffix test records this boundary. Raw byte-language equivalence
   is not claimed.

2. checker478 eagerly evaluates 3 % len(a). It therefore rejects some old
   administrative aliases with an empty auxiliary goal. The supplied
   canonical_goal_raw_boundary.json has a canonical arithmetic public goal
   accepted by checker479 but rejected by checker478 through such an alias.
   The same theorem has an ordinary one-computation proof accepted by both.
   The claimed invariant is soundness plus canonical completeness, not exact
   raw acceptance equivalence.

3. The smallest compact checkers assume exact integer/list data and the
   canonical guarded public grammar. They should not be described as fully
   validating interfaces. checker636 checks the whole integer/list alphabet
   and the closed native Eq/D public grammar, including unused array data.

ATTRIBUTION

The scalar iterator calculus, primitive logical rules, arithmetic and logical
bridge, raw codec, scope discipline, and all old fixtures are inherited.
The stream protocol is also inherited from the later incoming archive.
New work here is the four-byte wildcard import refinement, the eager mode
selector, its canonical-completeness argument, two raw-acceptance boundary
examples, the generated computation cases, and the reproduction harness.
See PROVENANCE.json, INCOMING_PROVENANCE.json and LICENSE-ProveIt.txt.
