# Root-deterministic certificate protocol

## Acceptance and trusted program

Each checker is a standalone Python 3 module importing only the standard JSON parser. Feed one JSON array on standard input. Acceptance means normal exit with exit status zero and exactly `ACCEPT\n` on standard output. Exceptions reject. The final array item is the closed goal; earlier items are instruction records consumed backwards with `pop`. An unused prefix is inert. The producer, case builder, proof audit, and measurement tools are untrusted test support and are not imported by a checker.

The byte/AST profiles use lexical eigenparameter scopes and start with the retained derived truth `[]`, read as `0=0`. The token profile uses the inherited monotone global floor and starts with an empty context. These two certificate-numbering conventions need separately generated packets; they present the same canonical theory.

## Canonical object formulas and administrative syntax

Canonical object formulas are literal equations and paired D formulas. At an atomic D matrix the syntactic guard is required:

`D_{x,y}(I(y,0;u.h) = I(y,0;u.k))`.

The updates may contain the bound state and passive parameters. The ordinary interpretation is the inherited `exists x (B(x,0) -> forall y B(x,y))`; the guard makes `B(x,0)` provable by computation. The proof builder uses the narrower selector form `C(y,0,s) = C(y,0,t)`.

Q closures are administrative retained resources, read as `B(0) -> forall y B(y)`. A raw unguarded atomic D used inside a certificate has the ordinary soundness reading `exists x forall y (B(x,y) -> B(x,Sy))`. Its elimination exports Q using equation induction in iPRA. Completeness and the two identity composites are asserted for the guarded canonical object language, not for every raw administrative spelling. In particular, the unrestricted raw D constructor does not have one uniform old Q-based meaning.

The compact profiles do not run a syntactic canonical-goal validator. If one is added to an interface, its source must be counted separately or together with that interface. It must not be silently omitted from a claim about a program which enforces canonical input.

## Arrays and opening

The inherited arity codec is unchanged:

- Numerical zero is `0` or `[]`; successor is `[t]`; scalar iteration is `[n,a,h]`.
- Formula equality is `[s,t]`; D is `[B]`; canonical administrative Q is `[B,B,B]`.
- Empty formula arrays and arrays of arity at least four are truth aliases. In numerical positions, binary and high-arity arrays are zero annotations. They are raw administrative aliases, not extra arithmetic operators.

At numerical root depth 3, coordinates 0,1,2 are zero aliases (the canonical zero code is 0), while coordinates `3+2j` and `4+2j` refer to protected slot j. Negative integer labels are rigid eigenparameters, admitted down to the current floor. Formula root depth is 0. A node of arity r changes depth by `5-r`. Consequently D adds two protected numerical slots; Q and iteration add one; equation switches from formula to numerical depth. Successor introduces two dummy zero slots and the iterator introduces a dummy zero slot in its counter and initializer. In its update the iterator's new slot is the bound state.

Opening preserves a scalar in the currently admitted interval; another relevant scalar denotes the substitution hole. Images are validated at numerical root depth 3 before insertion. A missing image at a used hole fails. Witness opening precedes allocation of the new eigenparameter; reversing this order is unsound.

An atomic guarded D has raw form `[[[5,0,h],[5,0,k]]]`: immediately beneath D, each side's iterator counter reads the innermost y coordinate through the iterator's dummy counter slot. The pattern applies recursively at every D with an equation matrix.

## Four-field instructions

Each record has fields `[major, source, initializer, template]`.

- With a nonempty `major`, the checker verifies that major in the current context. If it is the equation `[source,initializer]`, `template` specifies equality transport. If it is `[template,template,template]` and `source` is zero, the same matching/continuation implements Q use. Otherwise the record can be a neutral major. A unary D major exports its Q closure at a fresh witness; other nonempty arities export a truth alias.
- With the neutral empty-array major and a truthy `initializer`, the checker constructs a computation equation. Falsy `source` selects I0; truthy `source` constructs the successor of that predecessor for IS. The endpoint is constructed by opening the update at the recursive iterator. Nonempty certified zero terms repair the inherited restriction on literal-zero initializers and predecessors.
- With neutral major and falsy initializer, the checker opens the D goal using `template` as its witness. After opening, an equation root automatically receives the progress assumption `E(z)`. A compound root automatically receives the base assumption `B(0)`. The successor instance is always the continuation goal. `source` is unused in this introduction packet.

The previous distinction between initializer `0` and initializer `[]` as an introduction-mode choice has been removed. Both now select the unique root-determined introduction. One inherited negative fixture deliberately toggles this retired field while keeping a valid equation-progress derivation; the deterministic checker correctly accepts that fixture, whereas the old choice checker rejects its claimed case mode.

## Measured profiles

Measurements use CPython 3.12.14. Normalize the source by parsing it, removing actual module/function/class docstrings, and applying `ast.unparse(tree) + '\n'`; then count its UTF-8 bytes, significant tokenizer tokens, and all `ast.walk` nodes. Gzip uses `gzip.compress(..., compresslevel=9, mtime=0)` on the normalized UTF-8 source and is informational.

| Profile | Bytes | Tokens | AST nodes | Gzip-9 |
|---|---:|---:|---:|---:|
| Simple lexical, `code/checker.py` | 528 | 265 | 308 | 332 |
| Byte, `code/checker_bytes.py` | 527 | 266 | 307 | 335 |
| AST, `code/checker_ast.py` | 607 | 263 | 286 | 349 |
| Token, `code/checker_tokens.py` | 575 | 260 | 290 | 345 |

The coordinate envelope is `(527 bytes,260 tokens,286 AST nodes)`, achieved by different programs. No one listed profile achieves all three minima. The corresponding inspected baseline minima are 529 bytes,261 tokens,289 AST nodes, again achieved by different programs. These are observations about a frozen corpus, not lower bounds on all proof checkers.

## Executed evidence

`evidence/extended_validation.json` is the earlier exploratory receipt: it records 720 CLI checks across nine implementations, including the readable expansion and two old baselines, in ordinary Python and `python -O`. It retains the original workspace paths, which are not the delivered package paths. There are zero mismatches against the explicitly stated protocol expectations. The fixtures include computations, transport, guarded introduction, guarded elimination, compound implication introduction and elimination, a 176-instruction nontrivial guarded induction certificate, scoped-parameter attacks, and malformed inputs. The authoritative reproduction receipt for the delivered layout is `evidence/validation.json`, with 800 checks across ten programs.

The old atomic case theorem `D_{x,y}(y=1)` is accepted by the old checker and its supplied old case certificate is rejected by every deterministic profile. Its old ordinary reading is true because the base `0=1` is false; its new raw progressive reading is false at y=1. This is evidence against silently assigning the old interpretation to all raw atomic D forms.

`evidence/guard_audit.json` checks that every atomic D occurrence in all eight canonical named positive derivations is guarded, including 13 occurrences in the nontrivial induction derivation. The separate administrative-Q fixture and the old-case counterexample are explicitly marked outside the canonical goal language.

These are finite executable checks. They supplement the written soundness, completeness, and interpretation arguments; they are not a proof-assistant formalization.

The delivery also records 800 checks across ten programs in `evidence/validation.json`, reproduced by `python3 scripts/reproduce.py`. That run includes the standalone strict-goal checker and the corresponding old-core parser control. The table above uses normalized source with actual docstrings removed.
