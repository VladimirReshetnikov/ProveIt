# Independent codec and Boolean-control audit

Reviewed `linear_ground_codec.py`, `shared_template_codec.py`,
`boolean_class_control.py`, `named_selector.py`, `channel_collapse_control.py`,
their supporting source, the final `encoding_experiments.tex`, and emitted
artifacts.
`codec_audit.py` independently recomputes the reported costs from the literal
JSON trees and payload lengths; it imports neither codec nor its metric
functions. Its optional source44 check verifies the pinned source hashes and
regenerates the four original clause lists directly from those primary files.

## Prefix ground-term names and fair refutation search

The seven retained symbols, including the constant, have fixed three-bit
tags and known arities. Preorder traversal therefore gives exactly three
bits per tree node. The arity-slot invariant proves unique parsing. The
decoder rejects unused tag 7, unfinished trees, and extra tokens after a
completed root. A leading one makes the bit word an injective positive
integer name without losing its initial zero bits.

Enumerating all finite tag words by length and then lexicographically, and
discarding ill-formed words, is fair: there are only finitely many words
before any specified finite term. The frontier includes every retained
ground term eventually. Every finite substitution tuple therefore appears
at a finite stage. Endpoint terms are retained even when they lie outside
the substitution frontier. Each propositional decision problem is finite,
and the exact DPLL search either finds a checked satisfying valuation or
exhausts all branches. Compactness and the existing equality-congruence
quotient supply the ideal inconsistency-semidecision argument.

This statement concerns the mathematical unbounded algorithm. In the host
implementation, recursion, integer, and memory limits can produce exceptions.
The code does not catch those exceptions as refutations. Thus a successful
UNSAT return has its intended meaning; arbitrary process termination is not
a certificate of inconsistency. The script is not itself a binary machine
with the requested halting equivalence.

The code comparison uses the same two-term frontier, `d` and `V(d,d)`, and
the same completed clauses. Prefix names and Cantor names identify exactly
the same syntactic endpoints, so deterministic first-occurrence atom
numbering produces the same numbered CNF for that fixed theory and stage.
This claim does not identify the B and S finite CNFs with each other or
claim that later prefix frontiers equal later numerical Cantor frontiers.

Independent grounding of the emitted JSON gives:

| Target | Ground clauses | Atoms | Endpoint occurrences | Largest endpoint nodes | Depth | Prefix bits | Cantor bits |
|---|---:|---:|---:|---:|---:|---:|---:|
| FC13S | 300 | 259 | 1,768 | 115 | 15 | 345 | 63,197 |
| FC14S | 308 | 267 | 1,832 | 115 | 15 | 345 | 63,197 |
| FC13B | 300 | 259 | 1,768 | 111 | 13 | 333 | 15,798 |
| FC14B | 308 | 267 | 1,832 | 111 | 13 | 333 | 15,798 |

The positive integer representation needs one additional leading bit. These
are endpoint-name lengths at a fixed ground stage, not template lengths,
running times, or machine state counts.

## Fully charged shared-template payloads

The full DAG codec charges an Elias-gamma header for the number of constructor
records, the signature-dependent width for each function opcode, every child reference at its
current dictionary width, every root reference at the final width, all
clause/literal controls, and the terminating clause code. Proper subtrees
have smaller depth, so the stated ordering gives only backward references.

The sparse grammar codec also charges its macro-count header and every
macro definition. The all-ones opcode is escaped uniformly. In the original
four-bit case, opcode 15's old constructor form costs five bits, while its
macro-reference form costs five control bits plus the current index width.
The first macro cannot reference itself, and a
dictionary with one entry legitimately uses a zero-bit index. The body
includes all clause and literal controls and its terminator. Source44's
ninth proper constructor receives the extra escape bit wherever used. It
is not silently priced at the old four-bit rate.

The six universal variable slots are local to each clause. Renaming them
bijectively before encoding selects an alpha-equivalent universal theory.
The encoded decoder may retain those selected names; it need not recover
the original human-readable variable names. Therefore the inverse audit
maps do not need to be placed in the bit payload or executed at runtime.
The independent audit checks that each map is a bijection onto exactly the
used slots and reconstructs every original clause. Shared entries denote
syntactic expressions with those local slots, not new semantic function
symbols or comprehension principles.

The signatures and their arities are known to these codecs, as they are in
the original flat comparison. A real compiler must still implement that
knowledge, dictionary decoding, variable substitution, proof search, and
blank initialization. No interpreter or decompressor state charge is
included. The exhaustive local alpha-renaming pass and sparse-macro local
descent are compile-time searches and make no global optimality claim.

All 78 emitted theory/renaming combinations, including the named-selector
controls below, matched independent cost recomputation, including header,
dictionary, body, and actual payload length.
For the same `greedy_dag` variable policy on each theory:

| Target | Flat bits | Full DAG bits | Sparse grammar bits |
|---|---:|---:|---:|
| FC15* native | 881 | 900 | 828 |
| FC13B native | 1,024 | 1,212 | 911 |
| FC15* completed | 1,616 | 1,870 | 1,543 |
| FC13B completed | 1,499 | 1,792 | 1,367 |
| FC16* native | 1,088 | 1,190 | 1,020 |
| FC14B native | 1,215 | 1,483 | 1,078 |
| FC16* completed | 1,823 | 2,090 | 1,729 |
| FC14B completed | 1,690 | 2,137 | 1,553 |

For example, FC13B completed's 1,367 sparse bits comprise a 5-bit header,
90-bit macro dictionary, and 1,272-bit clause body. Native FC13B remains
larger than native FC15* under this same format. The full DAG is larger than
the flat payload in every displayed row; unrestricted subtree sharing is
not automatically profitable.

## Boolean-normalized B control

The B variants change exactly one subexpression in the closure clause. Write
$\bot=d$ and $N(X)=I(X,d)$. The common implication/falsity clauses give

$$
\operatorname{Inc}(s,N(N(X)))\ \longleftrightarrow\
\operatorname{Inc}(s,X)
$$

for every assignment $s$ and every class object $X$. The exact universal
clauses then give the corresponding equivalence under $U(r,-)$ with its
selector unchanged. Exact implication propagates it through the outer
class expression. Consequently

$$
I\bigl(U(r,I(I(X,d),d)),d\bigr)
\quad\text{and}\quad
I\bigl(U(r,X),d\bigr)
$$

have the same incidence at every assignment. Here
$X=I(C,I(S,d))$, where $C$ and $S$ are the already constructed closedness
and support classes. This is precisely the expansion of the existential
conjunction used in the old hull.

Only I/U class-operand positions are changed. No equality of class objects
is inferred, and no selector, coordinate, assignment, or membership-label
position is rewritten. Therefore the original S and changed B closure
clauses are equivalent in every structure satisfying their common core.
The two theories have the same models in their common signature. Their
completed versions add the same equality clauses and retain this fact.

The literal JSON comparison confirms that all other clauses and literals
are unchanged. Two I nodes and two d nodes disappear, saving exactly 16 flat
bits. Independent resulting counts are:

| Target | Clauses | Literals | Term nodes | Maximum depth | Bits |
|---|---:|---:|---:|---:|---:|
| FC13B native | 13 | 26 | 226 | 13 | 1,024 |
| FC13B completed | 23 | 57 | 314 | 13 | 1,499 |
| FC14B native | 14 | 30 | 270 | 13 | 1,215 |
| FC14B completed | 24 | 61 | 358 | 13 | 1,690 |

## Named-selector Q/Qd controls

Both controls replace every fixed selector term $I(d,d)$ in B by an explicit
second constant $q$. Qd adds the genuine definition $q=I(d,d)$ after that
replacement. Q instead adds the universal truth clause $\operatorname{Inc}(s,q)$.
The definition costs 22 flat bits and the truth clause costs 14; neither is
treated as free decoder metadata. There are 15 replaced selector occurrences
in the raw B presentation and 19 in the extensional one. Each replacement
saves two four-bit term nodes.

Qd is a direct definitional extension. The truth-only Q model transport is
also sound, with a different scope: in a native genuine-equality Q model,
change the implication operation only at the ordered pair $(d,d)$, assigning
that value to $q$. The new value has true incidence everywhere, so exact
implication is preserved. All explicit selector, coordinate, assignment,
freeze, and witness terms retain their intended values. The affected nested
class expressions retain their incidence by induction through I/U class
positions using exact universal semantics. Since the changed operation now
has $I'(d,d)=q$, forgetting the named constant gives a B model. The converse
expansion simply names the original $I(d,d)$.

This is a model transport, not an assertion that truth codes are equal as
objects or that forgetting $q$ from an arbitrary Q model without changing I
already gives a B model. In the explicit-equality completed presentations,
one first takes the established equality congruence quotient and performs
the native construction there; no naive piecewise function update on a
nontrivial prequotient equality relation is claimed.

Independent exact substitution checks and counts give:

| Target | Native clauses / literals | Native nodes | Native bits | Completed clauses / literals | Completed nodes | Completed bits |
|---|---:|---:|---:|---:|---:|---:|
| FC14Q | 14 / 27 | 198 | 918 | 24 / 58 | 286 | 1,393 |
| FC14Qd | 14 / 27 | 200 | 926 | 24 / 58 | 288 | 1,401 |
| FC15Q | 15 / 31 | 234 | 1,077 | 25 / 62 | 322 | 1,552 |
| FC15Qd | 15 / 31 | 236 | 1,085 | 25 / 62 | 324 | 1,560 |

All have maximum template depth 12 and six proper functions. The two-constant
codecs correctly use eight fixed DAG bases with six variable slots, and eight
ground-prefix tags, including both nullary symbols. Their padded numerical
comparator assigns $d=0$, $q=1$, and proper constructors values
$2+i+8\pi(\ldots)$. The independently checked ground comparisons distinguish
the common frontier $d,V(d,d)$ from the new alphabet's own first two terms
$d,q$. The former has a maximum 95-node endpoint, 285 prefix bits; the latter
has a maximum 71-node endpoint, 213 prefix bits. These are different finite
substitution experiments, not interchangeable evidence.

The source44 named-selector controls also charge their new constant. Nine
proper functions, two constants, and six variable slots require 17 distinct
tags, hence five-bit flat opcodes in that fixed-slot variant. Separate native
controls use four variable slots, which suffice for their native clauses and
restore four-bit opcodes. Those tighter native controls must be compared
under their stated interface; the completed ternary-function congruence
clauses still need six variables. None of these signature or payload
differences alone establishes a binary state saving.

## Three-function channel control

The rejected channel control expands I/A/U into tagged V/C/F terms. The
independent audit reconstructs that conversion from the emitted truth-Q
clauses and verifies every resulting clause. It also independently removes
exactly the three now-unused congruence clauses. Flat counts and actual
sparse payload lengths are:

| Control | Clauses / literals | Term nodes | Depth | Flat bits | Lexical sparse bits |
|---|---:|---:|---:|---:|---:|
| Raw native | 14 / 27 | 978 | 56 | 4,038 | 2,625 |
| Raw completed | 21 / 49 | 1,036 | 56 | 4,357 | 2,944 |
| Extensional native | 15 / 31 | 1,234 | 56 | 5,077 | 3,306 |
| Extensional completed | 22 / 53 | 1,292 | 56 | 5,396 | 3,625 |

No immediate collision blocks the proposed upper-model sketch. Exact
assignment semantics and $d\ne q$ make $P$ injective and the three channel
tags distinct. Thus a fixed first key $P(\tau_G,P(a,b))$ identifies at most
one requested constructor, argument pair, and desired value. Constructor
requests occur only at the F key with second argument $d$ and constrain
the output's $d$ coordinate. A possible overlapping universal-witness
request at that same F key constrains its $q$ coordinate instead. Pair
injectivity also ensures at most one such witness request. The F output's
required incidence class remains a third, independently prescribed
condition.

The needed strengthening of the rich-code construction is explicit:
every desired definable incidence class must have representatives in every
prescribed pair of $d,q$ coordinate fibers. Choose a third selector $h$
distinct from $d,q$. By writing an arbitrary value at $h$ while keeping
the two designated coordinates fixed, one obtains infinitely many distinct
underlying assignment codes in every fiber. Distributing the countable
definable-class family over each such fiber, excluding reserved constants,
supports the stated simultaneous conditions. These requests depend on the
previously fixed incidence classes and assignment operations; they need
not depend circularly on the later choice of F outputs.

This review finds no immediate key-collision flaw, but does not promote
that paragraph into an additional completely audited consistency endpoint.
The final supplement appropriately labels its upper-model argument a
sketch and the artifact a measured negative encoding control. Its displayed
costs already exceed the tested six-function alternatives; no binary-state
conclusion follows from lowering the number of function symbols alone.

## Reproduction and source44 portability

```bash
python3 -B codec_audit.py \
  --formalisms /path/to/formalisms \
  --output codec-review.json
```

The codecs themselves read the bundled `source44-encoding-snapshot.json`
and do not need a live ProveIt checkout. That snapshot contains exact
literal clauses, signatures, flat reference costs, pinned commit identity,
and source-file hashes. In the present audit, both primary hashes and all
four clause lists were independently checked against the pinned checkout.
To repeat that optional provenance check, add:

```bash
--source44-root /path/to/ProveIt/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels
```

This audit is an ordinary mathematical and artifact review. It neither
proves an exact binary-state bound nor adds a new kernel-checked theorem.
