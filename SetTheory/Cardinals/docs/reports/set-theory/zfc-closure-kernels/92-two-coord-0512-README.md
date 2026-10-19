# Frozen-assignment finite closure kernels

This directory contains a new **finite-theory presentation and exact reference
frontend**, with an ordinary mathematical consistency proof. It does not contain
a compiled binary Turing machine or establish a state bound below 245.

The final recommended compiler inputs are **FC13B** (one constant, 1024 native /
1499 completed flat bits) and **FC14Qd** (two constants, 926 native / 1401
completed flat bits). **FC15Qd** is the corresponding extensional control, with
1085 / 1560 bits. The `Qd` targets add the literal definition `q=I(d,d)` and are
definitional extensions of the Boolean-normalized targets. All retain six
proper functions. Their complete proof/cost supplement is
`encoding_experiments.tex`; this is a body-only TeX input for the parent report.

The original six-function S controls, whose full proof is retained unchanged,
are:

| Target | Native clauses / literals | Completed clauses / literals | Native bits | Completed bits |
|---|---:|---:|---:|---:|
| `FC13S` (raw EPSC) | 13 / 26 | 23 / 57 | 1040 | 1515 |
| `FC14S` (extensional control) | 14 / 30 | 24 / 61 | 1231 | 1706 |

Both have one constant, six proper functions, and two non-equality binary
predicates. Native equality is retained. They have at most four local universal
variables per native clause; equality completion raises that to six.

For comparison, source44's FC15* has 15 / 35 native and 29 / 82 completed clauses /
literals, nine functions, three non-equality predicates, and 881 / 1616 native /
completed bits. FC16* has 16 / 39 native and 30 / 86 completed clauses / literals,
with 1088 / 1823 bits. Thus the new completed streams save 101 and 117 bits,
respectively, while their native streams grow by 159 and 143 bits. The chosen
checker architecture determines which cost matters. These counts are not
converted into machine states.

## Mathematical changes

`F(b,t)` names the class whose value at assignment `s` is the original class `t`
evaluated at `b` with only the designated input/output coordinates replaced by
those of `s`. Its two defining clauses guarantee actual two-coordinate support,
even if `t` depends on every auxiliary selector. This allows the entire supported
EPSC implication to be asserted by one guarded class-incidence clause. Reusing
binders inside disjoint subformula scopes reduces the auxiliary selector budget
to one.

The existing `F` object also stores the quantifier's counterexample witness:

```text
q       = I(d,d)
P(s,j)  = C(C(d,d,s),q,j)
J(s,j,a)= V(F(P(s,j),a),q).
```

`P` is injective by the assignment laws and `d != q`. Consequently each `F` key
has at most one witness request. In a countable ZFC model, the incidence coding
can be chosen so that **every definable class has a representative in every
assignment-coordinate fiber** `V(-,q)=w`. The class semantics and the witness
coordinate are then simultaneously satisfiable. This is the proof for the
sharing; arbitrary identification of Skolem functions would not suffice.

The report specifies membership-language formulas for `V,C`, including a common
normalization of invalid graph codes to the empty graph. It uses arbitrary
set-coded partial functions; internal finiteness is unnecessary. All uses of
these formulas in a possibly nonstandard model refer to that model's
satisfaction relation. They do not assert that its internal graphs or natural
numbers are externally standard.

The class family allows logical equality. “Pure membership” excludes `Inc,F`
and the other added symbols, not logical equality. Extensionality in the upper
ZFC model can eliminate native equality from these defining formulas if needed.
Class definitions use the ambient proof's finite syntax and parameters from the
model. Uniform finite EPSC proof templates justify every such instance, with no
expanded-language truth or comprehension assumption.

The lower interface gives all raw equality-free EPSC matrices with arbitrary
finite parameters. The extensional fourteenth clause gives actual
Extensionality, and the source44 direct bootstrap yields ZF without Foundation
or Choice. Existing Foundation and constructibility proof transports calibrate
this to ZFC. The report explicitly identifies those dependencies. It does not
claim a new Lean/Rocq theorem, serialized proof-code compiler, or PA endpoint.

## Files

- `frozen_kernel_note.tex`: complete standalone mathematical note; intended for
  incorporation into the parent report.
- `frozen_kernel.py`: exact finite clauses, payload encoder and independent
  parser, structural metrics, wrapper and capture diagnostics.
- `FC13S_native.json`, `FC13S_complete.json`, and their `.bits` files: principal
  raw target, with all abbreviations expanded.
- `FC14S_native.json`, `FC14S_complete.json`, and their `.bits` files: principal
  extensional control.
- Other `F` and `R` payloads: measured intermediate variants. `F` retains the
  separate witness function; `R` removes it; `S` additionally reuses safe binder
  scopes. They are comparison controls, not additional recommended targets.
- `frozen_frontend.py`: exact ground-clause semidecision reference. Its default
  runs a single finite stage; `--whole-search` implements the unbounded ideal
  search and should not be expected to terminate.
- `frozen-kernel-results.json`, `frozen-frontend-results.json`, and
  `frozen-frontend-extensional-results.json`: finite reproduction results.
- `sources.json`: exact pinned source paths, section locators, Git blob IDs, and
  SHA-256 values of the inspected comparison files.

## Reproduction

Use Python 3 with assertions enabled. There are no external Python dependencies.

```sh
python3 frozen_kernel.py
python3 frozen_frontend.py --stage 1
python3 frozen_frontend.py --stage 1 --extensional --output frozen-frontend-extensional-results.json
```

The wrapper tests check both scope layouts against a separate direct EPSC
predicate for all 260 arbitrary `E,R` table pairs on carriers of sizes one and
two. They also check 4096 freezing-support diagnostics and an explicit capture
negative control. These finite carriers **are not models of the full
infinite-carrier assignment core**. Every emitted payload round-trips through
the parser. The reference frontend compares DPLL with exhaustive truth
assignment for 130 small CNFs and tests 4096 radix-eight term-code roundtrips.

The two actual bound-1 runs return SAT:

| Target | Ground clauses | Atoms | Maximum endpoint-code bit length |
|---|---:|---:|---:|
| FC13S | 300 | 259 | 63197 |
| FC14S | 308 | 267 | 63197 |

Finite stage `n` instantiates every local variable by every code `0,...,n`,
including equal substitutions. Endpoint terms beyond that frontier are retained.
Equality is an explicit predicate in these finite clauses; the fair unbounded
stream eventually includes every required equality/congruence instance.
The solver does not impose total interpretations of the functions on the
bounded frontier. A finite SAT valuation is a propositional ground-clause
certificate, not a finite model of the entire theory.

The 63197-bit endpoint arises from nested Cantor coding at depth 15, despite
using only codes 0 and 1 for the substituted variables. It is a concrete runtime
cost of the new wrapper, not a payload size or state count. The smaller
six-function signature permits radix eight with two padding tags, but does not
remove this depth cost.

The exact DPLL search returns UNSAT only after exhausting its branches. Host
exceptions propagate and are never converted into a refutation. Fair grounding,
compactness, and the retained-function equality quotient prove the ideal
unbounded semidecision contract in ordinary ZFC. All binary compilation and
blank-initialization costs remain unmeasured.

## Source boundary

All repository references are pinned to ProveIt
`6446ff5668307a2ac6aee1896037f0b792090389`. Source44's documents have section
locators rather than numbered theorem declarations; the exact section names
are recorded in `sources.json`. Its original six closure clauses, finite
assignment/class architecture, and EPSC/PSC calibration are attributed to that
work and its prior sources. The general assignment/class machinery is due to
Harvey Friedman, *Impossible Counting*, September 2, 2017, Section 4.1; Theorem
4.2.3 is the earlier finite-system consistency comparison.

Friedman's axiom K[1,5] already supplies unary projection that freezes
parameters, and his Theorem 4.1.3 supplies the countable definable-class
expansion. The present binary assignment-pullback operator is a variant of
that precedent; projection and class coding themselves are not claimed new.

The new result here is the specified frozen-assignment presentation, the
rich-coordinate coding proof for its witness sharing, and the exact new payload
and reference implementation. No global historical priority claim is made.

## Final encoding supplement

The S presentation has been preserved. `boolean_class_control.py` changes just
the hull class from `Ex(r,And(c,s))` to `I(U(r,I(c,I(s,d))),d)`, cancelling one
class-level double negation. This is equivalent in every common-core model;
it does not assert equality of the class objects. FC13B/14B save exactly four
tree nodes and 16 flat bits and lower the maximum depth from 15 to 13.

`named_selector.py` separately emits two-constant variants. `Qd` adds
`q=I(d,d)`; `Q` instead adds `Inc(s,q)`, with the additional native-model
transport proved in the supplement. Q saves eight further bits relative to Qd.
The new constant is charged as a real opcode, reference base, and ground symbol.
No extra positive-arity congruence axiom is needed for it.

| Target | Native C/L | Complete C/L | Native flat | Complete flat | Best complete sparse grammar |
|---|---:|---:|---:|---:|---:|
| FC13B | 13/26 | 23/57 | 1024 | 1499 | 1367 |
| FC14Q | 14/27 | 24/58 | 918 | 1393 | 1322 |
| FC14Qd | 14/27 | 24/58 | 926 | 1401 | 1330 |
| FC14B | 14/30 | 24/61 | 1215 | 1690 | 1553 |
| FC15Q | 15/31 | 25/62 | 1077 | 1552 | 1475 |
| FC15Qd | 15/31 | 25/62 | 1085 | 1560 | 1483 |

`shared_template_codec.py` measures full constructor DAG and sparse repeated
subtree grammar encodings under three explicit local-variable naming policies.
Headers, records, escapes, references, literals, and the final terminator are
all included; the known signature is excluded just as in the original flat
format. Every emitted stream reconstructs the exact selected alpha-renamed
trees, and audit maps recover the original variable names. This is a finite
syntax experiment and does not introduce new semantic function symbols.
Full DAGs lose against flat syntax in every measured main target. Sparse
grammars help, but their decoder cost remains unmeasured.

The comparison is self-contained: `source44-encoding-snapshot.json` contains
the exact old clause trees, source commit, generator paths, and hashes. Naming
the old selector too gives an important fairness control. With only the four
variable slots actually needed by native old clauses, old FC15*/16* improve to
855/1022 flat bits and 811/975 sparse bits. Thus the new targets do not win the
best old native-payload comparison. Their reliable advantage is in completed
payloads; old original completed streams cost 1616/1823 flat or 1543/1729 sparse
bits. No bit count is converted into states.

`linear_ground_codec.py` gives a fair alternative reference refuter using
arity-delimited prefix words. An n-node retained ground term has exactly 3n
bits; a natural-number name with one leading 1 has 3n+1 bits. For the identical
substitution frontier `{d,V(d,d)}`, S's maximum endpoint is 345 prefix bits,
B's 333, and Q/Qd's 285, versus 63197/15798/11796 bits in their respective
nested-Cantor comparators. Each row's prefix and numeric versions produce the
same ground CNF after atom renaming, with checked SAT valuations. The Q/Qd
enumerator's own first two terms are `{d,q}`; its 213-bit result on that different
frontier is separately labeled and is not used as a common-frontier comparison.

The optional unbounded searches enlarge a monotone term frontier, ground every
substitution tuple including collisions, and halt only on an exhausted exact
UNSAT result. Invalid prefix words are skipped. Host resource errors propagate;
there is no arbitrary word-length cutoff or failure-to-refutation conversion.
Compactness and equality completion give the same ordinary-ZFC consistency
endpoint as the finite theories. There is no new machine-level certificate.

`channel_collapse_control.py` records a rejected three-function direction that
stores I/A/U constructor outputs in F-value coordinates. Its native raw flat
payload grows to 4038 bits at depth 56; the extensional version has 5077 bits.
The richer upper-model construction is only sketched, and this control is not
among the fully proved recommended endpoints.

Additional finite reproduction commands are:

```sh
python3 boolean_class_control.py
python3 linear_ground_codec.py
python3 linear_ground_codec.py --boolean-normalized --output linear-ground-boolean-results.json
python3 shared_template_codec.py
python3 named_selector.py
python3 channel_collapse_control.py
```

The optional ideal refuters are `linear_ground_codec.py --whole-search`,
`linear_ground_codec.py --boolean-normalized --whole-search`, and
`named_selector.py --whole-search`. For the last command, `--truth-only` chooses
Q instead of Qd. Add `--extensional` for the extensional control. These are not
quick reproduction commands and should not be expected to terminate.
