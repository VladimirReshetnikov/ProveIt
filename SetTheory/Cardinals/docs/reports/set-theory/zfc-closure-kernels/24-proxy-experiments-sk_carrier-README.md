# An explicit combinatory carrier for the literal 253-state machine

This directory supplies a closed SK term `P253`, a transparent compiler from
ordinary two-symbol Turing machines, a one-constant encoding, and finite
validation results. The output is a concrete finite equational theory. It is
a reference artifact for the consistency-carrier proposal; no new small-state
Turing-machine bound is asserted.

## Reproduction

Python 3, standard library only:

```sh
python3 build_carrier.py literal_zfc253.tm --output .
python3 test_carrier.py
```

The literal input table is frozen as `literal_zfc253.tm`, with SHA-256
`84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`.
It defines 253 working states and 506 transitions, starts in state 0, and
halts by reaching an undefined transition. Its relation to ZFC consistency
belongs to the upstream machine audit. The construction here supplies the
separate, generic equivalence between a machine's nonhalting and consistency
of its associated equational theory.

## The exact finite theory

Application is binary and associates to the left. The first presentation has
constants `K`, `S`, and exactly these three first-order axioms:

1. `forall x y. K x y = x`.
2. `forall x y z. S x y z = (x z) (y z)`.
3. `P253 != K`.

The symbol `P253` in axiom 3 is a metanotation for the **entire closed term**
serialized in `P253.bcl`; it is not a third constant, an oracle, or a hidden
axiom. Its prefix codec is `K = 00`, `S = 01`, and application `= 1` followed
by its two subterms. The file is ASCII bits with no terminating newline.
`P253.bcl.bin` contains the same bits packed most significant bit first.

A second presentation uses one constant `o` and the same binary operation.
Write `k = (o o)` and `s = (o (o o))` only as textual abbreviations. Its axioms
are:

1. `forall x y. ((k x) y) = x`.
2. `forall x y z. (((s x) y) z) = ((x z) (y z))`.
3. `P253_one != k`.

`P253_one` is the exact closed term in `P253.one.btree`; the tree codec is
`o = 0`, application `= 1` followed by its two children. Its `.bin` companion
uses big-endian packed bits with zero padding in the last byte. The exact bit
length, not padded byte length, is recorded in `metrics.json`.

## Measured size

The SK payload has 41,063 K leaves, 23,028 S leaves, 64,090 application nodes,
and 192,272 BCL bits (24,034 packed bytes). The one-constant payload has
302,419 bits (37,803 packed bytes). The encoded transition table accounts for
188,951 BCL bits, approximately 98.3% of the complete SK payload.

All build-time graph sharing is unfolded during serialization. No DAG pointers
or definitions remain in either payload. These measurements include the full
table, interpreter, state number, empty left and right tape halves, and blank
scanned symbol. They do not include a binary Turing-machine implementation of
SK reduction or a blank-tape writer for the payload. Such a machine still has
to be constructed and charged before any state-count comparison is valid.

The single-constant encoding illustrates the tradeoff directly. If an SK
term has `a` K leaves and `b` S leaves, its BCL length is `3(a+b)-1`; this
one-constant translation has length `4a+6b-1`. A simpler symbol vocabulary
therefore increases this payload. The shorter codeword is assigned to K
because K is the more frequent leaf in this build.

## Transparent source algorithm

The compiler uses ordinary lambda abstraction only as a finite source
notation. It removes every abstraction by these three rules, with `I = SKK`:

```text
[x] x       = I
[x] A       = K A                    if x is not free in A
[x] (A B)   = S ([x] A) ([x] B)
```

There is no eta rule. In particular, the compilation of `lambda x y. x` need
not be syntactically K or reduce to K. For this reason the machine's halt
handler is the primitive symbol K itself. This distinction has an executable
regression check.

Boolean zero is K; boolean one is `K I`. Empty lists are `K I`, and
`Cons h t = lambda c n. c h t`. Tuples use the Church observer convention
`Tuple a ... z = lambda observer. observer a ... z`. State numbers are fixed
width big-endian lists of selector booleans. The table is a complete binary
tree of pairs, and each leaf is a pair of transition records, selected by the
scanned bit. An undefined transition has record `Halt = K`; a defined
transition has record `Act w d q = lambda h c. c w d q`. Direction R is the
first selector, L the second. Empty tape halves supply a zero on popping.

In the following source, every displayed name is expanded in the payload:

```text
Y = lambda f. (lambda x. f (x x)) (lambda x. f (x x))

Lookup = Y (lambda look path tree.
  path (lambda b rest. look rest (tree b)) tree)

F = lambda table rec q left bit right.
  (Lookup q table) bit
    K
    (lambda w direction next.
      direction
        (right
          (lambda b rest. rec next (Cons w left) b rest)
          (rec next (Cons w left) K Nil))
        (left
          (lambda b rest. rec next rest b (Cons w right))
          (rec next Nil K (Cons w right))))

Run table = Y (F table)
P_M = Run Table_M State_start Nil K Nil
```

The emitted term `P253` is exactly the basic-abstraction compilation of this
construction for the frozen input table. `build_carrier.py` specifies all
finite encodings and checks that no free variable remains.

## Mathematical calibration

For every finite table M accepted by the parser, the construction gives:

```text
M halts from the blank tape
    iff P_M reduces to the literal K
    iff the three-axiom SK theory is inconsistent.
```

These equivalences concern ordinary finite computation and syntax and are
formalizable in ZFC. They require no assumption that M actually halts or
that ZFC is consistent. Consequently, **if the chosen literal table has its
required internally provable calibration**, then its three-axiom carrier is
provably equiconsistent with ZFC. The separate compiler construction does not
repair or silently assume an absent calibration for the input table.

The mathematical argument is given in `proof_sketch.tex`. Its parts are:

* The standard bracket-abstraction application lemma and finite transition
  simulation, including both blank-boundary cases.
* Confluence of the two orthogonal SK rules, so convertibility to the normal
  form K is equivalent to reduction to K.
* A ground-term quotient model, showing that adding `P != K` is consistent
  exactly when P and K are not convertible. This avoids adding an
  extensionality axiom or invoking the claim that all equational theories
  can be inconsistent: equations alone have a one-element model.
* Orthogonality of the one-constant rules and exact reduction transport for
  the encoded SK image. Global confluence prevents reverse equation use on
  unencoded terms from creating additional identifications inside the image.

The report's proof is a human mathematical proof. No proof-assistant-checked
compiler-correctness certificate is supplied in this directory.

## Finite validation

`validation.json` records the actual run of `test_carrier.py`:

* 101 complete terminating runs for toy machines, including an immediately
  halted machine; all produced the literal K with no pending argument.
* 72 local cases covering both directions and writes, both scanned bits,
  and empty and nonempty left/right tape halves.
* 200 single-step comparisons on random cyclic transition tables and arbitrary
  finite configurations.
* The first 300 exact configurations of the literal 253-state machine,
  compared against a direct native simulator.
* Every one-step reduction of every SK term with at most five leaves: 550
  terms and 360 distinct reduction edges, compared with a separate literal
  one-constant tree rewriter.
* Complete serialization/parse roundtrips of both actual payloads.

These finite checks detect implementation mistakes. They do not establish
an infinite run or the consistency of ZFC.

## Source references

* John Tromp, *Functional Bits: Lambda Calculus based Algorithmic Information
  Theory*, September 24, 2026, sections 3.0--3.2:
  <https://tromp.github.io/cl/LC.pdf>. The explicit codec in Definition 3 and
  its worked example use K=00 and S=01, the convention followed here. The
  prose immediately before that definition interchanges the names.
* John Tromp, accompanying implementation page:
  <https://tromp.github.io/cl/cl.html>. It discusses the relative description
  sizes of binary lambda calculus and binary combinatory logic.
* H. B. Curry and R. Feys, *Combinatory Logic*, volume I, 1958; and
  J. R. Hindley and J. P. Seldin, *Lambda-Calculus and Combinators: An
  Introduction*, 2008, for the standard confluence and normalization results.
  The two-rule confluence argument needed here is also included in the proof
  sketch by the elementary orthogonality/parallel-reduction argument.

No historical novelty is claimed for the general computational-carrier
construction. The contribution of this artifact is the exact closed payload,
its reproducible compiler and accounting, and the explicit one-constant
presentation and reduction transport.
