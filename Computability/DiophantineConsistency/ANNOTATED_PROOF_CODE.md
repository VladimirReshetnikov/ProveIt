# Numeric codes for the direct sealed-ZFC checker

`Lean/DiophantineConsistency/AnnotatedProofCode.lean` adds explicit executable
natural-number quotations and untrusted parsers to the frozen parent-index
checker. The public numerical result is

```lean
exists_checked_code_iff :
  (∃ code : Nat, check code = true) ↔ BProv ZFCax_s [] fBot
```

`exists_checked_fuel_code_iff` gives the same statement for independently
supplied parser fuel, and `no_checked_code_iff` identifies rejection of every
numeric code with the negation of the original sealed-ZFC refutation
predicate. `checkGoal` can check a numeric certificate against another specified
external formula. None of these statements asserts consistency.

The intermediate syntax has two constructors, `Tree.atom n` and `Tree.fork a b`.
Its literal numeric quotation is

```text
atom n    ↦ Nat.pair 0 n + 1
fork a b  ↦ Nat.pair (quote a + 1) (quote b) + 1
```

Here `Nat.pair` is Mathlib's square pairing, with its executable square-root
inverse, rather than `SetTheory.Cantor.toNat`. Zero is reserved for rejection.
The fuel decoder unpairs a positive code; a zero first component denotes an
atom, and a successor first component denotes a fork. Both child codes are
smaller than the enclosing code. The fixed parser supplies its input as fuel.
The proofs establish a depth bound, decoding/quotation roundtrips, the unique
quotation of every decoded tree, and rejection whenever quotation depth
exceeds fuel.

Typed parsers validate constructor tags, exact argument counts, list shapes,
formula syntax and natural fields. Quotations and roundtrips are provided for
`Form`, all seventeen `Rule` cases, `Line`, and `Certificate`; axiom tags and
contexts have their own transparent tree parsers. The final numerical checker
parses a certificate and invokes the already proved finite checker. An
untrusted code never supplies a proof of axiom membership or a correctness
certificate for its own parse. There is no choice operator, derived
`Encodable` instance, or `noncomputable` definition in this layer.

Formula tree tags and their argument arrangement follow the internal
`BoundedZFCConsistency.Coding.formCode` convention exactly: membership 0,
equality 1, bottom 2 with empty payload, implication 3, conjunction 4,
disjunction 5, universal quantification 6, existential quantification 7. Numeric
atoms are a separate arithmetic representation. No theorem in this module
identifies a natural numeral with the hereditarily finite set `formCode`, nor
does it identify external numeric checking with the internal
`ObjectCodeSeal` consistency formula. Such a transport needs an explicit
interpretation of atoms and forks as internal naturals and Kuratowski pairs,
and then a verification of parsing/checking inside the object theory.

The remaining arithmetic obligations are also explicit: construct and certify
primitive-recursive code (or direct arithmetic graphs) for the numeric tree
parser, typed parsing, renaming/substitution, syntactic bounds and sealing,
tagged axiom expansion, context/list comparisons, backward lookups and the
finite line loop. Prove that the resulting arithmetic checker computes this
module's `check`, then feed that supplied checked code or graph into a
Diophantine compiler. Merely having a terminating executable Lean definition
is not a proof of any of those representation claims. Repeated pairing can
produce large numeric quotations, so no compact-code or equation-size claim
is made here.

`Lean/checks/AnnotatedProofCode.lean` exercises zero and truncated decoding,
malformed formula/axiom/rule/list payloads, exact roundtrips, valid parent
sharing, a forged assumption, and the final equivalences. It audits the data,
parser and semantic endpoints separately. Runtime controls also execute the
square-root inverse on small valid, malformed and truncated inputs. Data and
parsing definitions use at most `propext`; the library pairing-inverse proofs
and the final roundtrip/existence theorems use the standard three axioms
`propext`, `Classical.choice`, and `Quot.sound`. This proof dependency does not
introduce a choice-based encoding or parser.
