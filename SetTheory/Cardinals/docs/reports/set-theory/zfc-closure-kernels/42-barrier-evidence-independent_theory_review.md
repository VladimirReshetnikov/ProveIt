# Independent review of the represented-EPSC finite kernel

Reviewed against the generated `fak5_clauses.json` and `fak5_shared_clauses.json`
in `/tmp/zfc_theory_innovation_new`, as well as the pinned ProveIt source-34
FAK12 specification. This is an ordinary mathematical review, not a new Lean
or Rocq proof. The finite tests below inspect only the six EPSC clauses.

## Verdict and prior overlap

The five-axiom kernel and its shared fifteen-clause presentation are sound
proposals at the requested ZFC-provable consistency level. I found no overlap
with the thirty-four reconciled reports or the five newer unplaced archives
at ProveIt commit `61e77836565f63582561f54745f633d50efd9c7d`.

The constituent ideas are established: Friedman's assignment/class coding,
the prior equality-free EPSC calibration, standard Skolem witnesses, and
conditional reuse of witnesses. The concrete new result is their combination
into this explicit calibrated finite payload. It is not a new binary machine
state count or a claim of global historical priority.

## 1. The selector argument is valid without set-existence axioms

Write `q = N(o,o)`. The NAND axiom implies `N(a,a) != a` for every object a:
if equality held, evaluating the class equivalence at any assignment object
would identify a proposition with its own negation. Nonempty-domain ordinary
first-order semantics is essential, and is already the stated convention.

Thus `q != o`. Put

```
c = C(C(o,o,N(V(o,o),V(o,o))), q, N(V(q,q),V(q,q))),
h(x) = C(c,c,x).
```

By Change, `V(c,o) = N(V(o,o),V(o,o)) != V(o,o)` and
`V(c,q) = N(V(q,q),V(q,q)) != V(q,q)`. The second update preserves the
first comparison because `q != o`. Consequently `c != o` and `c != q`.

Changing coordinate c therefore leaves both comparisons intact. Every h(x)
differs from o and q. Also `V(h(x),c) = x`, so h is injective. The ground terms

```
o, q, h(o), h(h(o)), h(h(h(o))), ...
```

are pairwise distinct: injectivity cancels a putative repetition down to o in
the range of h, and q is outside that range. No Foundation, Infinity, Pairing,
or extensionality axiom was used. Since x occurs once in h(x), their expanded
length is linear in the iteration index, with a fixed coefficient from c.

The constant o is an assignment base and selector. It must not silently be
identified with an E-empty object in the lower direction. The proof does not
need that identification.

## 2. Formula representation gives the required full schema

For each fixed equality-free E-formula, give all its free and freshly renamed
bound variables distinct selectors from the preceding sequence. Use A for
membership atoms, N for Boolean operations, and Q for existential quantifiers.
An induction on the ordinary finite syntax gives a class code t that evaluates
the formula under the values `V(s,d_i)` of any assignment object s.

The quantifier step is exact because C changes the bound variable's coordinate
to any object of the common domain and preserves all other distinct selector
coordinates. It does not restrict substitutions to fresh or injective values:
different variables may receive the same object. This avoids the finite-sort
obstruction to the retired reduced logical engines.

Fix o and q for the matrix's input and output coordinates. Starting from any
assignment object, finitely update the other selectors to encode the desired
parameter tuple. The represented relation

```
R(b,t,x,y) = P(C(C(b,o,x),q,y),t)
```

then agrees with that arbitrary E-matrix at its arbitrary parameter values.
The fifth axiom supplies exactly its EPSC instance. Native equality need not
be encoded in these source matrices: the accepted raw EPSC calibration is
already equality-free. Equality remains genuine in Change and the clausal
proof engine.

## 3. The upper model does not assume a truth predicate

Inside ZFC, Con(ZFC) supplies a countable set-sized model M of ZFC. Choose o
to be its empty object for convenience. Define V and C in M by normalized
finite assignment graphs, with default value o. Invalid graph codes normalize
to the empty assignment. This makes Change hold for every domain object.

Externally enumerate the E-definable subsets of M, with finite parameters, by
the objects of M, and let P be membership in the represented class. The
enumeration is not asserted to be definable inside M. Each individual P-column
is an ordinary definable class of the E-reduct. Choose total N, A and Q from
the corresponding closure operations on those columns. Ambient ZFC Choice
or an enumeration-based selection provides the needed witness functions.

The object `q = N(o,o)` is a fixed parameter of M. For each particular b,t,
`R(b,t,x,y)` is E-definable using b, q and a finite E-definition of the
P-column t. Therefore M's existing EPSC theorem applies. It is not necessary
that N, A, Q, or the whole class enumeration be uniformly E-definable.

Formula coding is restricted to the E-language. No comprehension schema for
the expanded language with P,V,C is being asserted. This restriction prevents
an illicit self-truth construction.

## 4. The six shared clauses have the correct signs and dependencies

For fixed b,t abbreviate `B := G(b,t)=o` and `k := K(b,t)`. The shared
clauses, with all displayed variables universally quantified, are:

```
not B or R(b,t,k,U(b,t,d))
not B or E(T(b,t,d),U(b,t,d))
not B or not E(T(b,t,d),d)

B or E(T(b,t,x),x) or not R(b,t,x,y) or E(y,k)
B or not E(x,k) or not R(b,t,x,y) or E(y,k)
B or not E(y,k) or R(b,t,U(b,t,y),y)
```

If B holds, the first three clauses exhibit one input k such that every
proposed bound d has an output containing a member outside d. Hence the
local-boundedness premise fails. If local boundedness holds, B is impossible;
the last three clauses give closure from every E-empty input, recurrent
closure from every member of k, and unrestricted support of every member of k.
For an empty input x, the extra disjunct `E(T(b,t,x),x)` is necessarily false.

Conversely, if local boundedness fails, choose k to be a failed input and,
for each d, let U and T be an output and escaping member witnessing failure.
Set G to o. If the premise holds, choose k to be an EPSC hull and set G to q,
which differs from o. On this branch, U chooses supporting preimages for hull
members, and T chooses a member of x whenever x is nonempty. Give arbitrary
values where no obligation applies. All choices concern sets in ambient ZFC.

The reuse is safe because the two obligations for K, the two for U, and the
two for T occur on disjoint branches for the same b,t. No range axiom for G
is needed: the cases `G=o` and `G!=o` exhaust the possibilities. U and T retain
all b,t dependencies. A unary empty-member witness is also sound as an
unshared control, but has a larger signature.

The Q witness in the other nine clauses remains a separate ternary function.
Its obligations are ungated and must not be conflated with U or T.

## 5. Exact metrics

The direct unshared payload has 15 clauses, 35 literal occurrences, 183 term
nodes, one constant, and 13 proper function symbols. The shared version has
the same clauses and literals, 185 term nodes, one constant, and 10 proper
functions: six binary and four ternary. Both have at most four universally
quantified variables per clause and maximum term depth three.

The pinned source-34 FAK12 generator reproduces 28 clauses, 62 literals,
244 term nodes, two constants, and 15 proper functions, including a quaternary
witness. Its maximum clause-variable count is five. These are comparisons of
explicit finite logical payloads, not binary Turing-machine working states.

## 6. Independent finite verification

`check_fak5_epsc_block.py` reads the emitted shared JSON directly and interprets
its actual term and literal trees. It does not import the generator. It compares
the six-clause transformation with an independent direct evaluation of EPSC.

- On all 256 pairs of two-object E and R relations, it checks all 16,384
  assignments of the shared gate and witness functions. There are 1,616
  satisfying assignments, spread across precisely the 150 positive EPSC
  instances. This checks both directions exhaustively at that size.
- On all 262,144 pairs of three-object relations, 182,342 positive EPSC
  instances have explicitly constructed expansions satisfying the actual
  emitted clauses: 75,450 use the failed-bound branch and 106,892 use the hull
  branch. The 79,802 false EPSC instances are recorded; all possible witness
  assignments are not enumerated at this larger size.
- Three mutations flipping a gate or support polarity are rejected with
  concrete counterexamples.

The evidence file is `fak5_epsc_block_verification.json`. These are tests of
the local EPSC clausification. The complete FAK5 theory has no finite models;
the tests do not claim otherwise or prove its consistency by bounded search.

## 7. Optional further signature packing

Packing the eight non-V/C functions into one ternary J can be semantically
sound. Assign N the fixed selector o, so its decoded term is
`N*(a,b)=V(J(a,b,o),o)`. Compute q, c and further selectors from this term.
In an upper model, first compute the original selectors and original eight
function values, then define J by finitely many C-updates to store those
values in their distinct slots. Reading slot o recovers original N globally,
so the derived selector terms have their intended original values. This
resolves the apparent self-reference. A different N slot depending on the
yet-undefined tags would require another argument.

Such packing expands repeated selector terms and should be measured as a
separate control. A smaller signature alone need not give a smaller payload
or interpreter. The 10-function shared kernel is the cleaner primary proposal.

## 8. Independent review of the selector Lean file

The delivery's `formal/FiniteKernelSelectors.lean` states all assumptions as
fields of `Core`: an inhabited domain supplied by o, the two assignment-update
laws, and the NAND equivalence. Its proof of `nand_ne_self` is the expected
classical contradiction, and the two evaluations of `diagonal` use the
correct inequality orientations. `shift_injective` follows by reading its
own update coordinate; `shift_ne_o` and `shift_ne_q` preserve the two diagonal
comparisons. The induction proving `names_injective` correctly treats the
zero/successor cases and cancels one shift in the successor/successor case.
`names_avoid_q` then handles the additional reserved selector.

This is a correct formalization of the selector lemma. Its infinite sequence
is `o, h(o), h(h(o)), ...`, with q separately excluded; placing q second gives
exactly the selector ordering used by the Python formula compiler. The file
does not formalize EPSC calibration, its upper model, the syntax compiler,
the resolution implementation, or a binary Turing machine. The separate
successful Lean run recorded in the delivery checks the proof; this review
additionally checks that the formal statement matches the intended lemma.

## 9. Codec and refutation-engine source review

Reviewed `code/clause_codec.py`, `code/ground_resolution.py`,
`code/test_reference.py`, and `code/representation_and_audit.py` in the delivery.
I found no soundness or mathematical-completeness defect in their intended
finite-clause semantics.

The binary codec includes the function and predicate counts, every arity,
the equality predicate index, the maximum variable-slot count, the clause
count, every clause length, and all literal signs and term tokens. Variables
are independently renamed in each universally closed clause. The recursive
term parser consumes exactly the arity declared in the header. The decoder
rejects unused high term/predicate codes, truncated data, nonbinary equality,
and excess nonpadding bytes. Its format explicitly restricts header quantities
by the encoded file length, so an unused symbol with an arbitrarily huge
declared arity is outside this format. This restriction is consistently
enforced by both encoder and decoder and affects none of these kernels.

Native equality is handled by reflexivity, symmetry, transitivity, function
congruence, and predicate substitution. Quotienting any nonempty model of
these finite clauses by the congruence yields an ordinary equality model of
the input clauses. Symmetry supplies the reverse predicate substitution.
The equality predicate itself needs no additional congruence row beyond
equivalence. Adding a fresh constant when the input has none preserves
satisfiability under the stated nonempty-domain convention.

At depth d, `ground_terms` produces every ground term of height at most d.
Each source clause is instantiated at every tuple from this common set of
terms, including tuples with repeated values. The search keeps previous
instances and saturates by propositional resolution. Every unordered pair
of clauses is processed when its later index is dequeued; newly generated
resolvents are queued, so no pair is lost across depth boundaries. A stage
has only finitely many atoms and hence finitely many set-valued clauses, so
its saturation terminates. Herbrand compactness and completeness of ground
resolution then give the unbounded procedure's mathematical completeness.
The certificate checker reconstructs every axiom instance and checks both
parents and the pivot of every ground resolution, independently of search
state. The empty-clause conclusion is explicitly checked.

The delivered 512-case propositional controls are an appropriate exhaustive
test of the small resolution core; they also exercise every clause-set
choice on two propositions. They do not establish the general completeness
theorem or calibrate the set theory. The source proof above explains why
the enumerator is not a finite-variable or finite-depth truncation.

The formula compiler uses the same selector order proved above, recursively
translates atomic E, NAND, and existential formulas, and constructs parameter
assignments only in slots numbered at least two. Its truth and falsity terms
are the correct NAND tautology and contradiction. Repeated variable names
under quantifiers are interpreted by ordinary coordinate update.

The implementation is a reference, not a practical ZFC consistency test or
a binary-machine compiler. Its recursive term traversal and proof-DAG
extraction are subject to Python's recursion limit, as well as ordinary time
and memory bounds. The unbounded completeness statement concerns the
underlying algorithm with adequate resources; the concrete Python program
does not promise to execute arbitrarily large finite certificates under its
default interpreter limits. Ground resolution is deliberately expensive.

## 10. Upper-model details checked against the written theorem

The upper construction correctly uses the whole domain of a countable
set-sized model M, not just its internally natural-number objects. Countability
of the domain and of ordinary finite formulas with finite parameter tuples
gives an external enumeration of all definable columns. One can choose every
constructor value by the least available code in an external enumeration,
so the external total functions N, A, Q exist as sets in ambient ZFC.

No transitivity or omega-standardness of M is required. If M regards an
assignment graph as finite while that graph is externally infinite, its
internal function and update theorems still give genuine uniqueness and the
two Change laws for all domain arguments. The uniform E-definitions of V,C
therefore remain suitable for the fixed-column argument. The upper proof's
use of ordinary logical equality within E-definitions is allowed; M is a
model of full ZFC, even though the lower reduction only needs equality-free
EPSC matrices.

For each b,t, only the fixed class D_t and the fixed parameters b,q occur in
the E-definition of R. The potentially nondefinable external function N is
not quantified over within that definition. This is exactly the separation
needed to apply each ordinary EPSC theorem of M without assuming a truth
predicate for the expanded structure.

## 11. One further measured definitional extension

The generator's `named_selector_kernel` adds a new constant q and the single
unit equation `q = N(o,o)`, then replaces the four repeated selector terms
inside represented relations by q. Genuine equality makes this a conservative
definitional extension of the shared kernel. Every shared model has the
unique expansion interpreting q as N(o,o), and substituting the equation
recovers all original shared clauses in every expanded model.

Independent regeneration and binary round-trip give:

| Presentation | Clauses | Literals | Term nodes | Meaningful bits | Stored bytes |
|---|---:|---:|---:|---:|---:|
| Original FAK12 | 28 | 62 | 244 | 1609 | 202 |
| Direct represented EPSC | 15 | 35 | 183 | 1146 | 144 |
| Shared witnesses | 15 | 35 | 185 | 965 | 121 |
| Shared witnesses, named q | 16 | 36 | 181 | 957 | 120 |

The named version has two constants and ten proper function symbols. With
four variable slots, exactly sixteen term-token values still fit in four
bits. The code includes the additional arity and defining equation in the
957-bit total; its SHA-256 is
`8189e846a54cc9bf67a1343cdaeadf4158f7aaca7a78bf6f9132fd1c3fe77b25`.
This improvement is a measured fixed input payload, not a converted machine
state saving.

## 12. Review of the 901-bit constructor variant

The subsequently generated `fec16b_compressed_clauses.json` makes three
additional changes, each mathematically sound at the stated ZFC-level
consistency calibration.

First, a native binary predicate B(b,t) replaces the six occurrences of the
equality test G(b,t)=o, retaining every literal sign and both arguments. The
G function can then be deleted. A B-model expands to the original gated
model by G=o when B holds and G=q otherwise; conversely the equality test
defines B in every old model. B need not be E-definable, since B is absent
from the relations whose EPSC instances are applied.

Second, a separate q constant with the unit inequality q!=o suffices in place
of its defining equation q=N(o,o). The lower selector construction must use
this actual q throughout the second coordinate and diagonal term. The proof
of c!=o,q uses only q!=o and NAND's pointwise diagonal inequality. The upper
model remains available by choosing q=N(o,o). This is a new calibrated
presentation, not a definitional extension of the old presentation in both
directions.

Third, the unit equation N(a,b)=N(b,a) replaces the second positive NAND
clause. Instantiating the retained positive clause with arguments b,a and
substituting the unit equality derives precisely the omitted clause.
Together with the negative clause, full NAND semantics follows. For the
upper model, choose N(a,b) as the least external code for the class
complement(D_a intersect D_b). The represented class is symmetric in a,b,
so the selected code itself is symmetric. This changes the available
constructor choice; literal commutativity is not claimed of an arbitrary
previously chosen code function.

The emitted signs and dependencies agree with these arguments. The payload
has 16 clauses, 35 literals, 167 term nodes, two constants, nine proper
functions, and three binary predicates besides equality. The current codec
records 901 meaningful bits and 113 stored bytes, with SHA-256
`e3daf5766bd850ceb19667e476378aa8ae116633b00afcd32b244b7b234b5cd6`.

A concrete review finding was repaired before delivery: the original formula
example compiler hardcoded N(o,o), appropriate to the term-selector control
but not to the independent-q variant. The repaired `selector_term` accepts
`selector='term'` or `selector='named'`; `class_term` and
`parameter_assignment` propagate that choice through every recursive call,
including the diagonal term's q. Independent inspection and execution confirm
the repair. Replacing q by N(o,o) in each of the first eight named selectors
recovers the original selector exactly. Both delivered formula examples and
parameter-assignment terms regenerate exactly and are well formed in their
respective 901-bit and 917-bit signatures. The serialized kernels independently
round-trip at their recorded bit counts and SHA-256 values.
