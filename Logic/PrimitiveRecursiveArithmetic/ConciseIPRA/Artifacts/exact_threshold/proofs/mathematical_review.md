# Independent mathematical review of exact_threshold.py

Reviewed candidate: `research/optimizer/exact_threshold.py`.
Control: the incoming `ipra_intrinsic_validation/code/checker.py`.

Result: the three inspected changes support a new sound and complete input
presentation of the same eight-rule native calculus. They do not establish
identical acceptance of arbitrary old and new JSON certificates, and they do
not delete an arithmetic axiom. This is a paper-level operational review,
not a formal verification of Python or a new proof of the inherited iPRA
bi-interpretation.

## 1. Threshold-selected introduction

The old selector is

    len(a) == 2 == u

and the new selector is

    len(a) == 2 > u.

Python reads the latter as `(len(a) == 2) and (2 > u)`, evaluating `u` in
the second comparison only when the opened matrix has length two.

The selector is reached as an introduction selector only after a neutral
major and the successful witness opening `a := i(*a,t,2)`. A successful
opening returns an integer/Boolean/list tree. Thus a successful `len(a)==2`
test identifies an equation matrix in the inherited formula reading, not
an arbitrary two-character string or other JSON value.

If the comparison is true, the retained assumption is the parameter
instance of that equation and the continuation proves its successor
instance. This is the existing DI-progress rule. If it is false, the
retained assumption is the zero instance and the continuation proves the
successor instance. This is the existing DI-case rule. A comparison error
rejects. Therefore no successful threshold choice applies induction to a
compound formula.

Both legitimate modes remain available in canonical certificates:

* Set `u=1` to choose progress on a literal equation.
* Set `u=2` to choose cases on a literal equation.
* Compound matrices choose cases regardless of the second comparison.

These choices do not change the supplied witness, which remains `t`. Both
1 and 2 are permitted root-term auxiliary codes during proof checking and
have the numerical reading zero. In a canonical introduction, `m=[]`.
The later elimination comparison cannot accidentally fire: its expected
major is a two-element slice or a triple repetition, neither of which is
the empty list. This permits the ordinary rule-by-rule completeness
construction with the new mode values.

One should not describe this as a global replacement of every packet's
second field: that field also serves other roles at non-introduction
instructions and at terminal computation instructions. A compiler changes
mode choices when compiling introduction nodes, or reconstructs the checked
call tree before translating an existing certificate.

Foreign JSON values in `u` need not all be rejected merely because they
influence a mode. When `2>u` is meaningful, it still chooses one of the two
already sound rules; when it is meaningless, checking rejects. For example,
a Boolean mode field can change its mode between the old and new programs.
This is a change in proof syntax, not in the public formula grammar.

## 2. Omitting a discarded source-instance scan

The old expression computes both entries of

    (a, i(t,s))[elimination_matches]

before selecting one. The new expression is

    i(t,s) if elimination_matches else a.

The opener `i` has no state writes, does not consume packets, and does not
mutate any input tree. Its only relevant outcomes are a fresh result or
failure. Consequently, when the elimination match succeeds, both programs
check the same source and target instances at the same floor. Their order
changes, but successful values and the native substitution inference do not.

When the match fails, `i(t,s)` contributes no value to the continuation's
goal or to its added context. The continuation uses `a`. Dropping this
discarded scan may admit certificates whose unused source image is invalid,
out of scope, or otherwise rejected by the old eager traversal. It cannot
introduce that source image into the proved statement. The target-instance
scan `i(t,u)` in the match remains present, as do the witness opening, major
subproof, opened assumption, and successor-instance opening.

Terminal cases are unchanged: the lazy expression is not reached after a
retained-hypothesis or computation match. A computation candidate is still
checked by equality with the already scanned goal under the inherited
typed-equality argument.

The proof is therefore direct extraction of a native rule from each
successful new call. It must not be stated as literal simulation of every
new successful trace by the old eager program. The old program may reject
an irrelevant annotation which the new program never traverses.

## 3. Reader and public aliases

Replacing `from json import load` and the separate assignment of `q` by
`import json` and

    c([[]], (q := json.load(open(0)).pop)())

uses the same standard JSON parser and the same bound list-pop method.
The assignment to `q` occurs before its call and before entering `c`.
The popped final element is still the public goal; preceding elements are
still consumed right to left. This neither evaluates certificate source
nor imports any new theory data.

The opener is byte-for-byte unchanged from the intrinsic control, and its
first public scan still occurs at floor zero, before the reservation that
decreases `k`. Accordingly:

* The public language is exactly the genuine-binder Eq/D grammar with its
  documented Boolean-true spelling of numerical zero.
* `true` passes exactly where public integer code 1 passes and has the same
  arithmetic reading.
* `false` fails the public odd-code test. The fallback then scans the
  function sentinel and fails; it does not quietly become zero.
* Public floats, strings, nulls, objects, wrong arities, free labels and
  out-of-scope slots remain rejected by the same checks.

These statements concern the public goal. Unused fields and prefixes can
contain arbitrary JSON, as in the intrinsic control. In particular, the
new lazy branch need not scan an irrelevant `false`, float, or object.

## 4. Native equivalence and the inherited iPRA bridge

The primitive native inventory remains Hyp, I0, IS, Tr, QE, DE, DI-case and
DI-progress. The same canonical code is used: zero is 1, successors are
unary lists, iterators are ternary lists, and genuine binders determine
scope. The discarded zero-code experiments and their missing-IS0 repair
are NOT part of this final candidate.

Soundness follows from the control's successful-opening and scope lemmas,
the unchanged terminal cases, and the two branch arguments above.
Completeness follows by compiling the same native derivation and using the
new canonical introduction-mode fields; skipping an unused scan cannot
reject that construction. The source-selected elimination and its
literal-zero-source completeness argument remain inherited unchanged.
The native/iPRA whole-domain bi-interpretation, equality interpretation,
and two round trips consequently transfer through the unchanged native
theorem set.

## 5. Conditions that must not be weakened in the report or implementation

1. Progress requires a literal equation; the threshold alone is not its guard.
2. The opener's three-positional-argument arity boundary must remain intact.
3. Public scanning must precede the fresh-floor reservation.
4. The major proof must still be checked, and the floor must keep decreasing
   across that proof and the continuation.
5. A selected equality/closure elimination must still check both relevant
   instances. Only the unselected source instance is omitted.
6. Acceptance equivalence on arbitrary JSON is not claimed; theorem-set
   equivalence and exact public-language validation are the claims.
7. The complete checker is counted, including parser and acceptance output.

## Sources inspected

* Candidate `research/optimizer/exact_threshold.py`.
* Incoming intrinsic control `code/checker.py` and its readable expansion.
* Incoming `ipra_intrinsic_validation.tex`, sections on native rules, public
  syntax, raw readings, opening, arbitrary-JSON traces, and correctness.
* Its `evidence/independent_math_review.md`.

Repository snapshot containing that incoming archive:
`f25af53c682ea76c57b67c70c976bcaf836b0c91` of
`VladimirReshetnikov/ProveIt`.
