LATE COMPARISON: INITIALIZER EVALUATION IN THE 2283-BYTE GOAL CHECKER

The repository advanced during this investigation. At commit
56aafa39cf53a47dc4ae9f3a030fd8ac279a5624, Research/clausal_single_evaluation
already supplies a smaller goal-directed implementation of the old Step
rule. This folder contains its exact selected source (control_step.py)
and an initializer-evaluation adapter (checker.py) with the same public
grammar and validation contract.

The only executable changes are in its arithmetic case:

  Step major: I(c,a;h)=b        Seed major: a=b
  Step result: r=h(b)          Seed result: r=h(I(c,b;h))

The common second premise is I(S c,a;h)=r. Zero iteration is contracted
by syntax. Counter and body are kept fixed. The code represents S(t) as
[0,t], I(c,a;h) as [c,a,h], equality as [s,t], and D as [B]. A first bound
variable has index 1; fresh branch parameters are negative levels.

The Seed adapters' arithmetic packet is ['v',c,a,h,b,major,minor]. The older
control uses the same packet positions, but its major verifies the entire
predecessor iteration against b. Both retain the upstream convention that
a validated reflexive goal closes regardless of its unused proof payload;
the examples use null for this leaf. This convention does not prove any
nonreflexive equation and is unchanged between the matched programs.

MEASUREMENT

CPython 3.12.14, remove the module docstring, apply ast.unparse, append LF:

                       Bytes  Tokens  AST  Gzip-9
Upstream Step           2283     741   826      818
Initializer evaluation  2283     741   826      822
Shared-walk Step        2265     709   787      872
Shared-walk Seed        2265     709   787      877

In each matched pair, the three primary source coordinates tie. The shared
traversal saves 18 bytes, 32 tokens, and 39 AST nodes in BOTH arithmetic
interfaces. This is a validator/substitution refactoring, not a saving
caused by the Seed rule. The files are control_step_shared.py and
checker_shared.py. The source programs include their full syntax and
scope checks. Therefore initializer evaluation
does not establish a source-size improvement against this latest compact
goal-directed implementation. The direct computation certificate still
avoids supplying the whole predecessor iterator as the fourth arithmetic
term argument. No claim of a new global checker minimum is made.

VERIFY

  python3 validate.py
  python3 checker.py < examples/seed/nontrivial_seed_equality.json

The validator authenticates the exact control source, checks equal public
goals in each old/new certificate pair, runs all four programs in normal and
optimized Python, checks rejection cases, and recomputes all measurements.
It writes evidence/metrics.json and evidence/verification.json.

The eight positive pairs cover zero and positive predecessor counters,
nontrivial seed equality, fixed passive data in the counter and body,
zero contraction inside a nested body, bound-counter substitution,
an occurrence below a nested state binder, and a genuinely used equation
induction hypothesis. The rejection cases cover an unsupported equation,
invalid syntax hidden in a zero iterator, a noncanonical zero iterator,
an unsupported changed seed, a wrong initializer, a Boolean initializer,
a wrong result, and unproved erasure of a term merely provably equal to zero.

The fixtures were first checked in the main forward Seed calculus,
translated to its Step control, then re-encoded in this goal protocol.
The standalone checkers do not import the producer or the main kernels.
Finite checks support the implementation; the general equivalence rests
on the report's written proof.

SOURCE AND SCOPE

https://github.com/VladimirReshetnikov/ProveIt/blob/56aafa39cf53a47dc4ae9f3a030fd8ac279a5624/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Research/clausal_single_evaluation/code/checker.py

Exact Git blob: 38f80e16a9b4cc92ced82ddb659cc464e919a77c
Exact source SHA-256:
e24664d1d6b562fe29239d6eed073ed33cae14f8b7042ddaa7c2963131161108

The late package also already states two-Eval congruence and four-Eval
transport. Those proof macros are inherited, not new results here.
The report's primary comparison remains explicitly pinned and its local
forward-checker reduction is distinguished from this late tie.
Upstream material retains the MIT No Attribution license included in the
main package. No repository write was made.

SHARED TRAVERSAL AUDIT

With sort=1, only equation arrays of length 2 and D arrays of length 1
are accepted. With sort=0, an array is a successor [0,t] or an iterator
[c,a,h]. Integers are accepted only in term positions and are checked
against the current numerical scope and binder depth. A D child is a
formula at two extra binders; the third child of an iterator is a term
at one extra binder. The generic root sort -1 is used only for opening;
child sorts are still fixed by the root arity. Formula and successor
arrays have the same binder-free two-child profile, so that ambiguity
does not affect opening.

Every child is traversed before contraction. On input validation,
comparing the rebuilt expression with the input rejects noncanonical
zero iterators. On opening, contraction is retained. No replacement
term has a free positive index at insertion; its own bound variables
remain local, and negative levels denote ambient parameters. Hence
insertion below a binder needs no shift of the replacement.
