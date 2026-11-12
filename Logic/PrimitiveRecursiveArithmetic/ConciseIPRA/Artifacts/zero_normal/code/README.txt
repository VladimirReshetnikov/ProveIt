ZERO-COUNTER NORMALIZATION: EXECUTABLE ARTIFACTS
Prepared November 11, 2026 (America/Los_Angeles)

Result
------
zero_six.py implements six rules: hypothesis, successor computation,
crossed one-context equality, Q elimination, D elimination, and the
witness-selected D introduction. Literal-zero-counter iterators are absent
from input term syntax. Capture-avoiding substitution rebuilds every term
with I(0,a;u.h) replaced by a. The zero computation axiom is therefore absent.

zero_seven.py separates case D introduction and equation-progress Q
introduction. Its substitution operation is stable under numerical
substitution without a witness-mode side condition; it is a convenient
intermediate for translating legacy proofs into the six-rule calculus.

Names and comparisons
---------------------
  zero_six.py       Final six-rule kernel; 3095 normalized bytes.
  zero_seven.py     Separate-introduction kernel; 3272 normalized bytes.
  control_seven.py  Equally factored old seven-rule control; 3145 bytes.
  control_eight.py  Equally factored old eight-rule control; 3322 bytes.
  upstream_one_context.py  Frozen repository checker; 3358 bytes.
  upstream_native.py       Frozen repository checker; 3382 bytes.

Both matched reductions remove 50 normalized bytes, 11 significant Python
tokens, and 5 AST nodes. Gzip-9 increases (964 to 977 for the six-rule
comparison, 984 to 996 for the seven-rule comparison). Compression is only
informational. The .py.gz files contain normalized sources with gzip level9
and timestamp0; raw sources retain their ordinary formatting.

These are full tagged-syntax checkers with exact term/formula/scope checking.
Their byte counts do not beat the separate permissive arity-code contract
whose leading repository checker is 521 bytes. No global minimum is claimed.

Input and invocation
--------------------
Every checker reads one JSON object from stdin, with exactly four fields:
  variables: nonnegative integer, the number of free numerical variables;
  context: list of formulas;
  goal: formula;
  proof: proof tree.
An accepted certificate exits normally and prints exactly ACCEPT followed
by a newline. Invalid certificates exit with nonzero status. Python's
resource limits can reject very large valid certificates.

Run an example:
  python3 zero_six.py < examples/used_hypothesis_induction_one_zero_six.json

Terms use de Bruijn variables:
  ["v",i]           variable i;
  ["z"]             zero;
  ["s",t]           successor;
  ["i",n,a,h]       iteration, binding variable0 in h only.
In zero_six.py and zero_seven.py the counter n of every supplied iterator
must not be literally ["z"]. This restriction applies recursively, including
inside bodies, contexts, templates, and witnesses. Proof data with an I0
redex is rejected, even if erasing that redex would hide bad scope data.

Formulas:
  ["=",s,t], ["q",B], ["d",B].
Q binds one variable in B. D binds y at index0 and x at index1.

Six-rule proof tags:
  ["hyp",index]
  ["succ",counter,seed,body]
  ["tr",term_template,major_proof,minor_proof]
  ["qe",target,closure_proof,base_proof]
  ["de",goal,existential_proof,continuation_proof]
  ["di",matrix,witness,premise_proof]
The eight-/seven-rule old controls additionally have ["zero",seed,body].
The separate-introduction controls additionally have ["qi",equation,premise].
All schemas and side conditions are implemented explicitly in each module.

Verification
------------
  python3 verify.py

The script validates and translates 64 inherited positive certificates,
including equation induction with its hypothesis used, numerical witnesses,
nested logical binders, and open equation transport. It checks all outputs
against standalone kernels. Additional examples exercise replacement of a
case assumption underneath a fresh DE eigenvariable and a closed nonliteral
zero witness. Negative cases include I0 redexes in every input position,
hidden scope escape, invalid tags, incorrect goals, and mismatched equality
premises. Every process check is repeated under Python -O.

The recorded run has 500 process checks, zero mismatches, and 4832
substitution-commutation checks. Other property counts are in
verification.json. Finite executions do not replace the universal proofs.

translate.py is untrusted elaboration code. No checker imports it. Its
seven-to-six transformation repairs the removed case-introduction instance
at witness0 using J0=I(1,0;u.0), transports the local base via J0=0, replaces
the assumption capture-avoidantly, and transports the successor endpoint
back. There is no claim of linear serialized proof-tree overhead.

Provenance
----------
Repository: VladimirReshetnikov/ProveIt
Pinned commit: ecb3b847290c33b1ef7f04571cac63e97c73a54e
Base directory: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
Upstream sources: Research/one_context/direct/{native_checker.py,
  one_context_checker.py,certificates/}

The frozen upstream sources and inherited fixtures are distributed under
the repository's MIT-0 license; see LICENSE-ProveIt.txt. The controls are
explicit local adaptations of those sources. The checker additions and
proof compilers are supplied for inspection and reproduction, without a
claim of proof-assistant verification unless separately accompanied by a
completed Lean theorem in the surrounding research package.
