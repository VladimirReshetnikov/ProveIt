COMPOSED ARITY / UNIFORM-PREDECESSOR CHECKER

This is an independently implemented synthesis of two existing draft mechanisms,
not a new arithmetic foundation or a significant new axiomatization.

checker.py: 604 normalized bytes / 266 tokens / 312 AST / gzip9 356 bytes.
checker_explicit.py: 612 bytes / 266 tokens / 310 AST / gzip9 360 bytes.
checker_short.py: 593 bytes / 267 tokens / 315 AST / gzip9 355 bytes.
checker_guarded_ast.py: 690 bytes / 269 tokens / 300 AST / gzip9 371 bytes.

The first and third use the inherited exact-JSON-list test a*0==[]. The second
uses isinstance(a,list) and is the preferred explanatory profile. All four
terminate structurally on finite JSON; none relies on recursion limits to reject
strings. The short profile uses inherited Boolean short-circuit expressions.
The guarded AST profile matches, but does not beat, the current 300-AST minimum.
It traverses a+[] inside try/except: strings fail immediately, and a tail loop
uses immutable tuple contexts to avoid leaking child assumptions. Against the matched
arity-byte driver (608/265/314), the 604-byte synthesis saves 4 bytes and 2 AST
nodes but costs 1 token. Existing snapshot coordinate minima were 616/268/300.
The exact matched and unmodified references are under reference/.

Public interface: JSON array of four-field instructions followed by a closed
formula. Packets are consumed from the end. Success is exit0 with exactly
ACCEPT plus newline. An exception rejects; an unused prefix is inert.

Native formulas encode Eq(s,t)=[s,t], D(x,y).B=[B], Q(y).B=[B,B,B]. Numerical
zero=0 or [], successor=[t], and I(n,a;u.h)=[n,a,h]. Numerical roots have opening
base3. Positive variable coordinates start at3; unary numerical nodes protect
two dummy zero slots, ternary iteration protects one slot (dummy for counter
and seed, state for update). Node traversal adds 5-len(node). Higher-arity
formula nodes are constant truth and numerical nodes are constant zero, with
traversed annotations. The opening lemma is semantic at meaningful roots;
raw idempotence below ignored high-arity fields is false, as recorded.

Instructions: truthy major m is proved before transport/Q specialization/D
elimination. A null major supplies the equation for predecessor p=s, seed a=u,
update h=t: I(0,a;h)=a when p is raw-falsy, otherwise
I(Sp,a;h)=h[I(p,a;h)/state]. The successor is constructed internally. Other
falsy modes introduce D: [] selects base/case, 0 selects progress for literal equation matrices (and harmless even-arity
truth aliases). Literal witness0 is supported directly.

The symbolic producer uses named formulas and genuine primitive rules; it does
not import or run the checker. It combines the uniform-predecessor proof
producer (including a verified box for IS at literal-zero predecessor) with
the arity-calculus encoder. It is an example producer, not a general automatic
compiler from arbitrary ordinary-iPRA derivations.

Validation performed:
- 42 named/adversarial packets across 4 programs, normal Python and -O;
- 10 malformed public inputs across the same programs/modes;
- total 416/416 ordinary CLI checks passed;
- 4 deliberately unsafe mutations in both modes, 8/8 admitted their targeted
  forbidden certificate or false equation, while the original rejected them;
- 24,050 arithmetic source triples, 55,443 valuations of generated equations,
  216 independently encoded substitution checks; no counterexample or budget skip.
These are finite implementation checks, not formal proofs of soundness.

Reproduce all metrics and checks: python3 reproduce.py.
Individual checks: python3 test_checkers.py; python3 independent_audit.py.
To inspect measurements without executing reference proof checkers, import
source_measure.metrics and apply it to each source listed in metrics.json.
The saved source_measure.py is an unmodified upstream measurement module; its
CLI path expects the original upstream package, so use its metrics function.

The mathematical transfer argument is in composition_note.txt. The full
inherited Choice-DI/ordinary iPRA bridge must remain attributed when reused.

ADDITIONAL SAME-DRIVER AUDIT

Screening 105 old complete-program profiles under the same rejection driver
finds a 601-byte affine control (274 tokens, 318 AST, gzip 358). The new
593-byte profile saves eight bytes, about 1.33 percent, against that stricter
minimum. The 604-byte and 612-byte profiles do not beat it. Matched token
and AST minima are 264 and 297 and remain unbeaten by the new family.
The exact affine source and transformed control are included.
