# Seed-selected arithmetic certificates

These files implement the new computation-packet normal form. The numerical
and logical presentations are inherited from the attributed ProveIt drafts.
The new mathematical step is the simultaneous normalization below; the
opener and arity representation are inherited.

## Run

Each checker reads one JSON array from standard input. The last item is the
goal. Earlier items are instruction packets, consumed from the end. Success
prints exactly `ACCEPT` and exits zero. A failed check raises an exception
and exits nonzero. Unused prefix packets are permitted. Count acceptance
only when both exit status and the exact success output agree.

`checker.py` is the preferred implementation with an explicit list test.
`checker_bytes.py` uses the inherited exact-JSON zero-product list predicate.
`checker_joint.py` uses the inherited generic exception-based traversal;
malformed nonempty strings rely on the fixed Python runtime's recursion
limit for rejection. Its canonical finite array/integer interface has
structural recursion. Do not omit this qualification when quoting its size.

## Canonical language

Numerical terms denote zero, successor, and initialized scalar iteration
`I(n,a;v.h)`. Iteration binds its previous state, not a recursion counter.
Formulas are equations, unary paired binders D, and internal Q resources.

| Raw shape | Numerical meaning | Formula meaning |
| --- | --- | --- |
| `[]` | Zero | Truth |
| `[b]` | Successor, with two dummy zero slots | Paired binder D |
| `[s,t]` | Zero annotation | Equality |
| `[n,a,h]` | Scalar iteration, one state slot | Q, using the third field |
| Arity at least four | Zero | Truth |

A canonical Q resource is `[B,B,B]`; D is `[B]`. The opener increases
depth by `5-len(node)`. Numerical roots have depth three. Coordinates
0, 1, and 2 denote zero; under binders, 3 and 4 name the nearest protected
slot, 5 and 6 the next slot, and so on. Allocated negative integer labels
name rigid parameters. The producer uses one representative per slot.

## Packets

A packet is `[m,s,u,t]`.

* If `m` is truthy, verify it as an elimination major. Matching equality
  or Q endpoint fields perform transport/specialization. A unary D major
  exports its triplicated Q body. The other exports are truth aliases.
* If `m` is falsy and `u` is truthy, supply an arithmetic equation. Here
  `s` is the predecessor discriminator, `u` the initializer, and `t` the
  update. Falsy `s` supplies the zero equation; truthy `s` supplies the
  successor equation at predecessor `s`.
* If `m` and `u` are falsy, introduce the unary D goal with witness `t`.
  The canonical marker `m=0` permits progress only when the opened matrix
  is a literal equation; `m=[]` selects the case rule. The `s` field is
  unused in this branch. In particular, a literal-zero witness is allowed.

Thus arithmetic has no separate null opcode. The producer retains null
as a harmless falsy marker in its arithmetic packets, but verification
also includes an arithmetic packet whose marker is Boolean false.

## Simultaneous normalization

Let `C=I(2,1;v.0)`. The successor equation with predecessor 1, initializer
1, and constant-zero update directly proves `C=0`. Both its required
inputs are nonempty raw terms.

For any computation equation whose initializer is literally zero or whose
successor predecessor is literally zero, form a fresh motive E(w) by
replacing exactly those positions, simultaneously, by w. Keep passive
zeros in the update unchanged. Then E(C) is an allowed direct computation,
and equality transport using C=0 proves E(0), the original equation.
Each affected computation leaf therefore becomes exactly three native
inference nodes: one transport and its two direct computation premises.
No recursive normalization theorem or decision about a term's numerical
value is required.

## Fresh computation assumptions

Raw arithmetic packets do not necessarily generate equations true
uniformly in newly admitted parameters. With `m=0,s=0,u=3,t=0` and an
equation goal, the new assumption decodes as
`H(k): I(0,0;v.0)=k`: the initializer coordinate 3 is a dummy zero under
the iterator, while its occurrence at the equation endpoint is opened
at the fresh parameter k. H(0) is true, but H(1) is false.

Soundness uses the known-zero-instance supply rule: if H(0) is derivable
and the fresh k occurs in neither the retained context nor the conclusion,
a proof of that conclusion under H(k) can have k replaced by zero, after
which H(0) is cut in. The tests cover both an accepted independent
continuation and rejection of an attempted closed false consequence.

## Reproduction

Run `python3 verify.py` for 216 complete process checks: 36 cases, three
profiles, and ordinary plus optimized Python. Run `python3 measure.py`
for whole-module metrics and deterministic maximum-compression gzip files.
The producer, measurements, and tests are outside every checker's trusted
source. None is imported by a checker. The tests are finite integration
evidence, not a proof-assistant verification of soundness.
