# A redundant truth equation: a complete 921-bit stack packet

## Result and scope

Delete only equation 1, `d = N(d,N(d,d))`, from the supplied 946-bit
equational stack-EPSC packet. All other equations, their order, operation
signature, variable convention, and ground endpoints remain unchanged.
The removed equation follows from three retained universal equations.
Consequently the new 13-equation theory has exactly the same models and
equational consequences as the original 14-equation theory.

Precisely, writing E921 and E946 for the two universal equational theories,

    E921 |-eq d = N(d,N(d,d)),
    and, for every equation u = v,
    E921 |-eq u = v if and only if E946 |-eq u = v.

The first syntactic conclusion follows from the all-model argument below
by ordinary equational completeness; an explicit Sh1-only rewrite trace
for the deleted equation is not supplied.

The same complete codec now emits **921 bits**, comprising 55 header bits,
850 equation bits, and 16 endpoint bits. There are 209 term nodes, 13
operation symbols, three local variable slots, and four-bit opcodes. The
25-bit saving is exactly one equation marker plus six four-bit term nodes.
This is a local reduction of this supplied packet, not a global minimum
or a binary-machine state saving.

## Exact dependencies and equations

Let E abbreviate the binary operation `p_eps`, and write the retained
universal equations as follows (numbers are the original packet numbers):

0. `N(N(x,N(N(y,x),x)),N(y,N(z,x))) = y` (Sh1)
4. `E(s,P(a,b)) = N(E(s,a),E(s,b))` (class NAND)
7. `d = N(E(P(z,s),a),N(d,E(s,Q(a))))` (arbitrary witness)

The established Sh1 theorem identifies N with NAND in a Boolean algebra.
This is the same inherited Boolean-basis dependency used by the original
946-bit construction. No assumption that d already denotes Boolean top
is used in the argument below.

The source is W. McCune, R. Veroff, B. Fitelson, K. Harris, A. Feist and
L. Wos, *Short Single Axioms for Boolean Algebra*, Journal of Automated
Reasoning 29 (2002), 1-16, Theorem 2:
https://www.cs.unm.edu/~mccune/papers/basax/v12.pdf . The precise inherited
stack-kernel source is ProveIt Source79 at commit
13ec39ed43148b1807f51ed6e6528e1c84659562, with its source note at
https://github.com/VladimirReshetnikov/ProveIt/blob/13ec39ed43148b1807f51ed6e6528e1c84659562/SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/code/79-zb242-res-stack-kernel-stack_kernel_note.tex .

## Ordinary proof in every algebra

Fix arbitrary s,z,a, possible because the signature contains the constant
d and therefore every algebra is nonempty. Let

    e = E(P(z,s),a),
    q = E(s,Q(a)),
    r = E(s,Q(P(a,a))).

In the Boolean algebra supplied by Sh1, write 1 for its top, independently
of the interpretation of d. Equation 7 becomes

    d = not e OR (d AND q).

Joining both sides with e gives

    d OR e = 1.

Apply equation 7 a second time with a replaced by P(a,a), keeping s and z
unchanged. Equation 4 at stream P(z,s) identifies its left incidence value
with `N(e,e) = not e`. Hence

    d = e OR (d AND r),
    d OR not e = 1.

Distributivity now gives

    d = d OR (e AND not e)
      = (d OR e) AND (d OR not e)
      = 1.

Thus `N(d,N(d,d)) = N(1,N(1,1)) = 1 = d`, precisely the deleted equation.
This works in trivial and nontrivial Boolean algebras and does not use
ultrafilters, a quotient of native functions, the stack projection laws,
the selected-witness equation, atomic membership, or any closure clause.
In particular q and r need satisfy no relation to one another.

Every original model is a reduced model by forgetting an axiom. The proof
shows that every reduced model is already an original model on literally
the same carrier, with literally the same interpretations. Ordinary
equational completeness therefore gives identical equational consequence
relations. Equivalently, a finite derivation of the removed identity may
be substituted wherever it is used; no separate model-expansion or
consistency-only argument is required for this reduction.

The new packet retains the ground endpoints `N(d,d)` and `d`. Therefore
its ground nonderivability statement has exactly the old ordinary
ZFC-formalizable Con(ZFC) calibration, subject to the explicitly inherited
raw-EPSC/ZFC, Sh1, and equational-completeness dependencies. This is neither
a new Lean/Rocq check nor a supplied internal PA proof-code translation.

## Exact source and reproducibility

Input archive: `research_sub239/inputs/BusyBeaver239_Research_2026-10-19.zip`.
The source prefix in that archive is
`zfc239-coordinated-reuse-2026-10-19/foundations/`.

Relevant unchanged inputs copied into this directory:

- `stack_kernel_source79.py`
- `fuse_stack_packet.py`
- `packet946.json`, copied from
  `generated/stack_epsc_explicit_pick_cons_nand_truth_fused_spare_pick.json`
- `stack946_note.tex`, the inherited ordinary-calibration exposition
- `ATTRIBUTION.txt`, copied unchanged from the foundations directory

The source note attributes the original native stack to ProveIt Source79,
the false-class witness-slice technique to Source40, earlier truth fusion
to the Source78/79 reviews, and the new incoming 946-bit packet's shared
constructor and chosen slice composition to its supplied note. Those are
inherited results. The new contribution here is deletion of the explicit
truth equation by the three-equation argument above, plus its exact
same-codec artifacts. No general historical-priority claim is intended.

Run from this directory:

    python3 -B remove_redundant_truth.py

The script reconstructs the supplied 946-bit equations and checks its exact
recorded metrics and bit hash before deleting anything. It verifies literal
equality of every retained equation, signature and endpoint. The inherited
two structurally different parsers reconstruct the reduced packet exactly;
all 921 strict truncations and malformed/trailing-data checks pass. It also
checks 69,905 assignments in the powerset Boolean algebras with 0 through
4 atoms, treating q and r independently. Those bounded checks supplement
the all-algebra proof; they do not replace it.

Output: `packet921.bits`, `packet921.json`, `packet921.equations`, and
`truth_redundancy_verification.json`. The exact bit-character SHA-256,
excluding the file's terminating newline, is
`14757cd3b2ce4f92996f7ef3819c9b109b14b41144b5ff77ce178d6786c6a89f`.

## Charged machine boundary

An independent review has also accepted the ordinary proof and matched the
literal Sh1 axiom against the primary paper's Theorem 2. Its independent
codec imports none of the producer scripts:
`../encoding/review_packet921.py`, with receipt
`../encoding/packet921_independent_review.json`. It reconstructs both packet
hashes and locates the sole deletion at the zero-based bit interval
`[112,137)`. It verifies unchanged retained syntax, signature and endpoints,
and rejects all 1,867 strict truncations across both packets. This is an
ordinary independent mathematical and executable review, not a
proof-assistant certificate or an exhaustive prior-art search.

The input length includes the operation count, every operation's arity,
variable capacity, all equation trees and markers, and both ground
endpoints. It excludes no helper equation or signature declaration.
However, there is no binary TM compiler for this packet in this work:
the parser, substitution/inference engine, equality handling, fair search,
tape workspace, and blank-tape initializer all remain separately charged
obligations. Thus the total alternate-machine cost is currently unknown,
not 921 bits converted to states, and no part of the saving is subtracted
from the separate 238/239-state machine construction.

For comparison, ProveIt's older complete ground-equational generator was
measured at 299 working states before its ZFC-specific query and writer.
That is a different backend, not a cost claim for the new packet. Its
existence reinforces why payload length alone is insufficient.
