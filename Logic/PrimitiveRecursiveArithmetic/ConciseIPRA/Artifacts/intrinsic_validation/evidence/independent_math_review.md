# Independent review of proper_compareforce.py

Candidate reviewed: the frozen `code/checker.py` in this archive.
This is a paper-level operational audit, not a formalization.

## Result

No soundness defect was found in the specific candidate. Its mathematical
justification should be a successful-call-tree interpretation, not a claim
that every arbitrary JSON certificate can be coerced leafwise into an old
certificate with the identical execution trace.

## Successful-opening lemma

Assume inputs come from Python's ordinary JSON decoder. If an invocation of
`i(a,t,d)` returns normally, every recursively visited node of its source `a`
is a list, integer, or Boolean. Its returned value is also such a tree.

Proof: a list is selected by `a * 0 == []`, and every child is visited by the
list comprehension. If the public arity check rejects a list, the later
integer operation fails; it cannot succeed through the scalar branch.
For a scalar, the expression `(a | 0)` must be evaluated before the scope
comparison. It is defined on JSON integers and Booleans and undefined on
JSON floats, strings, null and objects. Objects/null in fact already fail
the multiplication. Retaining a scalar returns it or the integer 1.
Opening an exposed position recursively scans the image at root term depth,
and multiplication by the parity bit preserves the stated output class.
The default image is a function sentinel and cannot pass a successful scan.

This argument excludes actively scanned NaN, Infinity and nonintegral or
integral floats uniformly. No dense-real parameter interpretation is needed.

## Public syntax

At the initial floor zero, the existing arity/depth tests recognize the
actual-binding Eq/D grammar. The bitwise parity test rejects public False.
True is accepted exactly where integer code 1 is accepted, and denotes zero.
It cannot denote a protected slot, whose canonical positive codes are at
least 3. Thus the public grammar has an explicit extra spelling of zero.

Call this an exact-binding grammar with a zero alias. It is not literally
the predecessor's unique-spelling canonical grammar, although its binding
discipline and mathematical language are the same.

## Unvisited JSON fields

The opening lemma is deliberately about visited source nodes. A witness
image can remain unvisited when the template has no exposed numerical hole;
packet fields and an unused input prefix can contain arbitrary JSON.

This does not add mathematical premises. In a terminal computation case,
the raw computation candidate must equal `i(goal)`, a typed tree. Equality
with a typed scalar can admit a Boolean or a finite integral float alias,
but no nonintegral float, NaN, Infinity, string, object or null. Equality of
lists is componentwise, so the compared candidate has the same arithmetic
reading as the typed goal. Any term image actually used by opening is
scanned, hence satisfies the stronger lemma above.

In a matched equality-transport case, the major goal has been successfully
checked; its source tree is therefore typed. The raw pair `[s,u]` matching
that major forces its relevant leaves to be typed scalar aliases in the
same way. If a source or target image is used it is separately scanned.
If it is unused, its value is immaterial to that substitution. The closure
case uses the successfully scanned template and the same opening lemma.

A global float-to-int projection is not asserted: changing irrelevant
fields can change Python truthiness or a failed equality comparison. The
proof should extract the native inference of each successful branch directly.

## Packets need not all be lists

One minor raw-JSON corner case is worth recording. A four-key JSON object
can be unpacked as a packet. If its first key is the empty string, a terminal
retained-hypothesis case can succeed without using its other keys. It carries
no mathematical inference beyond the retained hypothesis. Such a packet
cannot produce a new computation theorem because its string fields cannot
equal the typed goal, and a nonterminal continuation fails when it scans
the string template. Thus a proof must not assert that every consumed
packet is necessarily a list.

## Changed child increment

The change from `2*(j == 2)` to `j & 2` agrees at every meaningful numerical
constructor: a successor has only child 0, and an iterator has children
0,1,2. Formula-position increments are unchanged. Differences at positions
3,6,7,... occur only inside malformed numerical arrays; their raw numerical
reading is zero and all children are annotations. The transformation can
alter whether such annotations are accepted, but cannot change the reading
of a successful expression. Prove semantic preservation, not execution-trace
equivalence on all arbitrary auxiliary inputs.

For completeness, a stronger execution invariant is needed because annotation
children are visited eagerly. Let N be integer/list trees whose arrays have
arity at most three. Native terms, formulas, templates, witnesses, and
numerical substitution images in the canonical construction lie in N.
Opening a source in N with an image in N returns another member of N.

The only larger expression arrays are `m * 3` for an equality major or a Q
major, of arities six and nine. These wrappers are opened at formula depth
zero, where the old and new transitions agree. Their descendants lie in N.
The wrappers are retained as auxiliary context entries and are not used as
numerical substitution images or native major formulas. Four-field packets
are not opened; only slices of length two or three are used.

Consequently every array visited at odd depth in the canonical construction
has arity at most three. The child increments agree at every visited child,
including eagerly traversed annotations. Induction over the opener calls
gives identical executions and results on this canonical class. This carries
the predecessor's canonical completeness construction across unchanged. It
does not claim acceptance equivalence for every arbitrary predecessor input.

## Freshness

The floor remains an integer and decreases strictly on every entered call.
A closed expression scanned before that decrease uses only rigid labels in
the old interval `[floor,0)`. The newly allocated integer below the interval
is fresh for it. Actively scanned real labels are impossible by the opening
lemma. Terminal matching to a typed goal cannot manufacture the newly
allocated negative label in the old goal. Thus the predecessor's call-tree
freshness argument applies with the same parameter meaning.

## Scope of the conclusion

These arguments support soundness and completeness of a new syntax/checker
for the existing native arithmetic calculus. They do not establish a new
axiom deletion or a source-code minimum over all possible presentations.
