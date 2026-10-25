# Four integer charts after deleting redundant sign graphs

This packet concerns only the accepted default-support16 Round15 derived-shell
ancestry, with its residue-one reparameterization. It makes two variants and,
for each, an initial translated chart and the accepted finite centered chart.
No additional support policy is part of this packet. At this review checkpoint
no new compiler, checker or eliminator has been executed, and no projected
census is claimed.

Let S be the complete pinned source.json, with522 body coordinates and446
quadratic residuals. Let G be the complete pinned guarded.json, with all38
Legendre graphs. The source, guarded input, transform certificate, raw semantic
ports, original proof and accepted private reproduction are pinned separately.
In particular we retain the complete body tuple, frame, all paired predicates
and every power/seed/remainder port. We do not extract only the equations used
in the sign proofs.

For an integer u, the graph used here is

    u = a² + b² + c(c+1).

It has integer solutions exactly when u>=0. Necessity follows from c(c+1)>=0
for integer c. For sufficiency,4u+1 avoids the three-square obstruction and
has a representation by three squares. Exactly one square is odd modulo4;
write its root as2c+1 and the other roots as2a,2b. Subtract1 and divide4.
Thus every omitted nonnegative scalar can later receive a fresh triple. No
polynomial choice, uniqueness or preservation of that omitted triple is used.

The following equivalences are ordinary unbounded statements. The finite
coefficient verifier supplies exact bindings to each hypothesis; the signed
fixtures and corruption controls are diagnostics, not proofs of solvability.

## 1. Guard filtering at a complete fixed body tuple

F_only omits original guard2, the scalar F=coordinate3, at row448 with private
auxiliary coordinates528,529,530. It retains the A sign guard. Its applicable
ordinary theorem is the separately sealed factorial-output-guard packet.

joint_F_A omits guards2 and25. The second is scalar A=coordinate246, row471,
private auxiliaries597,598,599. Its applicable theorem is the separately sealed
signed-frame-orientation packet. This is the JOINT theorem: the F-only theorem
cannot first be invoked while its retained A premise is absent.

In either case every522 body coordinate and446 body row remains identical.
Delete exactly the indicated entire graphs and their triples. Relabel every
remaining auxiliary monotonically into the resulting consecutive coordinate
list; retain its original name and guard label. GUARD_MAP records all old/new
coordinate and row indices, all38 old graph specifications, the deleted
sublist and every remaining graph. There is no free old guard auxiliary hidden
in the body: every original triple is disjoint and occurs only in its graph.
The verifier rebuilds all38 graphs and checks all their occurrences before
checking the compacted source and every mapped remaining graph.

If G has a zero, forget the omitted triples and rename the rest. Conversely,
fix any zero of the compacted source. Undo the auxiliary renaming, so the full
body tuple and all retained graphs are available. The relevant ordinary
sign theorem proves F>=1 (F_only), or jointly F>=1 and A>=2 (joint_F_A).
Supply fresh Legendre triples for these restored signs. This gives a zero
of G at the same entire body tuple. Hence the sets of projected body tuples
are equal. This is not an integer bijection of all guarded tuples and does
not assert equality of their sum-of-squares polynomials.

The two closed ordinary manifests are part of SOURCE_PINS. Their entire
closed inventories, not only their manifest bytes, are authenticated. The
accepted442 reproduction provides the original G calibration; it is not
rerun as an unreviewed incoming program here.

## 2. Thirteen private slack rows after compaction

The original pruning certificate selects exactly the YminusK coordinates of
the13 doubled seeds. The undoubled t and K slacks remain in the source.
Transport every selected coordinate, row and restoration through the actual
guard compaction map. The verifier compares this entire transported list to
the original certificate, checks that each slack occurs in exactly its listed
row, and checks that row is ±(slack-restoration). Every restoration is an
integral polynomial in the retained body coordinates, with no self dependence.

Delete these13 rows, retaining all listed variables for now. The forward map
forgets their constraints; the inverse sets each private slack to its stated
restoration, independently of the other slacks. Since they have no other
occurrence and no retained sign graph, this is an existential equivalence over
all integers. Their signs are not premises. The values originally assigned to
these now free coordinates may later be overwritten in the inverse map.
Neither a new guard index nor a restoration is assumed from an uncompacted
certificate.

## 3. Signed Horn factorization with its full boundary

Apply the exact previously accepted factor_horn bytes to the newly pruned
source. Independently replay the full certificate on that input. Its17
square-difference coordinates are bound by name, each original defining row
and an affine root checked by full coefficient multiplication. The eleven-link
product chain is recovered from exact rows. The11 private factors used outside
the bundle are replaced by their signed affine roots, and their products are
reordered before a final square. A fresh Horn coordinate multiplies that square
by the unchanged bundle sum. Every external occurrence of the old terminal
Horn coordinate is redirected to this fresh exact expression.

The guard bundle is reconstructed explicitly. In old notation it contains
h_old=L², u_old=M², z_old=h_old*u_old and d_old=D², and its tested factor is
(z_old-d_old)². The new circuit uses h=LM, z=h²-D², and tests z². These are
identical polynomials in the external atoms. The two obsolete private defining
rows, for u_old and d_old, are deleted. The old coordinates remain listed until
the projection handles their actual lack of occurrences.

The verifier checks all18 exact edits, both deletions, the one fresh coordinate
and row, and the complete output equation. It verifies that the signed Horn
factors and guard-internal coordinates have no occurrence outside the permitted
private rows. Therefore arbitrary values of those internal gates are never
exported as semantic data.

Given an old zero, rebuild all changed private gates and the new root from
the unchanged external atoms. The boundary polynomial and every external row
retain their values. Conversely, given a new zero, rebuild the old private
squares, products and two obsolete gates from those same atoms. The same
boundary identity restores every external row. Old and new terminal coordinate
values need not be identified with each other; their respective exported Horn
values agree. This establishes both existential directions without taking a
square root of an arbitrary witness or requiring a sign on any affine factor.

## 4. Monic integer projection and all free coordinates

The pinned reviewed optimizer is used only with max_support16, affine_support
None and quadratic_first false. Its heuristic selects a certificate; soundness
does not depend on that heuristic or on a claim of optimality.

At each step the CURRENT designated row is exactly ±(z-Q), where Q has integer
coefficients, degree at most2 and no z. Substitute Q in every other current row
and remove that designated row. The verifier checks every coefficient, every
remaining degree bound, every dependency and every row that becomes identically
zero. Thus forward projection sends a zero to a zero. In the reverse order,
set z=Q using the already restored coordinates. The deleted equation then
holds and substitution proves all prior rows. This is an integral, unique
restoration for the eliminated coordinates conditional on values of coordinates
that have not been eliminated.

The certificate separately partitions the remaining original coordinates into
the actual used retained list and unconstrained_removed. Only coordinates with
no occurrence after all substitutions may be put in the latter list. Set each
of them to0 before reversing the monic stack. Their values are not unique, and
no count or list is inherited from the old442 result. In the later inverse
steps from sections2 and3, overwrite the private slack/obsolete coordinates
with their original definitions when necessary; their lack of occurrences at
the projected boundary makes this legitimate.

The checker verifies the entire variable and row maps, schemas, step metadata,
policy fields, all engine statistics, the exact projected equation metadata
and the engine's verification record. It also reconstructs all original
factored residuals for two signed retained vectors. Surviving residuals equal
the corresponding projected residuals and every deleted residual equals0,
without assuming those retained vectors are solutions. This fixture check is
supplemental to the universal symbolic certificate replay.

## 5. Both translations and the full quartic

The initial plain chart uses exactly the accepted name-based translation:
shift crt.encoded* coordinates, M0 and names ending minus1 by−1, and t0 by−16.
The convention is old=new+shift. The compiler obtains the16 from the actual
pinned t exponent; the verifier checks the exact complete translation list.
Every row is substituted literally. The inverse is new=old−shift, so this is
a bijection of all integer coordinate tuples.

The centered chart uses the exact accepted center_integer bytes on the plain
chart. It performs at most8 finite coordinate-descent passes, with the stated
finite increment list and the same tie break. This is a deterministic finite
search, with no assertion of global optimality. Its certificate records the
composed shift from the unshifted projected parent. The checker replays every
history increment, verifies its actual whole-quartic score and strict
improvement, the history ordering and excluded guard coordinates, the composed
shift list, original parent translation and full printed search transcript.
The pure deterministic rebuild additionally repeats the exact search policy.

For each of the four charts, independently square every actual quadratic
residual and collect every integer coefficient of their sum. Compare the
complete sparse polynomial, including header/domain/coordinate census; compute
its degree, monomial count, coefficient height and row height. Check every
row's forward translation and inverse translation coefficient identity. All
listed projected/final coordinates must occur. These identities hold for all
integer tuples, not just the signed fixtures or a univariate specialization.

A real sum of finitely many squares is zero exactly when every residual is
zero. In particular this applies over the integers. Combining this fact with
sections1–5 gives both soundness and completeness for each full quartic,
relative to the accepted native source calibration. Every canonical witness
of the original source maps forward by forgetting omitted private triples,
rebuilding private factored gates, projection and translation. Every new zero
maps backward by inverse translation, complete monic restoration, old private
Horn/slack reconstruction, the appropriate ordinary sign theorem and fresh
omitted triples. No source coordinate or semantic port is discarded silently.
