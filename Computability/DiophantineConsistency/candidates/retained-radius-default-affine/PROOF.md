# Default-affine raw projection over the integers

This is a new projection of the **unchanged** frozen source
`candidates/retained-radius-comparison-base/guarded.json`, SHA256
`c30bee5671a654988f4ffa1eb5e5b43469b000292f4e78a85f5c062c0239494e`.
It has all1259 raw coordinates/all1177 original residuals and the same78
three-witness nonnegativity guards, hence1493 integer coordinates and1255
quadratic residuals. In particular raw694/base0.T is still guarded; the
bootstrap-guard exchange is not applied. Neither metadata nor row labels
are renamed or reordered.

## 1. Exact integer zero-set bijection

Let the full parent residuals be r_0,...,r_1254. At each of the880 steps,
the currently present pivot row is exactly v−f or its negative, where f is
an integral polynomial in other currently live coordinates. Its degree is
at most2. Replace v by f in **every** other current row, including every
nonnegativity guard. If a row becomes the zero polynomial, it can be
removed; all other substituted rows are retained. The exact certificate
checks that their degrees remain at most2. No parent coordinate is
removed as unconstrained.

For every integer zero of a current system the pivot gives v=f, so
restriction to the other coordinates satisfies precisely the substituted
system. Conversely, at any integer zero of that substituted system, set
v=f at those coordinates. This is an integer, satisfies the removed pivot,
and makes every original current residual equal to its substituted
residual. It is the unique possible v. Thus each step is an exact
integer-zero bijection. Applying these maps in order, and reversing the
880 integral recipes in the opposite order, proves the full bijection
between the literal1493 source and the stored613-coordinate child.
No natural-number sign, source interpretation or divisibility premise
is used in this argument. The restoration coefficients may be negative.

The entire retained-row map has375 rows. The checker collects the complete
pivot polynomial and every successive row substitution; it does not just
inspect a gate name or an approximate support bound. It checks the entire
375-row literal output and all613 retained metadata identities. All234
private guard coordinates remain among the retained coordinates. In
particular no guard is omitted because its sign is intended or because
it is absent from the original natural semantics.

## 2. Whole quartic equation

Write the complete child residuals as s_0,...,s_374. The new equation is

    P(x_0,...,x_612) = sum_{j=0}^{374} s_j(x)^2 = 0,   x in Z^613.

All coefficients of all375 quadratic residuals appear in `equation.json`.
The **entire** collected polynomial appears in `expanded_polynomial.json`.
For integers, P=0 if and only if every s_j=0, because each square is
nonnegative. Consequently the bijection in Section1 proves that this
quartic has a zero exactly when the unchanged literal1493 parent does.

The independent complete expansion has9661 nonzero monomials, exact
(nonzero) degree4, and maximum absolute coefficient2445790974704. Every
one of the613 variables occurs in that polynomial. The maximum absolute
quadratic-row coefficient is1122540. These are properties of the actual
stored coefficients, verified coefficient for coefficient. They are not
merely upper bounds obtained from the source graph.

## 3. Only after restoration inherit the source calibration

First reverse all880 signed deletions to obtain a full literal1493 zero,
including all raw coordinates and all78 guard triples. The copied
`source/BRIDGE901.json` then gives the exact integer bijection to the
literal901 source: its592 triangular affine integer restorations make592
defining rows zero and send the remaining1255−592=663 rows to the full
compact body and guard residuals. All78 triples are copied to their exact
slots. No sign condition or new witness precedes that literal901 zero.
The checker independently recollects the entire1255-row partition through
the pinned frozen source-bridge functions.

At that literal901 source, the previously accepted signed-B/main-root
ordinary argument applies. Its comparison-coordinate reconstruction is
**nonpointwise**: it keeps existing U,V and all78 guarded values, changes
q4 and its comparison witnesses, and restores all affected raw rows.
Only the resulting positive **new** q4 receives three fresh guard
witnesses to reach literal904. The original unguarded q4 is not claimed
nonnegative. Only after obtaining that literal904 zero does its accepted
pointwise21-sign theorem and63 fresh witnesses give the literal967 zero.
The copied `source/LIFT904.json`, the exact901 bridge and the downstream
967 bridge are pinned and checked. The ordinary discussion is preserved
verbatim in `source/PARENT_PROOF.md`.

Conversely, a literal904 zero forgets the q4 triple to give901; its unique
affine restoration gives1493, and Section1 then restricts it to this613
child. Thus this sibling inherits the same ordinary zero-existence
calibration as its frozen parent. The finite source binding is checked
before that inheritance. There is no attempt to apply a natural theorem
to an arbitrary signed child assignment before restoring the source.

## 4. What changed in the optimization

The producer applies the previously reviewed signed terminal optimizer
directly to the **exact frozen parent bytes** with `max_support=8`, default
`affine_support=None`, and `quadratic_first=False`. Accordingly the same
support cap8 is allowed for both affine and quadratic restoration recipes.
This differs from the parent's stored low-height family whose affine caps
are1 or2. It also differs from first contracting to901 and then optimizing.
The raw input's actual variable ordering is retained unchanged; there is
no specially relabeled or semantically altered source.

The accepted compact cap32 point has613 coordinates,375 rows,10013 terms,
degree4 and height2445790974704. This new raw/default-affine point has the
same coordinate/row counts, degree and height, with352 fewer terms (9661).
Their pointwise polynomials need not agree: they are different projections,
with zero equivalence through the common restored source. This is an
order/configuration improvement, **not** a consequence of exchanging a
guard, a proof of global minimality, or a reduction in unknowns.

## 5. Verification and boundary

The generator imports only the hash-authenticated optimizer member from
the pinned archive. Its normal and optimized rebuild modes reproduce all
whole generated bytes. The separate checker never imports that optimizer,
its verifier, a builder or a historical emitter. It implements its own
monic-pivot, complete-substitution, retained-row and full-SOS comparisons.
It also authenticates the complete parent inventories and source files,
and calls only pinned frozen literal-source identity functions after
restoring the full parent. Changed inverses, dropped guard rows, altered
surviving/whole coefficients, incorrect guard-witness slots and an illicit
old-q4 positivity premise are rejected.

Normal and optimized-Python checks retain all these checks. The proof is
ordinary unbounded algebra over the integers. No Lean formalization,
internal-ZFC proof or new native-calibration theorem is claimed. Accepted
parents, pages and common documentation are preserved.
