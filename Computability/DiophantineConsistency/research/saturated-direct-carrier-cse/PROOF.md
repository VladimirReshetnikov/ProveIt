# Exact direct-carrier sharing across the saturated family

This is a polynomial identity and literal operation-count improvement.
No positive parameterization or arithmetic/native theorem is changed.
All five complete parents are frozen; this packet supplies separate graphs.

## 1. One private multiplication is redundant

Every actual direct parent contains

    qbJ=q*bJ, q4=q3*q, P1=q4*bJ,

where bJ=q-1 and q3=q³ have already been computed. The qbJ register
is independently live in lowY=qbJ*Y. Inspection of EVERY actual parent
row shows that q4 has exactly one consumer, namely P1. Replace only
P1=q4*bJ by P1=q3*qbJ and delete q4. The identity

    (q3*q)*bJ=q3*(q*bJ)

holds over the free coefficient/input polynomial ring, without any sign,
Pell equation, divisibility, fixed-port value or source interpretation.
Each later row therefore has exactly its former value by induction on
the unchanged binary source order. In particular the entire output
polynomial, not merely its positive zero existence, is unchanged.

Every deleted coordinate is uniquely reconstructed by q4=q3*q. Every
remaining gate, input and fixed port is live. The sole deleted gate is
one paid multiplication; no constant, interpreter, division, auxiliary
quantifier or unprinted operation is introduced.

## 2. Complete source and native boundaries

The exact routes are

| Whole frozen parent | Old operations | New operations | Exact degree |
| --- | ---: | ---: | ---: |
| saturated direct upper |98|97|258|
| saturated direct sharp |99|98|254|
| reused-b direct upper |97|96|258|
| reused-b direct sharp |98|97|254|
| uncentered reused-b direct |95|94|262|

CUTS.json includes every original row index, its new index, the sole
changed consumer, the sole deleted definition and every q4 consumer.
The independent checker compares each entire new graph and all metadata
to the exact permitted change from its authenticated complete parent.
All ten strictly positive independent inputs and the four fixed ports
are preserved. Thus each parent's full ordinary source/refutation theorem
transfers by the identity on every independent positive tuple. There is
no new completeness witness map, calibration obligation or chronology.

Each primary graph retains the WHOLE compact44 BFS coefficient tuple.
The separately retained INDEXED_BINDING and all four indexed payloads
give the SAME whole second native instance licensed by the parent theorem.
These distinct tuples are not identified or mixed. The free-port identity
in Section1 applies to either entire instance, and indeed to every
substitution at the four named ports.

## 3. Global degrees and entire leading forms are preserved

Pointwise polynomial equality in the free ring transfers the complete
global upper-bound and attained-leading-form proofs of the sealed
parents. It does not infer a global degree from sample evaluations.
Write q0=beta*J, X0=q0+x and k0=eta+zeta. The complete highest forms
for BOTH upper routes are

    2^11*q0^124*X0^29*Y^61*i^10*k0^32*(q0-F)²,

for BOTH sharp routes

    2^10*q0^122*X0^28*Y^60*i^10*k0^32*(q0-F)²,

and for the uncentered route

    -2^10*q0^126*X0^30*Y^62*i^10*k0^32*(q0-F)².

Their degrees are258,254,262. Selecting respectively the highest x
power, eta^32 and F² gives nonzero coefficients
2^11*beta^124,2^10*beta^122,-2^10*beta^126 at either actual tuple.
The checker binds the actual parent degree/whole-graph records and these
complete forms, and runs a supplemental exact full univariate expansion
of each new literal graph. No parent or incoming checker is imported.

## 4. Scope of the additional search

The checker also enumerates every two-gate associative +/* rewrite in
the frozen89/95 sources in which an intermediate is used exactly once,
as one operand of that parent, and a different pairing is already
computed before that parent.
It finds exactly the q4 contraction above in direct95 and none in zero89.
This is a closed, explicitly restricted search result. It is not a lower
bound for arbitrary arithmetic circuits, distributive transformations,
other parameterizations or consistency encodings.

Several alternative evaluations of the two-root norm and carrier merely
exchange multiplications for additions at the same total binary cost.
They are not promoted as improvements. No page, frozen source, common
document or Lean file is changed by this packet.
