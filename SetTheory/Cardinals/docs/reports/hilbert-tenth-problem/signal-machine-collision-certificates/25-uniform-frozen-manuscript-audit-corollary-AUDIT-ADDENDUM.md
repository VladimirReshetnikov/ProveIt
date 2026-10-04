# Report 51 moving frame corollary audit addendum

Date: 4 October 2026 UTC

## Verdict and scope

Mathematical PASS for the proposed credited corollary of Report 49. The original full manuscript audit remains unchanged at ../report51-manuscript-audit-20261004. This addendum reviews only the new original-frame non-Presburger example, its direct stationary-frame comparison, the corresponding revision to the remaining question, and the final changed manuscript/PDF bytes. The final 21-page draft passes complete diff review and all-page visual inspection; exact final pins and rendering observations are recorded in FINAL-VERIFICATION.json.

The corollary supplies a concrete obstruction. It does not classify all original-frame untimed relations, alter the conditional hypotheses of the uniform chart theorem, imply undecidability, or invalidate the natural-single-fold timed quartic. The explicit example remains decidable and has a simple quadratic parametrization.

## Imported Report 49 result

Read the literal six-row specification, full-shift reversibility conclusion, complete phase formulas, and epoch timing proof in the approved Report 49 manuscript:

- Source: /workspace/shared/reversible-clock-report49-release-20261004/manuscript/report49.tex
- Source SHA-256: c78133175cca8be54cbf230af1423b77b0ee3bcf6d71bd816f6478800ccf9056
- PDF SHA-256: 3e9aecc5f93634f0cf5a458e99c944afa1fc21d223505f3d252bdc4d6f2150fa

This is a read-only import of an approved result. No Report 49 checker or CA implementation was executed for the addendum.

Rename Report 49's rule G. It is binary, globally reversible, finite number-conserving, and radius at most 90. Each endpoint in its six-row specification has at least two particles, so a configuration consisting of one particle admits no raw key and is fixed. Thus G already has stationary isolated units.

For D>=13 put C_D={0,5,6,D} and L_D=2D-22. Report 49 gives every integer time of a cycle, with disjoint adjacent ranges:

- Right phase: G^s(C_D)={0,5+s,6+s,D}, 0<=s<=D-11
- Left phase: G^s(C_D)={0,2D-18-s,2D-14-s,D+1}, D-10<=s<=2D-23
- Endpoint: G^(L_D)(C_D)=C_(D+1)

Starting from C_13, cycle k therefore has D=13+k and start time T_k=k^2+3k. Every positive coordinate in both phases is at least five, and the final marker is strictly right of the moving pair. Hence all displayed tuples are already strictly sorted, and their minimum is exactly zero at every time, including contacts and epoch boundaries.

## Shifted rule and its model properties

Define F=tau_1 composed with G. Translation equivariance gives F^t=tau_t composed with G^t. Both F and its inverse are CAs of radius at most 91, since F^(-1)=G^(-1) composed with tau_(-1). They are full-shift inverses; composition preserves quiescence and finite number conservation. F moves an isolated unit by +1, so its stationary frame is exactly G.

This step uses an ordinary spatial translation of a fixed rule. It introduces no time-dependent rule, extra label, extra particle, external clock, or nonlocal operation.

## Exact affine slice and projection

Let R_F be the set of strictly sorted complete occupied-coordinate tuples reached from the one fixed input C_13 at some nonnegative integer time. Intersect R_F with the affine slice

y_2-y_1=5, y_3-y_1=6.

For the right phase at time t=T_k+s, the first three shifted coordinates are (t,t+5+s,t+6+s). The two equalities hold exactly when s=0. In every left phase the two interior particles have separation four, whereas the slice requires their separation to be one. No left phase passes. Sorted order ensures these references cannot accidentally identify a marker instead of the moving pair.

Thus the sliced relation is exactly

{(T_k,T_k+5,T_k+6,T_k+13+k): k in N}.

Its projection onto y_1 is exactly {k^2+3k:k in N}. The minimum-coordinate identity y_1=t is the indispensable bridge from an untimed spatial tuple to the clock time; an anchored hit set alone would not establish this conclusion for an arbitrary CA.

The projected set is infinite and its successive gaps are 2k+4, which tend to infinity. An infinite eventually periodic subset of N has bounded successive gaps, so this set is not eventually periodic and therefore not Presburger-definable. Presburger relations are closed under affine intersection and coordinate projection. Consequently R_F itself cannot be Presburger-definable, even though the input is fixed. Any stronger uniform original-frame Presburger relation would yield this fixed-input relation by substitution and is therefore impossible in general.

## Exact stationary-frame comparison

For G from C_13, forgetting time eliminates only phase timing. Every D=13+k with k>=0 occurs, and in the right phase p=5+s ranges through every integer from 5 to D-6. In the left phase put E=D+1; q=2D-18-s ranges through every integer from 5 to D-8=E-9. Hence the stationary-frame untimed complete relation is exactly the union

{(0,p,p+1,D): D>=13, 5<=p<=D-6}

and

{(0,q,q+4,E): E>=14, 5<=q<=E-9}.

These are integer points of two explicitly affine sets. The two pieces are disjoint because the interior-particle separations are one and four. The smallest case D=13 gives right p=5,6,7 and left q=5, so both boundary regimes agree with the source. This comparison is direct from the approved orbit and does not need the conditional uniform theorem to establish this particular stationary-frame relation.

## Sharp binary particle threshold

Report 49 Theorem 6.1 states that, for each fixed finite input of at most three particles in any binary quiescent number-conserving CA, the complete timed relation between time and occupied output coordinates is Presburger-definable in the original frame. Existentially quantifying the natural time variable therefore gives Presburger-definable untimed complete reachability for that input. Reversibility is not required for this lower bound. The shifted clock above supplies a globally reversible four-particle counterexample. Thus four is the least particle number for failure of fixed-input original-frame untimed complete reachability in the binary class, and remains least when global reversibility is imposed.

This deduction is the direct projection of an explicitly identified inherited theorem; it adds no new lower-bound premise. A weighted formulation could also use source 16, but must retain positive nonvacuum weights and at most one weight-one symbol, and should not be attributed to Report 49's deliberately binary specialization. No claim for several weight-one types follows.

## Fresh bounded checks

The independent checker in this addendum derives states only from the displayed phase formulas. It does not run or reproduce the CA rule. It verifies:

- 1,001 complete cycles from C_13
- 1,005,004 individual complete-time states, including contact states
- Exactly 1,001 selected section states under the affine slice
- Exact coverage of both stationary-frame affine parameter intervals for every tested cycle
- 20 boundary checks for cycle indices through 10^100

The proof above, rather than the finite computation, establishes the unrestricted obstruction. No unrelated earlier arithmetic fixture was rerun, and the original audit packet remains byte-preserved.

## Integrated manuscript verification

Reviewed the exact draft5 addition as Proposition 8.1, its complete proof, explicit stationary-frame affine union, binary sharpness paragraph, fixed-input/uniform and forward/absolute-coordinate qualifications, abstract/scope amendments, revised remaining question, fresh-check paragraph, source appendix, and Report 49 bibliography entry. The rest of the mathematical construction and copied-input quartic are unchanged from the original reviewed TeX. The inserted Report 49 source is byte-identical to the approved original. No new mathematical corrections are required.

All 21 final PDF pages were independently rendered at 100 dpi and visually inspected. Equations, table, new proposition, bibliography, page numbers, and margins are clean. No overfull/underfull boxes or undefined references occur in the final build log; only the expected disabled-shell-escape notice remains.
