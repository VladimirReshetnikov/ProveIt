# One binary kernel certifies both control and selected histories

The complete fixed-table matrix compiler can share its controller subset
certificate with its eight selected-source tests. Its new literal count is

    7m+3h+p+223 = (3m+2h+102)M + (4m+h+p+121)A,

with **47 equations** and **m+67 strictly positive witnesses**. Here m=2^h
is the padded macro-table edge count and p is the paid selector-output
sum cost, exactly as in the [complete parent](group_complete_matrix_compiler.md).
The single sum-of-squares polynomial costs

    7m+3h+p+363 = (3m+2h+149)M + (4m+h+p+214)A,

and has exact degree **12m+112**. Relative to the parent, this saves
**50 certificate operations,89 polynomial operations,13 equations and20
positive witnesses**. The higher degree is recorded explicitly.

The represented ordinary-input relation is unchanged: for fixed positive
alpha,beta and fixed physical macro codes, the certificate accepts x>0
exactly when a macro word has product diag(L_r,L_r), where

    r=alpha*x+beta, L_r=[[1+r,1],[-r^2,1-r]].

The fixed universal subgroup theorem therefore still applies. No numerical
universal alphabet is instantiated, and this parameterized compiler does
not improve the separate numerical75/88 frontiers.

## 1. Joining the two existing bitwise predicates

Keep every history, geometry, controller-checksum, state-flow and
physical-port equation from the parent. Retain its supplied positive
q_geom,P,J,H_i,Shat_i,Zhat_i and all hatted controller edge variables.
Write the following as mathematical abbreviations for paid registers:

    B=8q_geom^2, D=q_geom^2,
    E_e=Ehat_e-1, S_i=Shat_i-1, Z_i=Zhat_i-1,
    K=1+P+...+P^(m-1),
    Hc=sum_e E_e P^e, Mc=J*K,
    Hb=sum_(i=0)^7 H_(floor(i/2) xor 1) P^i,
    Mb=(B-1)*sum_(i=0)^7 S_i P^i,
    Zb=sum_(i=0)^7 Z_i P^i.

The old source computes Hc,Mc and all three batch words already. Put
N=P^8 and form

    H=Hb+N*Hc, M=Mb+N*Mc, Z=Zb+N*Hc, T=P^(m+8).     (1)

Use the complete four-class binary AND certificate, with scale16T,
to assert

    0<=H,M<T, H AND M=Z, T a power of two.             (2)

This is an invocation of the proved scalar theorem from
[selector63](native_binary_masked_selection63.md), not an uncharged AND
operation. Its existing three positive fields F0,F1,F2 and native core
coordinates remain. Compute F3=16Z+8, and use the existing four-bit prefix
16H+12,16M+10. The source charges all of these operations.

Discard the controller's separate three-class subset kernel, including
its F0 and19 native auxiliaries. There is no identification of old Pell
witnesses across incompatible scales: the new four-class kernel is
constructed afresh in the positive converse below. Its scale16T remains
distinct from q_geom and the linked-geometry core.

## 2. Power typing before Boolean semantics

The full source still computes B=8q_geom^2 before using it. As all supplied
hats are positive, E_e,S_i,Z_i are nonnegative, even before any comparison
is assumed. Thus Hc,Mc,Hb,Mb,Zb and the three quantities in(1) are
nonnegative for every positive supplied tuple. In particular F3>=8, so
the entire native four-class positive domain is available immediately.
No controller digit theorem is used to justify this positivity.

At a positive zero, the retained linked-geometry47 component proves
q_geom=2^popcount(J), J>B and J odd independently of P. It therefore
types B as dyadic. The scalar AND projection independently makes
T=P^(m+8) a power of two. Since m+8 is a positive fixed integer and
P is positive, prime factorization makes P a power of two.

The retained controller equation (B-1)J+1=P then gives P=B^t and
J=1+B+...+B^(t-1). Together with J>B and the population equation, it
recovers exactly

    t>=2, q_geom=2^t, B=8*4^t, P=B^t.                 (3)

Every operation establishing T, B and the repunit remains in the actual
source. Neither runtime exponentiation nor a test for powers is free.

## 3. Bounds that exclude carries before selector typing

To extract the controller predicate from the upper region in(1), first
bound all three lower regions. An unproved assumption that Mb<P^8 would
make this argument circular, because its selectors have not yet been
typed. The already paid scalar checks supply exactly what is needed.

The history equation sum_i H_i+history_bound=P implies 0<H_i<P, so
0<Hb<N. The selected-output equation

    sum_i Zhat_i+selection_bound=P+1

implies sum_i Z_i<=P-8, hence 0<=Z_i<P and 0<=Zb<N.

The controller's hatted checksum gives

    sum_e E_e=J, 0<=E_e<=J<P.                         (4)

Its unchanged physical-port equations, interpreted only as scalar sums,
give S_i=sum_(label_e=i+1) E_e. Thus 0<=S_i<=J, before any Boolean
or adjacency conclusion. By the repunit identity,

    0<=(B-1)S_i<=(B-1)J=P-1.

Every coefficient in the displayed expression for Mb is therefore
between0 and P-1. Consequently

    0<=Mb<N, 0<=Hc<P^m, 0<Mc<P^m.                    (5)

These are purely algebraic consequences of positive hats and retained
scalar comparisons. They do not assume correct cell digits or a path.

Because N is a power of two, the proved bounds separate the binary
regions in(1). Relation(2) is now exactly the conjunction

    Hb AND Mb=Zb, Hc AND Mc=Hc.                       (6)

For contrast, without the low-mask bound, N=16,Hb=Zb=0,Hc=1,Mc=0,Mb=16
satisfies the joined AND even though Hc is not a subset of Mc. This
explicit carry contamination is why the port/checksum argument is part
of the proof, rather than a prospective optimization assumption.

## 4. Recovering the complete trace

The upper relation in(6) is precisely the old controller subset
predicate. From(4), each E_e is already a canonical base-P lane below P.
The mask Mc has ones exactly at the radix-B cell origins in each lane.
Hence every E_e is a Boolean length-t radix-B word. The paid margin
B>m then ensures that sum_e E_e=J has no cell carries and forces
exactly one selected edge at every position.

The retained ordered state-flow comparison and physical-port equations
now give the same hub-to-hub macro path and mutually exclusive Boolean
physical selectors as the [regular-controller proof](group_regular_macro_controller.md).
In particular, this proof uses chronological adjacency, not only edge
multiplicities. The lower relation in(6) recovers every selected source
digit Z_i from the canonical histories and these Boolean selectors.

All hypotheses of [canonical history47](group_four_register_canonical_history47.md)
are established. Its first-disagreement induction recovers the actual
shifted vector histories and both endpoints. The one-vector faithfulness
lemma then forces each final block to be L_r. This proves soundness for
the complete ordinary-input membership relation, with no remaining digit,
control, selection or geometry hypothesis.

## 5. Strictly positive completeness

Given an accepted macro word, pad its hub endpoint with identity steps
until t>=2 and B=8*4^t>m. Choose the true q_geom,P,J, shifted histories,
edge indicators and physical selectors exactly as in the parent's
positive converse. The old history and output-bound witnesses are
strictly positive. The linked-geometry theorem supplies its independent
positive native extension. The controller's radix margin B-m is positive.

The actual fields satisfy both relations(6), and all bounds(5). Hence
H,M<T and H AND M=Z. Apply the four-class truth-prefix construction at
the actual scale16T; all four classes are positive, including for wholly
unused letters or edges. It supplies F0,F1,F2 and every remaining positive
native coordinate. This is a single fresh AND extension: the parent
controller and selector kernel witnesses need not be preserved.

The new kernel and geometry auxiliaries are disjoint. Every other
comparison holds for the common genuine trace by the parent proofs.
Thus all supplied coordinates can be chosen strictly positive
simultaneously. This establishes equality of the accepted ordinary inputs;
it is not equality of the old and new polynomials at unchanged Pell
coordinates, nor a claimed bijection of their witness tuples.

## 6. Literal source changes, counts and exact degree

The [source](group_shared_typing_matrix_compiler.py) starts from the
actual complete parent DAG. It moves the controller prefix through its
Hc,Mc definitions before the selection block. It then removes exactly
the57 controller typing gates (30M+27A) and their13 comparisons. All
remaining controller equations are retained, including its checksum,
repunit, margin, chronological flow and eight physical ports.

The seven added instructions are

    Pm=(P^(m/2))^2, T=P^8*Pm,
    edge_shift=P^8*Hc, mask_shift=P^8*Mc,
    H=Hb+edge_shift, M=Mb+mask_shift, Z=Zb+edge_shift.

The preexisting controller power chain has P^(m/2), even when m=2.
The existing batch chain supplies P^8. These seven gates cost4M+3A;
the new source retains duplicate power gates when they coincide for
small m, so no free or implicit sharing enters the generic count.
Four existing registers are rewired: the paid scale and the three
padded data products. Their gate counts do not change.

Subtracting57 and adding7 gives the displayed50-operation saving.
Deleting F0 and19 native controller coordinates gives m+67 witnesses.
There are47 retained comparisons; their literal sum of squares adds
47M+93A=140 operations, giving the89-operation polynomial saving.
All fixed numeral products, squares and residual subtractions are paid.

For total degree, every supplied coordinate has degree one and all
compiler numerals have degree zero. The native index of the shared
kernel remains an independent positive supplied coordinate; its packing
equation is not substituted into the source when measuring degree.
The scale has highest form16P^(m+8). The unique highest residual is
the first norm of that kernel, with degree6m+56 and highest form

    w_selection^2*s_selection^4*k_selection^2
      *(16P^(m+8))^6.

All other residuals have smaller degree: direct DAG propagation bounds
the fixed geometry by14 and history by5, while the rewired packing
and padded-port equations remain below6m+56. Squaring the displayed
nonzero highest form proves exact polynomial degree12m+112. This is
larger than the parent's max(112,12m+16), so the operation saving has
a stated degree tradeoff.

## 7. Executable evidence

The [receipt](group_shared_typing_matrix_compiler.json) records four
complete source DAGs, comparison and witness lists, all added/removed
gates and exact ledgers. The checker compares every one of47 residuals
and the full SOS with independent formulas on1,024 supplied tuples,
including256 signed cases. Positive cases also check the newly computed
truth field is positive before any equation is imposed.

Weighted offset polynomial evaluations for m=2,4,8,16 verify the exact
highest degree and coefficient against actual-DAG degree bounds.
Another1,024 arbitrary non-Boolean edge decompositions verify the
algebraic low-mask bound, while1,024 typed concatenations verify both
bitwise projections and all four positive truth classes. The omitted-
bound counterexample is checked explicitly.

Four accepted-word fixtures also construct the common positive interfaces
for an actual target code, its inverse cancellation and hub padding.
They verify every shared outer comparison and the enlarged truth partition.
Both Pell cores deliberately retain placeholders in these fixtures;
their simultaneous positive extensions are provided by the proof above.

These finite checks support the source and interface identities. Full
positive core extensions and unbounded accepted traces are supplied by
the parametric arguments above, not inferred from these bounded samples.
Run the checker normally to compare the deterministic receipt; pass
`--write` to regenerate it.

An independent full proof/source/default review passed without findings.
It checked the pretyping bounds, separated bitwise projections, order of
power recovery, fresh positive converse, all47 comparisons and literal
ledgers. Additional checks compared512 arbitrary assignments, including128
signed cases, against the frozen parent and standalone AND64, verified4,096
bounded binary-split identities, and recovered weighted exact degrees and
highest coefficients at m=2,8,16. The reviewer also audited all four new
accepted-word fixtures and their explicit distinction from full Pell zeros.

A second independent full proof/source/default review passed without
findings. It additionally replayed the original prescribed scalar AND64
and the old controller's surviving comparisons on256 assignments,
including64 signed cases, matching every joined-kernel and retained
controller residual. Both reviews checked the positivity of the computed
truth field before invoking the native theorem. This packet is frozen.
