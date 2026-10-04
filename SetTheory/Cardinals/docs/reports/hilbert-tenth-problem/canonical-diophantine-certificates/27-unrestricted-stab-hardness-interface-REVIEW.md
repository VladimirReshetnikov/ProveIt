# Finite global stabilization: exact physical-interface hardness audit

Date: 2026-10-04. Read-only source/interface analysis. No upstream code, Lean, schedules, external communications, dense tile materialization, or raw-program compiler was executed or produced.

## Verdict and dependency hierarchy

**The exact eight-field physical language is r.e.-complete at the computable many-one level, upon adjoining the pinned Report35 loader theorem and its explicitly inherited fixed-U15 universality dependency.** Its patch alphabet 0–15, stable background alphabet 0–5, and nonnegative patch box cause no interface obstruction. Indeed the reduction uses binary patches and one fixed background with heights in {0,4,5}.

Keep three propositions separate:

1. The newly submitted polynomial's claimed equivalence to unrestricted finite global stabilization is a theorem about its raw physical input. It needs no Turing-machine simulation, Cairns reduction, or U15 universality theorem. This review does not replace that theorem's mathematical/source audit.
2. Recursive enumerability of the physical language has the direct finite verifier in §5 below, independently of the polynomial or any simulation.
3. Hardness additionally uses the immutable Report35 physical loader theorem and its inherited universal-machine theorem, then the original normalization in §4. The particular Report35 tile is fixed. Its arbitrary-program-to-U15 tape compiler remains an imported mathematical dependency, not an implemented or arithmetically charged construction here.

Cairns' §§5–6 provide the relevant published global-halting reduction, but their literal wording contains defects detailed in CORRECTIONS.md. In particular, the defective §5.1 definition is not sufficient for the claimed equivalence. A corrected qualitative reading also supports a fixed-universal-machine construction with some fixed tile; it must not be advertised as a verbatim implementation of the printed definition, or identified with Report35's particular tile without the latter dependency.

## 1. Exact event and input

Let G be the set of positive ordinary inputs whose right-associated seven Cantor pairings decode

    (p−1, q−1, r−1, T, d−1, e−1, f−1, D)

with p,q,r,d,e,f positive, T a base-32 tile of pqr declared digits in 0–5, and D a base-32 patch of def declared digits in 0–15. Nonzero higher digits are forbidden; leading zero slots are allowed. The initial configuration is the periodic tile plus D on [0,d)×[0,e)×[0,f).

Membership means existence of a finite legal threshold-six toppling sequence ending globally stable. Repetitions and the empty sequence are allowed. No target is an input field or part of the event.

The finite-total event is essential. The reduction's nonhalting runs have infinitely many distinct one-shot sites, although every site fires at most once. Local finiteness of the odometer cannot replace finite total mass. Neither an alarm's first firing nor infinite recurrence at one site is used.

## 2. Exact imported loader contract

The immutable files checked are the Report35 loader and composition copies in Report50's science/sources directory. Their hashes match source-pins.json; exact identities are in SOURCE_PINS.json.

The loader's §§1,2,4,5,6 provide the following contract, without a new construction here:

- One stable periodic b:Z³→{0,4,5}, with periods (1303671936,744955392,1955501604)
- A computable finite seed δ(ell,right):Z³→{0,1}; ell and right are nearest-head-first finite binary halves, with blank 0 under the state-A head
- U15 halts on those halves if and only if the sandpile has finite total toppling activity
- Every physical site is one-shot under every legal schedule; sites outside hardware support never topple
- The arbitrary-program/input to finite-U15-tape universality reduction is inherited, not implemented in the loader or in this review

The initializer is particularly explicit. For n=|ell|+|right|, put

    L=min(−3,−|ell|−1), R=max(3,|right|+1).

There is one selected active state for each cell x∈[L,R]: two boundary fronts, the initial head at 0, and the intervening tape symbols. The loader adds one chip at the distinct height-five root

    (B x + 24 + 48 s_x, 24, 0), B=186238848.

There are at most n+7 seeds. It does not perform a separate infinite blank-tape initialization. No negative seed, chip removal, initially unstable periodic site, or unbounded chip stack is present.

The composition file §9 explicitly reuses this same finite-total event. Its finite-prism certificate and its external union over prisms are not themselves the new fixed-arity polynomial. They corroborate the loader contract and do not replace the separate unrestricted-certificate proof.

## 3. Why halting leaves only finitely many total topplings

This section spells out the inference from the pinned loader's CA and physical-composition invariants, rather than treating finite CA output as automatically sufficient.

Before a halt at machine time T and position a, the fronts are at L−t and R+t. The head cannot catch them. Thus every finite row has finite support, and the first T+1 rows contain only finitely many active cells.

After the final head appears, indecision spreads at speed two. Define

    D_left = a−L+T, D_right = R+T−a.

The first all-lazy row is

    H = T + max(D_left,D_right) = 2T + max(a−L,R−a).

For example, at k steps after the halt the left indecision boundary is a−2k, while the still-moving left front would be L−T−k. They meet when k=D_left. The right calculation gives D_right. Once a front is lost it cannot regenerate: all relevant rules have positive-state inputs, and the all-lazy configuration is absorbing. There are only finitely many active spacetime cells, even including the blank fronts before they disappear.

Partial gate activity needs an additional argument. Let A be the finite set of active CA state roots. A temporal physical wire is a branch of a state root, and the receiving input diode blocks backward activation into that temporal signal. Hence temporal activity starts from A and can enter only the next row, within two cell positions of its source. Within any such destination cell, AND chains may partly activate even if no output state is produced. This can activate only finitely many sites: a cell's circuit and each routed edge are finite. No further temporal signal is generated without an actual new state root, which would already belong to A. Initial row-zero roots may also activate parts of their own producer circuits backward; these remain in finitely many finite cells. Negative-time roots have no seeds and cannot appear in the least closure.

Consequently all physical activity lies in finitely many finite circuit cells and connecting wires. The loader's global confinement/one-shot invariant prevents residual leaked chips from starting an independent exterior avalanche: a zero-background site has at most two support neighbors, and cannot reach threshold six. No infinitely long initialization wire or alarm network is included.

Thus a halting machine yields finitely many *total* topplings, not merely finitely many completed gates or bounded per-site counts. Conversely, a nonhalting machine activates a different headed state root on each time row, producing infinitely many distinct physical topplings. This establishes the required event equivalence, subject to the imported loader contract.

To match the raw language's existential formulation, observe that a finite complete legal execution ends globally stable. Conversely, if a finite legal sequence has stable endpoint and count u, no legal prefix can exceed u: at the first attempted excess at v its height is at most the stable endpoint height there. Therefore every legal prefix has length at most sum u. An infinite legal complete execution is impossible. Existence of a finite legal global stabilization and finite total complete legal activity are the same property here.

## 4. Original normalization into the raw eight fields

The following proof is independent of the detailed hardware implementation. Its only inputs are a stable periodic background b with positive periods P1,P2,P3 and a computably given finite seed δ with values in {0,1}.

Let S=supp(δ). For each coordinate i, let mi=min({0}∪{v_i:v∈S}) and choose

    s_i = P_i · ceil(−mi/P_i).

The integers s_i are nonnegative multiples of their periods. Define δ'(w)=δ(w−s). All its support coordinates are nonnegative. Periodicity gives

    b(w−s)=b(w),
    b(w)+δ'(w)=(b+δ)(w−s).

Translation by s is a lattice graph automorphism. It takes any finite legal sequence for b+δ to a finite legal sequence of the same length for b+δ', and takes stable endpoints to stable endpoints. The inverse translation proves the converse. There is no target coordinate to transform.

For i=1,2,3 set

    a_i = 1 + max({0}∪{w_i:w∈supp(δ')}).

Use d=a1, e=a2, f=a3, and p=P1,q=P2,r=P3. These are positive and the translated seed fits in the declared patch box. Form

    T = Σ b(x,y,z)·32^(x+p y+pq z),
        0≤x<p, 0≤y<q, 0≤z<r,

    D = Σ δ'(x,y,z)·32^(x+d y+de z),
        0≤x<d, 0≤y<e, 0≤z<f.

These are finite natural integers with no higher nonzero slots. T's digits are in {0,4,5}⊆{0,…,5}, and D's digits are in {0,1}⊆{0,…,15}. Empty positions and any declared leading slots are zero.

Finally let π(a,b)=(a+b)(a+b+1)/2+b and serialize

    InputPlus = 1 + π(p−1, π(q−1, π(r−1, π(T,
                    π(d−1, π(e−1, π(f−1,D))))))).

This is the exact eight-field, positive-input convention. Every step is a terminating integer computation. In particular, period-multiple translation leaves p,q,r,T unchanged; it does not replace the fixed background by an input-dependent phase. Only the finite patch descriptors change.

Although the fixed tile is enormous, a finite bounded coefficient evaluator determines every entry. Enumerating its finite fundamental box and serializing it is a computable operation. That observation does not claim this enumeration was performed, is practical, or has been paid for in the polynomial's arithmetic ledger. One may equivalently hardcode the resulting finite integer T in a computable-reduction existence proof.

Applying this normalization after the imported U15 tape compiler gives a total computable many-one map F satisfying

    machine M halts on input x  iff  F(M,x)∈G.

The reduction lands in the sublanguage with one fixed (p,q,r,T) and binary patch digits. Therefore both that fixed-background sublanguage and the full varying-background G are r.e.-hard. Allowing arbitrary physical firing repetitions in G does not break the reduction: its range is a one-shot subclass whose finite-global-stabilization event is unchanged.

## 5. Original semidecision procedure for the exact language

The domain is decidable. Invert the seven Cantor pairings; recover positive dimensions by adding one; inspect the finitely many declared radix slots and the higher-digit quotients. Reject any malformed code. This needs no simulation.

For a valid code, enumerate every finite sequence of signed lattice coordinates, for instance by increasing a bound on its length and all coordinate magnitudes. Include the empty sequence. A candidate is checked step by step using its finite count dictionary m and

    current(v)=b(v)+δ(v)−6m(v)+Σ_(w∼v)m(w).

Require current(v)≥6 before each proposed toppling, then update m. Afterwards let E be the finite union of the patch box, the toppled sites, and their six-neighbor sets. Compute the final height at every site of E and require it to be at most five. Outside E no patch or toppling contribution is present, so the height is the known stable b. Hence this is a decidable test of global stability, not an infinite search over exterior sites.

Accept if any candidate passes. Every finite global stabilization eventually appears, and every accepted candidate is one. Thus G is recursively enumerable. The same verifier works after restricting (p,q,r,T) to the fixed loader tile. Together with §4, this gives r.e.-completeness under computable many-one reductions.

The source calls its *infinite-total* decision question global halting prediction. Its yes/no orientation should not be copied into this result: the **finite-total** raw language is r.e.-complete; its infinite-total counterpart on valid physical codes is co-r.e.-complete.

## 6. Limits on use

- The unconditional raw polynomial equivalence, if independently verified, must be stated before adding the separate hardness dependencies
- No new primary-source theorem, author-issued erratum, literal raw-program compiler, arithmetic compiler cost, numerical dense tile, article, or resource ledger is supplied here
- Report35's inherited ordinary-program-to-U15 interface is retained as a named dependency; this review did not independently reconstruct its universality proof or compiler
- This check read and hash-verified the pinned Report35 proofs; it did not re-run or independently redo all underlying routing and primitive audits
- The corrected qualitative Cairns route gives a theorem-level reduction, not a literal unmodified transcription of the defective printed definitions
- No alarm subsystem, target field, first-firing event, or local-recurrence event may be substituted
- The finite code's initial heights remain ≤20 in general, and ≤6 on the reduction's instances; intermediate multiplicities for arbitrary members of G remain unrestricted

For a short user-facing source summary/corollary use POTENTIAL_COROLLARY.md. It has fewer than 200 words and no verbatim quotation. Original normalization and semidecidability arguments are separated above.
