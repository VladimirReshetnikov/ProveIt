# Horizon-free binary target-firing certificate

Research source, 4 October 2026. This extension is not yet independently audited. It builds on the independently accepted POWER, Sub, AND, SPREAD, physical decoding, and padded-prism lemmas of Report 50. It does **not** use the stabilizing-supersolution lemma, require stability at the endpoint, or require global stabilization.

## Exact intended relation

The input is one positive integer InputPlus. Decode InputPlus−1 by ten right-associated Cantor pairings into eleven natural fields

(p−1,q−1,r−1,T,d−1,e−1,f−1,D,ζx,ζy,ζz).

The tile and patch retain the Report 50 interface: positive physical dimensions, base-32 tile digits 0–5, patch digits 0–15, and no nonzero digits outside their declared arrays. The target coordinate represented by ζ=2h+s, h≥0 and s∈{0,1}, is h−2sh−s. Thus 0,1,2,3,… represent 0,−1,1,−2,… .

The predicate is existence of a finite legal toppling prefix that fires the supplied target and topples every lattice site at most once. It is not ordinary unrestricted target firing. On a separately established all-site-one-shot loader it agrees with target firing, even if evolution continues forever after the target fires. Identification with a particular loader and the raw-program-to-physical-code compiler remain separate inherited obligations.

## 1. Paid physical geometry

Use the same centered prism and exact physical tensors as the audited construction. Its dimensions A,B,C are even, its lower corner is (−a,−c_y,−c_z), and A=2a, B=2c_y, C=2c_z. Put b=32, X=b^A, Y=X^B, Q=Y^C. Let η̂=H+Δ be its correctly decoded initial-height stream, with digits 0–20. Let I be the strict-interior low-bit mask, whose complete formula is

I=bXY Jx Jy Jz,
b²((b−1)Jx+1)=X,
X²((X−1)Jy+1)=Y,
Y²((Y−1)Jz+1)=Q.

All periodic repetition, patch translation and reshaping are expanded by the already proved scalar POWER, geometric, SPREAD and Sub/AND equations. The six zero faces below restrict only which sites the certificate topples. Exterior stability is not a clause and is not used for correctness.

## 2. One integer equation certifies the whole binary prefix

Choose a positive integer K, and use POWER to obtain W=Q^K. Introduce natural R with (Q−1)R+1=W. Thus R=Σ_{t<K}Q^t. Introduce natural streams Apre,E,V and require

Sub(IR,Apre), Sub(IR,E), Sub(I,V),
Q(Apre+E)=Apre+WV.

Every coefficient of Apre and E is 0 or 1; they occupy only K spatial frames. V is binary in one spatial frame. Both sides of the recurrence have base-32 digits at most two, so no carries occur. Reading the equation frame by frame gives

Apre_0=0,
Apre_{t+1}=Apre_t+E_t for 0≤t<K−1,
V=Apre_{K−1}+E_{K−1}.

Because every Apre_t and V is binary, the new bits E_t never overlap any earlier bit. Every site topples at most once, and V is exactly the total fired set. Empty layers are permitted and harmless. K is existential, with no supplied or fixed finite horizon.

## 3. Exact neighbor streams cannot wrap through time

Introduce natural ax,ay,az with b ax=Apre, X ay=Apre, Y az=Apre. Every frame is zero on all six spatial faces. Therefore bApre, XApre, YApre, ax, ay, az are exactly the six physical neighbor-count streams, in every frame. The x-face zeros remove row wrap; the y-face zeros remove plane wrap; the z-face zeros remove frame wrap. They also prevent overflow above frame K−1. No interaction between distinct time frames is introduced.

Define

Cval=η̂R+bApre+XApre+YApre+ax+ay+az.

Every digit lies in 0–26. The factors η̂R have a unique frame decomposition and cause no collisions or carries.

## 4. Fully paid selected-site legality

The integer 31E has exactly five one-bits in every newly firing slot and zero elsewhere. Use the explicit three-Sub AND relation to set

Fsel=Cval AND (31E).

Introduce five natural bitplanes L0,…,L4. Require Sub(E,Li) for every i=0,…,4 and Sub(E,L3+L4). These six calls imply that

L=L0+2L1+4L2+8L3+16L4

is zero outside E and has digits exactly in 0–23 at E slots: the last call forbids the simultaneous 8 and 16 bits. The final equation is

Fsel=6E+L.

Both sides have digits below 32: Fsel≤26 and 6E+L≤29 slotwise. Consequently every newly firing site has η(v)+Σ_{w∼v}Apre_t(w)≥6. The recurrence has already ensured Apre_t(v)=0 there, so this is exactly its actual sandpile height before the layer. Conversely, if it is legal, the slack is between 0 and 20 and has such bitplanes. No elementwise product, array oracle, varying conjunction, or unexpanded comparison is used.

## 5. Paid exact target

For each axis introduce natural h,s,ℓ and a positive slack g. Enforce

ζ=2h+s, s(s−1)=0,
ℓ+2sh+s=half_extent+h,
ℓ+g=full_extent.

These clauses force s∈{0,1}, ℓ=half_extent+the signed physical coordinate, and 0≤ℓ<full_extent. Use POWER to form Ptarget=b^(ℓx+Aℓy+ABℓz), then require Sub(V,Ptarget). Positional uniqueness identifies precisely the supplied target. The interior mask forces it off the shell as a consequence, and can always be satisfied by enlarging a witness box around a genuine finite prefix and the target.

## 6. Soundness: a legal finite sequence, not an overfiring supersolution

The recurrence proves that E_0,…,E_{K−1} are disjoint finite subsets and exactly partition V. For each layer, the legality clauses certify every member at the beginning of that layer. Serialize its finite members in any order. Before a member itself fires, firing other members only adds nonnegative chips to its height. It remains unstable and may legally topple. Induct through all layers. The resulting finite legal sequence has binary odometer V and contains the target. Nothing is asserted about the endpoint’s stability or subsequent evolution.

In particular, two adjacent initially height-five sites cannot certify themselves by mutually supporting activations: Apre_0=0 forces the earliest nonempty layer to be tested without any later support. The known stabilizing-supersolution overfiring counterexample is rejected.

## 7. Completeness

Given a finite legal binary prefix containing the target, stop it when the target first topples. It has length K≥1. Enlarge the paid centered prism until every toppled site and the finite patch lie strictly inside, and all four spread margins hold. For each t<K let E_t be the singleton of the t-th toppling and Apre_t the set of earlier topplings. Their streams satisfy the recurrence; V is the full set. The neighbor and selected-site values are exact. The legality slack is at most 20 because initial heights are at most 20 and at most six previously toppled neighbors contribute one chip each. Its five bitplanes meet all six mask clauses. The target decoder and point mask have their unique intended values. Completeness of the explicit arithmetic macros supplies all remaining witnesses.

## 8. Remaining obligations

At this stage the architecture has no identified mathematical gap. The following are separate from this closed proof and must not be conflated with it:

1. Completed: a newly authored literal fixed-shape polynomial DAG implements every clause, positive adapter, and input field. It has 3,308 positive witnesses, 1,923 equations, 14,778 arithmetic gates, and exact degree 18. Author-side source-correspondence and semantic regressions pass; see SOURCE_NOTES.md and the evidence receipts.
2. Pending: independently reconstruct and audit that emitted source, including exact ledger and degree. The source and builder are frozen for this review.
3. The POWER macro retains the specifically pinned constructive Pell theorem dependency from Report 50.
4. Any universal-loader identification, all-site-one-shot property, or raw machine-input compiler needs its separately scoped dependency. No such theorem is reproved here.

Finite experiments may test these formulas but cannot replace their all-integer proofs. No finite-fold or real-witness exactness claim is made.
