# Factorizing Wang receivers: a separate compiler research candidate

## Status and intended use

This note proves a new local Boolean decoder and gives a fully materialized
candidate coefficient tuple. It does **not** claim a new complete
K215-to-Diophantine compiler theorem. In particular, do not substitute this
tuple into the main delivered polynomial merely on the strength of its
finite certificates. The remaining obligation is identified in Section 7.

The construction was developed against ProveIt commit
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`, chiefly package
`36-small-tuple/coefficients/`. Its comparison baseline is that package's
`B=2^1012115` tuple. The new local decoder and candidate geometry are
AI-assisted research material prepared for ProveIt; no human or proof-assistant
endorsement is asserted.

| Measure | Package 36 | Candidate |
|---|---:|---:|
| Unary selectors per native cell | 943 | 457 |
| All native support positions | 986 | 523 |
| Radix exponent b | 115 | 143 |
| Cell length L | 8,801 | 4,829 |
| Base exponent d=bL | 1,012,115 | 690,547 |
| Largest coefficient bit length | 1,016,946 | 697,126 |
| Four raw coefficient payloads, bytes | 506,664 | 346,098 |
| Deterministic gzip payloads, bytes | 10,416 | 5,749 |

The candidate's base exponent is 31.7719% smaller and its raw tuple is
31.6908% smaller. These are measured candidate sizes, **not** established
new bounds for the complete consistency polynomial. They have no bearing
on the main polynomial's proven variable/degree improvement.

## 1. The structural change

The old Wang language contains 488 receiver tiles: two possible scanned
symbols for each of 199 rightward and 45 leftward destination states.
Receivers have a special algebraic form. Number states by q in {0,...,215}
and define new labels

\[
 R(q)=256+q,\qquad L(q)=512+q,\qquad H(q,b)=512+2q+b.
\]

The two direction ranges are disjoint, and neither meets the six special
horizontal labels 0,...,5. Replace the old vertical markers
434,435,436,437,438 by 2,3,4,5,6. Ordinary symbols remain 0 and 1.
For actual state labels, this is an injective renaming of every edge
label in the original machine language.

Use two receiver modes

\[
 (256,0,0,512),\qquad (0,0,512,512)
\]

in place of all 488 receivers. Supply eight Boolean state bits q_R,j,
eight Boolean state bits q_L,j, and one Boolean symbol bit u. The remaining
455 selector modes are exactly the relabelled nonreceiver tiles, including
Start and the inherited globally impossible forbidden tile. Thus there
are 457 selectors and seventeen additional Boolean bits.

The right receiver's occupied expansions are

\[
 (256+q,b,0,512+2q+b),\quad 0\le q<256,\quad b\in\{0,1\},
\]

and the left receiver's are

\[
 (0,b,512+q,512+2q+b).
\]

The apparently superfluous q values cause no new tilings. A right receiver
with a q not among the actual 199 right destinations has a west label
that occurs on no east edge of any allowed tile. A left receiver with q
outside the actual 45 left destinations has an east label that occurs
on no west edge. Hence all such tiles are impossible in any edge-matched
periodic plane or torus. The finite audit enumerates the 1,479 expansions,
finds exactly 536 extra receiver tiles, and checks this unmatched-edge
obstruction for each one. Deleting them gives precisely the relabelled
943-tile language. The inherited forbidden tile is also impossible.

## 2. A local decoder with gated binary payloads

Let n be the number of selected unary modes. Put alpha=1 when the right
receiver mode is selected and beta=1 for the left receiver. Let

\[
 Q_R=\sum_{j=0}^7 2^j q_{R,j},\qquad
 Q_L=\sum_{j=0}^7 2^j q_{L,j}.
\]

First use a nine-bit selector field, masked by 510. Since 0<=n<=457,
its permitted values are exactly 0 and 1. Every other contribution is
divisible by 512, so this conclusion does not assume payload carry bounds.

Above that field place two nine-bit gate fields

\[
 G_R=255(n-\alpha)+Q_R,\qquad
 G_L=255(n-\beta)+Q_L,
\]

each masked at bit 8. After selector extraction each lies in [0,510],
so neither can carry out of its nine-bit field. If n=1, bit 8 is zero
in G_R exactly when Q_R=0 or alpha=1; similarly for the left gate.
This follows from the elementary identity

\[
 \{q\in[0,255]:(255+q)\mathbin{\&}256=0\}=\{0\}.
\]

A subsequent two-bit gate field is

\[
 G_b=(n-\alpha-\beta)+u,
\]

masked at bit 1. In an occupied cell, it forces u=0 unless a receiver
mode is selected. It has value at most 2, so causes no carry into its
next field.

The coefficient construction uses only nonnegative integers. For example,
255(n-alpha) is implemented by assigning gate contribution 255 to every
selector except the right receiver; there is no subtraction of unknowns
inside the local coefficient convolution.

There are 44 edge-bit fields, eleven per port, followed by three anchor
fields, all in radix four. Occupied label x is represented by x+1024.
Give q_R,j contributions to west bit j and south bit j+1; give q_L,j
contributions to east bit j and south bit j+1. Give u contributions to
north and south bit zero. Each edge field also receives its ordinary
Boolean copy bit. Mask the low bit in each radix-four field.

**Occupied-cell theorem.** If n=1, the clause mask accepts exactly the
correct copied edges and three unit anchors of one of the 1,479 expanded
tiles above.

**Proof.** The gates force the inactive receiver payloads to zero. For an
ordinary selected tile both Q values and u vanish. For a right receiver,
Q_L=0 and Q_R,u are arbitrary; its four labels are exactly
(256+Q_R,u,0,512+2Q_R+u), with no binary carry in these displayed
decompositions. The left case is symmetric. Every radix-four field now
contains a generated Boolean bit plus its copy bit, and is at most 2.
Its masked low bit is zero exactly when the two bits agree. The three
anchor fields are 1 plus their copy bit and therefore force all anchors
to one. This proves the claim. QED.

### Empty cells: the point needing care

For n=0 the new gates permit auxiliary q and u bits. Thus the old assertion
that an empty native cell has **no** edge payload is false for this decoder.
It must not be reused without modification.

Nevertheless every edge occupancy bit is zero in an empty cell. At each
lower edge-bit field the largest possible sum is q_R,j+q_L,j+copy_j<=3;
no radix-four carry is possible. The occupancy fields receive only their
copy bits and hence the low-bit test forces those bits to zero. Likewise
all three anchors are zero. Therefore the following weaker property is
proved for every locally accepted cell:

\[
 \text{all four copied occupancy bits equal } n\in\{0,1\}.
\]

After spatial and temporal edge matching have been established, occupancy
propagates from the marked Start cell to the entire connected recovered
tableau. Every cell then has n=1, and the occupied-cell theorem gives
exactly the original Wang computation. The order of these deductions is
essential; it is the main outstanding interface-review issue in Section 7.

## 3. Literal finite geometry and coefficients

The executable recipe in `build_factorized.py` is the authoritative finite
definition. In brief, selectors occupy positions 0,...,456, with Start at
0 and the forbidden tile at 1. Edge copies occupy offsets
(539,528,517,495), eleven positions per offset. State and symbol auxiliaries
occupy 567,...,583. Dummies are at 507,508, and anchors at 600,1203,1807.
Thus |E|=523.

Let W_j=2^(29+2j), 0<=j<47. The three gate-field units are
2^9,2^18,2^27. The clause coefficients c_e follow Section 2 literally,
and the clause mask is

\[
 \mu=510+2^{17}+2^{26}+2^{28}+\sum_{j=0}^{46}W_j.
\]

Set rho=2^143, L=4829, d=690547, and B=rho^L. Define

\[
\begin{aligned}
 D_C&=\rho^{33}+\rho^{68}+\rho^{603}+\rho^{1207}
       +\sum_{e\in E}c_e(\rho^{2409-e}+\rho^{3015-e}),\\
 D_R&=\rho^{46},\\
 M_C&=B-1-\sum_{e\in E\setminus\{1\}}\rho^e-2\rho^{507},\\
 Z&=(2^{141}-1)(\rho^{4823}+\rho^{4824})
       +(2^{100}-1)\rho^{4825},\\
 M_{F,\mathrm{nat}}&=4+\mu(\rho^{2409}+\rho^{3015})
      +\sum_{j=0}^{10}(\rho^{528+j}+\rho^{585+j})
      +\rho^{1203}+\rho^{1807}+Z.
\end{aligned}
\]

The candidate ports are

\[
 (B-1,\ D_C+BD_R,\ M_C,\ M_{F,\mathrm{nat}}+B-1).
\]

The basis audit checks every coefficient in these overlap identities:

| Target | D_C source | D_R source | Temporal source |
|---|---|---|---|
| 528+j, 0<=j<11 | 495+j | none | 528+j |
| 585+j, 0<=j<11 | 517+j | 539+j | none |
| 1203 | 600 | none | 1203 |
| 1807 | 600 | none | 1807 |

It also checks both complete clause identities on E, for 39,748 exact
scalar checks. The two clause hit sets are disjoint, and the two anchor
hit sets intersect only at zero. Since L>2 max(E), these ordinary
differences are also the circular differences modulo L. The greatest
unshifted convolution exponent is 4822; all 382 added padding bits are
strictly above it. The inherited conservative carry mass

\[
 \mathcal M=(|E|+2)(2\sum c_e+6)
\]

satisfies max(4M+8,2mu+4,16)<2^143. Padding digits also obey
2(2^141-1)+4<2^143. Direct materialization gives

\[
 \operatorname{pc}(M_C)=d-523,\quad
 \operatorname{pc}(M_{F,\mathrm{nat}})=523,\quad
 M_C\equiv2\pmod4,\quad M_{F,\mathrm{nat}}\equiv4\pmod8.
\]

## 4. An exact rank-control certificate

Here d=11^2*13*439. Let lambda=8761 and k=lambda-1=8760.
Trial division verifies lambda is prime. Modular exponentiation gives

\[
 \operatorname{ord}_d(B)=4380\mid k,\qquad
 B^k\bmod\lambda^2=46258081\ne1.
\]

The latter residue is 1 modulo lambda, so v_lambda(B^k-1)=1.
For H_0=1+BD_C+B^2(D_R+1), the relevant residues are

| p | B mod p | B^2-1 mod p | H_0 mod p |
|---:|---:|---:|---:|
| 11 | 7 | 4 | 7 |
| 13 | 11 | 3 | 3 |
| 439 | 271 | 127 | 297 |
| 8761 | 975 | 4436 | 2668 |

These are precisely the arithmetic hypotheses of the package-24 Boolean
prime-padding lemma reproduced in the reference file. For widths and
heights that are sufficiently large powers of lambda, that lemma permits
Boolean lower-dummy choices tuning the actual packed rank to the required
temporal shift. This is a finite certificate for the arithmetic hypotheses;
application to the new compiler still depends on the interface transfer
in Section 7. In particular, the code does not infer an unbounded theorem
from bounded computation.

## 5. Reproduction and exact outputs

Run, using Python's standard library only:

```
python3 build_factorized.py
python3 independent_local_audit.py
```

The first materializes four deterministic gzip payloads and reports geometry,
mask populations, carry bounds, and controller certificates in
`factorized_results.json`. The second independently reconstructs the old
943-tile language from the source builder, renames its labels, enumerates
all occupied generalized decoder values, and proves by finite enumeration
that every extra receiver has an unmatched edge. It also constructs and
checks all 1,479 local masked-clause witnesses.

These tests do not run the infinite blank computation, prove Con(ZFC), or
constitute a Lean/Rocq certificate. They do verify every finite assertion
reported in this note.

## 6. Provenance and reuse

`k215_transitions.json` is an exact copy from package 36 at the pinned
commit. Its SHA-256 is
`880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755`.
The verbatim source builder is `coefficients__build_coefficients.py`.
Inherited licenses and K215 notices are retained in `licenses/` and
`UPSTREAM_COEFFICIENT_NOTICE.md`. New code and this note follow ProveIt's
MIT No Attribution license. Earlier contributions remain credited within
their original stated scopes; they are not relicensed.

## 7. Precise remaining mathematical obligation

The original native proof decodes a marked arithmetic solution by finding
a clean clause band, synchronizing the binary rotation with anchors,
establishing whole-cell spatial/temporal matching, and then propagating
occupancy. The new local decoder preserves the finite support geometry,
all overlap identities, all anchor values, and every occupancy bit, but
it permits payload bits in empty cells. Before claiming full transfer,
one must supply an explicit generalization of the native synchronization
and soundness argument that uses only those preserved properties before
occupancy propagation, and does not silently use the stronger old fact
that empty cells have no payload bits.

Concretely, prove the following interface lemma:

> A native clause decoder with (i) zero or one selector, (ii) three anchors
> and all four occupancy bits equal to that selector count, (iii) arbitrary
> support-constrained lower payload bits when the count is zero, and (iv)
> an exact specified Wang tile when the count is one, satisfies the native
> soundness proof under the two clean-band and unique-anchor support
> conditions checked here.

This lemma should explicitly cover nonzero binary offsets and the upper
dummy spill exception before whole-cell alignment has been obtained.
Then verify that the canonical forward witness proof uses only supported
bits, the same carry bound, and the certified rank controller, and that
the optional odd/square witness promises follow from the unchanged
population and parity identities. Those are the complete integration
obligations. They look attainable but are not treated as already proved
by this package. Until completed, the tuple is an experimentally verified
compiler candidate and is intentionally absent from the main equation.
