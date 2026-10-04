# U15 has a universal repeated input block, but the block is hyperbolic

The published U15 construction does give an effective fixed-context family

```
U_S W^x V_S,       W=(01)^3 11,
```

that halts exactly for the positive integers x in any selected c.e. set S. This is a derived initialization theorem on the same finite-blank-tape interface as [the 193-generator semigroup](group_directed_semigroup193.md). The repeated physical block has eight bits and is independent of S. It is not a raw run of ones.

The actual matrix image has determinant one and **trace -8942**, so the earlier eight-gate affine loader does not apply. Indeed every nonempty concatenation of the published ordinary-symbol blocks has hyperbolic matrix image. The construction therefore closes the repeated-block initialization question within the published encoding, while leaving the exact indexed matrix-power relation and the unbounded fixed-arity membership certificate unpaid. It gives no improvement to the complete 84-operation universal polynomial.

## 1. Primary premise and exact source boundary

Primary source: Neary and Woods, *Four Small Universal Turing Machines*, Fundamenta Informaticae 91(1), 2009, pp. 123–144, [published DOI](https://journals.sagepub.com/doi/10.3233/FI-2009-0036). The [author reading PDF](https://mural.maynoothuniversity.ie/id/eprint/12416/1/Woods_FourSmall_2009.pdf) has SHA-256 `6274cb6828579c234bf9f62b8fecc64dea4bb1ae842b4e2e39b9bfc676114c1b`; its printed pages 105–126 and draft DOI differ from the published bibliography.

The imported result is the effective halting-preserving TM → clockwise TM → bi-tag → U15 simulation, specifically Lemmas 2.1–2.2, Theorem 2.1, Definition 3.1, Table 1, and Section 3.5. The first two stages preserve ordinary input symbols, adding finite boundary symbols and a state marker. For U15, an ordinary symbol a_i with its separator is encoded by `(01)^(8i-5)11`; e_1 is encoded by `(01)^(8q_B)`. The initial U15 state is u1 scanning the final zero of `10`. These are the source facts used below; the new initialization argument is an application of them.

The placed dependency audit SHA-256 is `e8121b79d24eabb025bf74b144cc6517f084b26992b2b9c4b4ace47c62f070f5`, at `SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/group-theoretic-substrates/08-matrix-semigroup-core-loader-audit-U15_DEPENDENCY_AUDIT.md`. It records the same finite-input scope, including the literal undefined J1 cell. No archived compiler or predecessor Python was executed here. No new implementation of the arbitrary-program compiler is claimed.

The helper authenticates these WIP files:

| File | SHA-256 |
| --- | --- |
| group_directed_semigroup193.json | `c802f1ca0fde3cfcc856dd0f14ea2bf6270e1a9a924fe9743ee00c4336891639` |
| group_directed_semigroup193.md | `75f7e527b62717f21394750842a5569adc56231f1f6d6fab5e359e63b71ce56e` |
| neary_woods_explicit_universal_tm.md | `b04739084d093b1ee20dde5dbcf851f4cfac4d6895978f971211f9027cfdac8f` |
| matrix193_power_block_obstruction.md | `60f442caa77c68f11c73a4995fbebc4582a0ef64b3a9e41dfd68c27d8782d978` |

The primary PDF hash is recorded as reading provenance; the replay does not require a locally cached PDF or fetch network material.

## 2. Derived fixed-context initialization theorem

Fix a c.e. subset S of the positive integers and a semidecider for it. Effectively construct an ordinary one-tape TM M_S with unary input convention `a^(x+4)`: it counts the finite run, subtracts four, and simulates the selected semidecider. It loops on lengths not representing a positive x. The counting and conversion occur inside the simulated machine, not in an uncharged external arithmetic loader.

Use a single halt state. The usual finite normalization never writes the external blank: visited semantic blanks use a distinct nonblank tape symbol. This preserves the initial unary tape and the accepted set. Choose the ordinary alphabet numbering so that the unary letter becomes a_1 in the clockwise and bi-tag alphabets. The source's clockwise construction keeps the nonblank tape symbols and adds the right/left boundary markers; at the cut before the first input letter, the initial bi-tag word is exactly

```
e_1 a_1^(x+4) a_right a_left.
```

This is a genuine encoded clockwise configuration with one state and both boundaries. It contains at least seven ordinary symbols. The simulation's active bi-tag steps replace one ordinary symbol by one or two, so this length margin is preserved. No correctness claim on arbitrary malformed or one-symbol bi-tag inputs is needed.

Let P_S be the fixed binary encoding of the resulting bi-tag program, and let q_B be its ordinary alphabet size. Write

```
A_i=(01)^(8i-5)11,     W=A_1=01010111.
```

With no optional program padding, the full finite configuration word for the semigroup compiler is

```
[ P_S 1 A 0 (01)^(8q_B) W^(x+4) A_right A_left ].
```

Here A is the literal U15 start-state symbol, and its immediately following zero is the scanned cell. The nearest-head-first left half is `reverse(P_S 1)`; the right half is `(01)^(8q_B) W^(x+4) A_right A_left`. Both exterior tails are blank zero. This gives the same head cut and source interface used by S193.

Absorb W^4 into the fixed prefix:

```
U_S = [ P_S 1 A 0 (01)^(8q_B) W^4,
V_S = A_right A_left ].
```

Then the displayed word is exactly `U_S W^x V_S`. The primary simulation proves that it reaches J1 if and only if x belongs to S. The established directed-semigroup theorem consequently gives

```
x in S  iff  diag(Phi(U_S W^x V_S #)^(-1), P) belongs to S193.
```

All choices of program, alphabet indices, and contexts are effective finite recipes in the selected semidecider. This is an effective mathematical theorem with the same imported simulation premise as the parent, not a newly materialized compiler from arbitrary program source. It does not imply universality of `[1^x A0]` or any other raw-ones slice.

A parity-free alternative uses source input `a^(2x+4)`, internally decodes `(length-4)/2`, and repeats the fixed 16-bit block W^2. This will be convenient for the positive Pell parameter below.

## 3. Actual matrix classification and a uniform obstruction

The literal source uses

```
P=[[1,2],[0,1]], Q=[[1,0],[2,1]],
Phi(0)=E_1, Phi(1)=E_2,
E_j=Q^(-j) P Q^j.
```

Direct exact multiplication gives

```
Phi(W) = [[-12827,-3064],[16264,3885]],
det(Phi(W))=1, trace(Phi(W))=-8942.
```

This is hyperbolic, not parabolic or unipotent. The conclusion is not an accident of alphabet index one. Put

```
G=[[11,4],[8,3]], H=[[35,16],[24,11]].
```

Conjugation gives `Q E_1 Q^-1=P`, `Q E_2 Q^-1=E_1`, `P E_1=-G`, and `G E_1^2=H`. Therefore, for every i>=1,

```
Q Phi(A_i) Q^-1 = -G^(8i-6) H.
```

G and H have strictly positive integer entries and determinant one. Any nonempty product of the matrices on the right is, up to its overall sign, a strictly positive integer determinant-one matrix. Its diagonal sum is at least three: diagonal entries both one would force determinant at most zero because both off-diagonal entries are positive. Hence every nonempty concatenation of encoded ordinary symbols has absolute trace greater than two. Changing the chosen unary symbol or replacing it by a fixed finite ordinary-symbol word cannot make this particular published encoding parabolic.

The primary encoding also permits optional `S=(00)^2` padding before the fixed head delimiter. Its matrix is unipotent, but its exponent is padding for the same encoded bi-tag configuration, not the dataword. Varying only this padding is therefore not a variable-input theorem. This identifies a concrete parabolic component in the primary format without assigning it a computational role it does not have.

The matrix argument was separately challenged by another reviewer and found sound; that brief challenge did not re-audit the primary simulation or certify the new initialization proof.

## 4. Exact indexed-Pell interface that remains to be paid

For the even block B=Phi(W^2), the actual values are

```
B=[[114699033,27398288],[-145432688,-34739671]],
trace(B)=79959362, det(B)=1,
a0=39979681,
D=B-a0*I=[[74719352,27398288],[-145432688,-74719352]],
Delta0=a0^2-1=1598374892861760,
D^2=Delta0*I.
```

Consequently, for every natural x,

```
B^x=chi_a0(x)*I+psi_a0(x)*D,
B^(-x)=chi_a0(x)*I-psi_a0(x)*D.
```

This follows by multiplication in the two-dimensional quadratic algebra and holds identically, not just on the bounded examples. For fixed context matrices `L=Phi(V_S#)^(-1)` and `R=Phi(U_S)^(-1)`, the target is

```
chi_a0(x)*(L R) - psi_a0(x)*(L D R).
```

Given **correctly indexed** positive Pell coordinates chi,psi, its four entries have a complete generic 12-row source: two multiplications and one addition per entry, **8M+4A**, with fixed signed context coefficients. The receipt contains this exact assembly template. It excludes the cost and proof of supplying `chi=chi_a0(x)` and `psi=psi_a0(x)`, and it excludes the unbounded matrix-membership certificate. The ordinary input cannot simply disappear from those obligations.

The Pell norm alone does not impose index x. For example, the pair `(chi,psi)=(a0,1)` satisfies the norm regardless of the requested x and always assembles the index-one target. On a compiled singleton language containing one, an interface that never couples these coordinates to x would therefore accept every positive x. This is a concrete reason that a free Pell root is not a completed loader.

Moreover no finite arithmetic straight-line program using only the ordinary x and fixed constants can produce the exact four target entries by additions, subtractions and multiplications alone. Such entries would be polynomials in x. Multiplying by the fixed inverse context matrices and taking the trace would then make `trace(B^(-x))` polynomial, whereas it equals `lambda^x+lambda^(-x)` with `lambda=a0+sqrt(Delta0)>1`. This proves why the existing eight-gate affine target component cannot transfer by a mere constant substitution. It is not a lower bound on certificates with extra integer witnesses.

## 5. Reproduction and remaining scope

The fresh helper checks the four constant identities proving the uniform conjugation formula, 16 literal ordinary-symbol blocks, all 256 products of two of those blocks, the exact W and W^2 matrices, the quadratic relation for D, and 13 exact Pell-power identities. It reads the actual alphabet codes from the pinned S193 JSON. No U15 simulation, arbitrary-program compilation, archived code, or historical suite is run. The finite checks corroborate matrix identities; the general initialization theorem is proved in Section 2 from the cited primary construction.

```
python3 u15_unary_block_interface.py --root ABS_WIP --expect ABS_JSON
python3 -O u15_unary_block_interface.py --root ABS_WIP --expect ABS_JSON
```

Writer and fresh normal/optimized replays from `/` passed with exact JSON-type comparison. No complete Diophantine source or operation bound is claimed. The open work is now precise: either produce a different universal parabolic/raw-unary initialization, or pay an exact index-coupled power loader for the explicit hyperbolic block, and in either case supply the unbounded fixed-arity semigroup membership relation. The previously proved power-block obstruction still rules out replacing the latter by a computably bounded collection of constant-block powers with only Presburger restrictions.
