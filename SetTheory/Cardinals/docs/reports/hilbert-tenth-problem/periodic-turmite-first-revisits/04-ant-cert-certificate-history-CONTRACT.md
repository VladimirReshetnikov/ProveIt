# Literal 174-operation bounded-ant component: recovered edition

## Recovery and execution boundary

This directory is a new recovered edition after filesystem loss. Its `history174.json` has been reconstructed from retained, independently authored formulas and its full byte identity with the earlier artifact is verified by SHA256:

`2075bb290f3f81d7c04a27b82f50c4f492638d55a3a27f434f66497ae9fb90ea`.

The generator, audit, contract and receipts are newly recovered files with new byte pins; their identity with lost versions is not asserted. The source proofs were retrieved again at commit `5883b08b7af362077f13bb4afa97a23a90ae4cf8`, and each retrieved file's Git blob identity was independently checked. HISTORY174.md was copied from the authenticated recovered Report42 package and retains its source SHA256 `9c26b118aa28f8454204be6fb6f751beeae713a752d18b75943e9862e7de1656`.

Every DAG node is `[output,opcode,left,right]`; opcodes are +, -, *, integer operands are literal fixed numerals, and strings reference inputs or earlier outputs. All 174 nodes are explicit, without macros, power oracles, or free computed quantities. Equalities are free in this component ledger. They are not yet combined into a single polynomial.

`reconstruct_history.py` and `audit_history.py` are own code. The former reconstructs formula sharing and separately states all source residuals in input variables, then checks polynomial identities. The latter reads the serialized DAG and imports only this own module. No upstream program, module, saved arithmetic schedule, or code from source/ is imported or executed. Upstream Python is stored only as `.py.txt` reference data. Checks use explicit exceptions, and normal/optimized Python agree.

## Count and interface

174 operations = 72 multiplications + 78 additions + 24 subtractions; 48 equations; five positive parameters; 61 positive witnesses. Fixed numeral set: `{1,3,6,8,9}`. The actual geometric join witnesses are `W,Wp,Q,q`; decoded `I,FM,FZ`, packed P, and D0 are exported computed outputs.

All parameters and witnesses independently range over strictly positive integers. All computed nodes range over arbitrary integers. The parameters are:

`InitialMemoryPlus, FinalMemoryPlus, InitialHead, FinalHead, FinalSignPlus`.

The 61 witnesses are precisely:

- 13 adapters: APlus, BPlus, GEPlus, GWPlus, GNPlus, GSPlus, DPlus, EPlus, FPlus, GPlus, ZPlus, SWPlus, SNPlus
- 13 geometry values: q, Q, W, uQ, uW, Gt, Gy, WidthOdd, HeightEven, K, Wp, HeadRoot, HeadQuot
- 16 strict field-bound slacks: BoundA, BoundB, BoundC, BoundD, BoundE, BoundF, BoundG, BoundGE, BoundGW, BoundGN, BoundGS, BoundTestE, BoundTestW, BoundTestN, BoundTestS, BoundZ
- BoundInitial and BoundHead
- 17 Pell witnesses: a,c,d,f,h,i,j,k,o,r,s,w,tau,eta,zeta,ga,y_aux

Case matters: geometric W and Pell w differ, as do history K and Pell k. The prose theorem's gamma is ga. C, the four Test fields, P, D0, and all Pell intermediates are computed expressions, not new quantified variables. The Pell discriminant differs from the raw history field D.

## Exact positive-domain iff contract

Decode I=InitialMemoryPlus-1, FM=FinalMemoryPlus-1, FZ=FinalSignPlus-1. Positive witnesses exist if and only if there are width>=3 odd, height>=2 even, and steps>=1 with:

1. I a ternary Boolean word on the width-by-height board, flattened by x+width*y with east and south positive
2. InitialHead=3^j at an even-index board site, initial incoming/pre-departure heading north
3. Exactly steps ordinary color-zero-right/color-one-left turn/write/move steps, with every move staying on the board
4. FM the exact resulting Boolean board, FinalHead the final head word, and FZ either zero or FinalHead. At a black/even-index site its zero/one sign means north/south; at a white/odd-index site it means east/west

The arbitrary five parameters have no external Booleanity, power, range, or heading promise. Those are consequences of the equations. No wrapping or reflection is permitted. The final head is an arrival/pre-departure snapshot after the last certified move, not a physical stopping event.

## Pre-power bounds and kernel substitution

Positive geometry gives W>=11, Q>=W and q>=Q before any prime-power conclusion. Every packed field and Z has a positive slack to q, so is strictly less than q. Raw fields are nonnegative adapter outputs, and C and Test fields are sums of nonnegative quantities. Horner packing uses the list:

A,B,C,D,E,F,G,GE,GW,GN,GS,TestE,TestW,TestN,TestS,D.

Hence 0<=P<q^16 over arbitrary integers. Four squarings produce L=q^16, followed by D0=9L and r=D0-3P-1.

The pinned kernel theorem is applied with its length q_kernel=q^4 and packed word P0=P. Its hypotheses q_kernel>=2 and 0<=P0<q_kernel^4 are already proved; no digit or prime-power promise is assumed. It proves q^4 is a power of three, whence q is a power of three. Since Q divides q and W divides Q, both are powers of three. The repunit equations yield Q=W^height and q=Q^steps. The width and height equalities force odd width>=3 and even height>=2. Head divisor, square and strict bound yield the initial even-index board site.

## Inherited theorem and dependencies

General all-integer soundness and positive completeness are inherited mathematical theorems, not conclusions of finite tests and not newly compiled formal proofs. The primary proof is source/HISTORY174.md Sections 1-7. The associated kernel source is EXPLORATION_BASE_THREE_PELL_KERNEL.md at the same commit.

The kernel's precise domain is arbitrary q_kernel>=2 and 0<=P0<q_kernel^4, with 17 strictly positive witnesses. Its ten Pell equations plus the supplied-r equality imply q_kernel is a power of three and D0 divides binomial(2r,r), therefore P0 is ternary Boolean. Soundness does not assume P0 even. Conversely, power-three q_kernel and an even ternary Boolean P0 in range have positive witnesses. Its 49-operation cost is six outer plus 43 core operations; our q^4 substitution adds two squarings, producing 51 mask-and-Pell operations.

Dependencies used, with their actual scope:

1. Standard integer Pell classification, recurrences, addition identities, positive growth and strong divisibility classify first/main indices and establish c>A*Delta^2 before auxiliary rank or exponent decoding
2. PELL_RELAXED_AUXILIARY_PROOF.md, sections “The relaxed norm forces an integral Pell solution at A” and “Recovering the required divisibility of the auxiliary index”: with A>1, c=psi_A(p)>A*Delta^2 and (i*c^2)^2=Delta*(f^2-1), obtain m>0 with f=chi_A(m), p|m, c|m, i*c^2=Delta*psi_A(m). This abstract argument applies to A=a+3 without importing the original a+4 compiler
3. HALF_PARAMETER_PELL_92_PROOF.md Sections 3-4: integer odd-index polynomial identities and auxiliary congruences establish exact main index p=2r+1, using the checked comparison bound 0<2p<=m. Its inherited chi step-down lemma is recorded in PELL_SIGNED_PROOF.md and reduced there to the ordinary chi step-down fact. These classical facts remain inherited number theory, not a newly formalized proof here
4. The base-three kernel's own Sections 4-6 prove the changed ratio estimates, exponent congruence with base 3 and modulus 6a+8, exact rounding and central-binomial divisibility. These are not assumed by simply changing constants in a binary theorem
5. EXPLORATION_ODD_PRIME_HALF_DIGIT_MASK.md Section 1 invokes Kummer's carry theorem: when L=3^N, D0=9L and r=D0-3P0-1, valuation v3(binomial(2r,r)) is at most N+2 and equals N+2 iff every ternary digit of P0 is zero or one
6. Kernel Section 7 constructs its canonical positive converse: U=3^(2r+1), exact binomial-floor Y, main and first Pell coordinates; m=2c(2r+1) then supplies positive integral i,f,o,j,y_aux. Even P0 implies 2r+1=1 mod 4, ensuring the positive-sign congruences for the auxiliary quotients

No positivity is imposed on intermediate arithmetic. In fact the auxiliary half-parameter differences u^2-y_aux^2 and 1-y_aux^2 are negative on solutions.

## Outer soundness and completeness

After Boolean decoding, the four forbidden masks establish proper parity and exclude outward moves. Thus spatial shifts are boardwise shifts. The head recurrence reduced modulo Q gives the unique initial head. Its unique permitted route yields one on-board next head and therefore no time-block carry. Subtracting the established identity and dividing mathematically by Q repeats this induction, proving uniqueness throughout and the final head. A global bound NextC<q is not assumed beforehand. The sign recurrence and charged Z bound then prove Z Boolean and supported on the head. Only afterwards are the carry-free local toggle equations used to decode the ant transitions. The memory recurrence recovers every successive board and final FM.

Conversely a genuine bounded run supplies positive raw adapters, geometry quotients, range slacks and head witnesses. Its fifteen distinct packed fields have sum congruent to D modulo two: the toggle identities cancel A/B and F/G; directions/Test fields reduce to C plus the forbidden sum; forbidden-sum parity is Gt; C and Gt both have parity steps. Appending D makes P even. Thus r is even, so the inherited positive Pell converse applies. The parity argument is required for completeness, not soundness.

This history component alone does not supply periodic hardware, raw input encoding, initialization, an arbitrary-machine reduction, or halting acceptance. Recovered Report40 uses the same east/south, turn/write/move and pre-departure conventions, but its physical initial heading is east at (288650,75). Composition therefore requires the explicit proved rotation/translation and word initialization bridge. Report40 acceptance is a pre-departure residue-and-heading event while the ant continues indefinitely. Its arbitrary-program-to-U15 encoding remains a published external dependency.

## Exact residual correction and degree

Index equations from zero. Actual residual F_i is the expanded difference of the two DAG outputs in equality i. It equals the independently stated source residual except at i=46:

F46 = source46 + source45*((2*r+1+j*c)^2-y_aux^2).

F45=source45. This is a unit-triangular acyclic residual replacement preserving the simultaneous zero set over all integers. The checker verifies it symbolically.

Giving each supplied parameter/witness degree one and fixed numerals degree zero, the maximum actual residual degree is exactly 104, uniquely at index 38, the first Pell norm. Its top homogeneous part is:

531441*q^96*k^2*s^4*w^2.

Indeed the high term U^2*Y^4*k^2, with U=9*w*q^16 and Y=9*s*q^16, has coefficient 9^6=531441 and degree 96+2+4+2=104. All other actual residuals have smaller degree in the exact expansion. This component's sum of squares therefore has degree 208 and positive leading coefficient 531441^2. After composition, actual substitutions and witness identifications must be considered afresh.

## Fresh recovered checks

The serialized DAG passes all literal, acyclicity, count, exact polynomial and degree checks. The independent outer simulator attempts 768 combinations: every Boolean 3-by-2 initial board, each even starting site, and one through four steps. Exactly 264 prefixes remain on board. Every one satisfies all 38 outer-plus-mask equations through the actual DAG with positive outer witnesses, even bounded Boolean packing, and exact factorial valuation v3(binomial(2r,r))=16*6*steps+2. These checks do not materialize the enormous Pell tuple.

Ten malformed-DAG mutations are rejected: undeclared operand, changed constant, wrong arithmetic, duplicate output, forward reference, changed equality, changed numeral list, changed quantified witness, Boolean in place of integer, and deleted operation. Normal and optimized modes agree. Finite evidence corroborates the component and validator; arbitrary-integer equivalence remains the pinned theorem.

Replay, requiring Python 3 and SymPy:

- PYTHONDONTWRITEBYTECODE=1 python -B reconstruct_history.py
- PYTHONDONTWRITEBYTECODE=1 python -B audit_history.py
- Repeat with -O for optimized-mode checks
