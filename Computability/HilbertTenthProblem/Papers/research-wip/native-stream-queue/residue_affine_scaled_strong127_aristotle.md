# The fixed binary residue-affine orbit polynomial in 127 operations

The complete fixed-map construction costs **127=60M+67A**, with the same
**21 strictly positive witnesses** and the same two ordinary positive inputs
`input=x`, `target=y` as the accepted binary-lane128 construction. Its ordinary
total degree is at most **668**. Allowing zero steps costs **129=61M+68A**,
with the same witnesses and degree at most **669**. The unmodified 128/586
construction remains the lower-degree alternative.

For positive integers x,y the new polynomial has a positive integer zero
exactly when f^T(x)=y for some integer T>=1, where the fixed map is

    f(2v+1)=3v+2,  f(2v+2)=v+1,  v>=0.

The zero-step variant instead allows T>=0. The horizon is existential and
unbounded, not another supplied parameter. This is a fixed shortcut-Collatz
finite-orbit representation: no termination, universal simulation, or new
universal Diophantine bound is asserted. No program code is supplied or
compiled; the fixed table is exactly ((3,2),(1,1)).

The saving applies the already established complete84 scaled-strong identity
to the actual paid128 source, including its outer comparison finalizer.
It gives a stronger equivalence than the earlier lane deletion:
**the identity map on every supplied witness tuple preserves positive zeros.**

## 1. Exact paid block and changed rows

Use the literal native meanings

    a=native__R12, c=native__R10a, Delta=native__A,
    c²=native__c2, Delta*c²=native__Ac2, f²=native__L16.

All three last registers are already paid, live producers in the parent.
The old private block is

    native__ic2 = native__i * native__c2
    native__ic22 = native__ic2 * native__ic2
    native__normalized_strong_Q = native__A * native__ic22
    native__f_square_minus_one = native__L16 - native__normalized_strong_Q
    native__R16 = native__A * native__normalized_strong_Q.

It costs4M+1A. Replace it by

    native__scaled_aux_root = native__i * native__Ac2
    native__R16 = native__scaled_aux_root * native__scaled_aux_root
    native__scaled_f_square = native__A * native__L16
    native__f_square_minus_one = native__scaled_f_square - native__R16.

This costs3M+1A. The fresh root and scaled-square identifiers are new paid
producers, not free inputs. The four new block rows are emitted at the old
`native__normalized_strong_Q` position; the five old block rows are removed
from their previous positions. Every dependency is then earlier in the list.
The names `native__R16` and `native__f_square_minus_one` are retained with
their new definitions.

The only other changed row is the final subtraction:

    norm_output = norm_outer_product - native__A.

Thus three old identifiers disappear, two new identifiers are added, and
three retained identifiers have changed definitions. Of each128-row parent,
122 rows remain literal; the new total is127. No packed lane, scale, endpoint
loader, ordinary residual, native norm besides the strong factor, or supplied
port changes. The control B P^4 variant has the identical change. Appending
the two literal endpoint rows produces the129-row zero-step variant.

The static receipt guards the five old definitions and their entire consumer
sets. The deleted `ic2` feeds only `ic22`; `ic22` feeds only the old strong Q;
Q feeds only the old strong difference and R16. The strong difference feeds
only `native__normalized_norm_units`, and R16 feeds only `native__L17`.
There is therefore no lost consumer or additional restoration cost.

## 2. Whole polynomial identity, including all outer equations

Put t=i*c² and let Ns=f²-Delta*t² be the old normalized strong factor.
The coefficient and strong-factor identities are

    R16_new=(i*Delta*c²)²=Delta²*t²=R16_old,
    Ns_new=Delta*f²-Delta²*t²=Delta*Ns.                 (1)

They are identities over every commutative ring. In particular the entire
auxiliary factor R16*(V²-y_aux²)+y_aux² is unchanged, with V=of-c exactly as
in this source. The already paid c², Delta*c² and f² keep all their consumers.

Let P6 denote, for proof only, the product of the other six native factors:
main, auxiliary, first, checksum, index, and linear. Let e0,...,e3 be the
four literal ordinary residuals and G=1+e0²+e1²+e2²+e3². These quantities
are not introduced as free circuit ports. The parent and new full outputs are

    F128=P6*Ns*G-1,
    F127=P6*(Delta*Ns)*G-Delta=Delta*F128.              (2)

All six native product multiplications, four residual squares, their additions,
the final multiplication by G, and the final subtraction remain paid. Scaling
does not remove, weaken or assume any ordinary comparison. Upstream retained
values and R16 are identical; downstream products containing the strong factor
are scaled. Literal retention is not a claim that all register values agree.

For the empty-step extension, the same all-ring identity is

    F129=(x-y)*F127=Delta*((x-y)*F128)=Delta*F130.       (3)

Neither (2) nor (3) uses a zero equation, division, binary typing, or a Pell
identity. The old native norm product equal to1 is recovered only after
cancelling the positive multiplier below. Inferring seven unit factors
directly from a product equal toDelta would be invalid.

## 3. Positivity before equations and full same-coordinate equivalence

The positive outer hats give E0,E1,W,Z>=0. The source computes

    J=E0+E1, h=x+y+height_slack>=3, B=8h>=24,
    P=(B-1)J+1>=1.

For the primary source Q=B P³>0, q=16Q>0, and

    F3=16*(E0+P*Z+P²*W)+8>=8.

The three supplied native F0,F1,F2 are strictly positive. Consequently

    r=F0+qF1+q²F2+q³F3>0,
    X=q*(r+bound_beta)>0,
    Y=(2*odd_half+1)*q>0,
    a=XY+Y=Y*(X+1)>0,
    Delta=a²+4a+3=(a+1)(a+3)>0.                       (4)

The native bound_beta and odd_half are positive supplied witnesses. These
inequalities use only source definitions on the entire positive domain; no
outer equation, repunit relation, kernel theorem, or dyadic scale is assumed.
The B P^4 control has the same positivity proof. The endpoint product adds
no restriction on the witnesses in the x=y branch.

Over the integers, (2)--(4) give F127=0 iff F128=0 on every identical allowed
tuple. Equation (3) gives the analogous F129/F130 equivalence. This is a
bijective identity map on all21 witness coordinates, not merely a projection
after choosing fresh native auxiliaries. The inherited complete positive-zero
theorem for128 therefore transfers without revisiting a native sign or rank
argument. The soundness and converse include all orbit lengths, unused
selectors and zero quotient words already handled there.

The six outer witness names remain edge0_hat, edge1_hat, quotient_hat,
product0_hat, height_slack, global_slack. The fifteen native names remain
F0,F1,F2,odd_half,bound_beta,eta,zeta,f,o,y_aux,h,ga,i,j,tau_gap, each with
the literal `native__` prefix. Together with input,target there are23 supplied
ports, all live. There is no unrestricted signed-zero equivalence claim:
cancellation requires Delta nonzero, and (4) establishes precisely the
positive-domain condition needed here.

## 4. Complete counts and handwritten degree bounds

| Variant | M | A | Total | Witnesses | Degree at most |
|---|---:|---:|---:|---:|---:|
| Q=B P³, T>=1 |60|67|127|21|668|
| Q=B P⁴ control, T>=1 |60|67|127|21|824|
| Q=B P³, T>=0 |61|68|129|21|669|

The two nonempty certificate producer cores cost113=55M+58A with five
comparisons in the inherited convention: four ordinary equalities and the
scaled native product equal toDelta. The complete polynomial still pays
the additional5M+9A, giving127. Products by fixed numerals, the power gates,
all loaders and all witness conditions represented by the parent remain in
the complete arrays. No source row is dead.

Here all23 supplied coordinates have degree one and integer literals have
degree zero. For the primary chart, deg P<=2, deg q<=7, deg F3<=5,
deg r<=26, deg X<=33, deg Y<=8, deg a<=41 and deg Delta<=82.
For the control the corresponding bounds are2,9,5,32,41,10,51,102.
The accepted handwritten parent bounds are586 and722, respectively.
Equation (2) therefore gives668 and824, and (3) adds one. No exact degree
is claimed and no saved array was evaluated or given automatic degree
propagation in obtaining these bounds.

As a factor-level check, the primary seven bounds change from
[92,220,51,7,120,42,42] to [92,220,51,7,202,42,42], whose sum is656.
The control bounds become [114,272,63,9,250,52,52], summing812. The literal
outer G has bound12 in either case. The main bound uses the same all-ring
identity (ac+D0)²-(a²+H)c²=D0²+2acD0-Hc² as the parent, with H=4a+3;
it does not use a zero-set relation.

## 5. Source binding, inherited coverage and execution limits

The receipt contains all383 rows of the three new arrays and authenticates
the complete parent JSON. The fresh helper performs only byte authentication,
literal edits, consumer checks, topology, liveness, role and paid-operation
counts. It has no source-array evaluator, polynomial interpreter or degree
propagator. No predecessor or supplied helper was executed or imported.
All12 dependency files are authenticated: eight immediate files below and
the four source/proof pins declared by the128 packet.

| Immediate dependency | SHA256 |
|---|---|
| binary-lane128 MD | b5d93830a38426f5ac4129d04888efa94b0086932277b969dd810bff0ad1120c |
| binary-lane128 JSON | daa90bb7113164e564444eaca6de7025edaddd0e27fde02f93c9e7b11f4d41ea |
| binary-lane128 PY, hash only | 14f0119560751ca783faceeff0b0bc35d8f095deeaf528641883794c0f7f8823 |
| independent128 review MD | 4be186c471e588c16d181f9da910c6a71b84969192a871737e737565f6360d8d |
| complete84 scaled-strong MD | 01eb7df6688c08c6788a3c7a1cc272ca5ffc1a87734fd622dbec8a64ae974ade |
| complete84 scaled-strong JSON | 8b2bc5d0b4db90c168107b7ded2cb4ca08df0098ed190851a3db4f1e49a9c0cf |
| scaled-strong249 MD | 2230f44faee7e2ecebb0ce29722462f121a49e85addf3740d8b8b54efd7bc8a4 |
| its required degree-correction MD | ada1718ff4e93eb4b48e50d1362b8912973c6d629e1f724878a4e12804a39f11 |

The full parent128 proof, all literal source rows, its accepted independent
review, and the complete84 identity proof were read inertly for this task.
The249 proof/correction were fully read in the preceding independent review;
they supply provenance for the same sharing, not this packet's degree bounds.
The parent128 native/Pell theorem and its external foundations remain inherited
through that accepted proof and review. They are not newly audited here, and
the old finite diagnostics are not rerun or promoted to a new kernel proof.

The only fresh code execution is this packet's own static writer and its
normal/optimized exact receipt checks before freezing. Afterwards its helper
is frozen evidence and must not be replayed. No repository or Git mutation
occurs. The new result is the complete fixed-map127 construction above;
the separate universal84 and U9 universal-host bounds are not changed.

The fresh static writer and the normal and optimized (`-O`) exact receipt
comparisons, all run from `/`, passed before this freeze. They authenticated
the12 dependency files and checked all383 emitted rows with all23 ports live.
The frozen evidence files are:

| File | SHA256 |
|---|---|
| `residue_affine_scaled_strong127_aristotle.py` | ef402af7278cf59a9e6f587ec360e02a94faa4a67f6b4663bfd83ecbe221e3b1 |
| `residue_affine_scaled_strong127_aristotle.json` | e02303ae38f9ef6651e5bc62ff59fed38d4772cd3d42a05ccc29f406e00c7965 |
