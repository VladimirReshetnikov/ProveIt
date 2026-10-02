# Bounded joint-norm scout on the complete asymmetric87 polynomial

No operation saving was found in the four complete schedules below. The preserved sources provide exact, fully charged comparisons, not a general lower bound on87 or an exhaustive circuit search. The [checker](complete87_joint_norm_scout.py) and [receipt](complete87_joint_norm_scout.json) preserve all four schedules; parent files and receipts are unchanged.

The baseline is the normalized form emitted by `complete75_asymmetric_scale_tradeoffs.py`, with87=48M+39A operations, degree169,19 positive witnesses and the ordinary positive inputx. I read its full source and scale proof, the normalized-strong and coupled-index sources/proofs, and relevant existing factor-grouping, auxiliary-gap, constant-deletion and modulus obstructions. In particular this scout keeps X=wq and **Y=sq³**, both ratio slacks, the complete ordinary-input bridge and normalized strong condition. It does not retry the refuted squared-Y scale.

The helper pins the actual asymmetric source and saved literal DAG, normalized/coupled sources and fixed-input adapter before reading the selected87 source. It rewrites that complete DAG, prunes only registers with no path to the final polynomial, checks every dependency, exact equality of the entire old/new free-coordinate sets (including fixed numerals), and all20 input/witness names, and records every emitted gate. Multiplication by a fixed constant, squaring, every subtraction and the final product-minus-one are charged normally.

| Fully emitted circuit | M | A | Total | Relation to baseline |
|---|---:|---:|---:|---|
| First-norm reassociation |48|39|87|Identical entire polynomial|
| Direct main/input norm composition |50|40|90|Identical entire polynomial|
| Composition after cancelling root terms |49|40|89|Identical entire polynomial|
| Strong-unit substitution in auxiliary coefficient |48|40|88|Identical entire integer zero sets; explicit off-zero correction|

The first three preserve the exact polynomial and hence degree169. The final row is already dominated as an operation count by87; no improved universal frontier is asserted.

## 1. Shared notation and the complete interface

Use the parent's literal meanings

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a²+H,
    D=ac+X+(rho+sigma)H,
    kappa=2d*x+b+delta*Delta,
    mu=a*kappa+W+rho*H,
    V=of−c, t=ic².

The source register `A` means Delta; it does not mean the Pell parameter a+2. The paid packed-index, input bound, masks, transport and coupled linear factor remain unchanged. The fixed-input adapter's already established convention is retained: the source symbol MF contains the fixed raw mask plus B−1, and Kconstant=DC+B*DR, Bm1=B−1 and twice_cell_bits=2d are compile-time numerals. No new variable-quantity precomputation is treated as free.

The eight factors are

    N0=g²+(E*kY)(2g−k),
    Nm=D²−Delta*c²,
    Ni=mu²−Delta*kappa²,
    Na=Delta²*t²*(V²−y²)+y²,
    Nk, Nt, Ns=f²−Delta*t², L.

The complete output remains their product minus1, except that the first two composed variants evaluate Nm*Ni as one identical polynomial.

## 2. First norm: the apparent multiplication saving is a tie

With U=E*kY, the exact identity is

    g²+U(2g−k) = g(g+2U)−Uk.

Both sides need two multiplications and three additions/subtractions after U and k are available. The new complete circuit deletes the original g-square/doubled-g/cross-term gates and inserts the corresponding doubled-U and products. Full pruning still yields87 operations. No square or coefficient2 multiplication is silently omitted.

## 3. Combining the two Pell norms

The quadratic-ring identity gives

    (D²−Delta*c²)(mu²−Delta*kappa²)
      = (D*mu−Delta*c*kappa)²
          −Delta*(D*kappa−mu*c)².

This is an identity over arbitrary commutative rings, without positivity or zero assumptions. In the actual source c² remains live in the strong auxiliary block. Thus deleting its main-norm use does not delete its multiplication.

After the shared c² register is paid, the old main and input factors need seven operations. Their inherited two multiplication gates combine them with N0. Direct norm composition needs eleven operations for the new two roots and their norm, plus one multiplication by N0. The complete count consequently rises from87 to90. Its larger multiplication count is not offset by a hidden saving in the input bridge.

There is a better exact composition using

    l=X+(rho+sigma)H, m=W+rho*H,
    D=ac+l, mu=a*kappa+m, Delta=a²+H.

Cancel the ac·a*kappa terms before evaluation:

    u = a*(c*m+kappa*l)+l*m−H*c*kappa,
    v = kappa*l−c*m,
    Nm*Ni = u²−Delta*v².

This removes both original root-only subcircuits. The new joint root construction costs15 operations from already paid a,H,c,kappa,X,W,rho,sigma; its norm costs four more, and multiplying by N0 costs one. The old two roots, norms and combination occupy18 corresponding operations. Pruning the actual whole source confirms the difference:89=49M+40A, two operations above the baseline.

These failures are specific to the displayed norm-composition schedules. They do not prove that a different shared evaluation of these factors cannot save an operation.

## 4. Strong-unit substitution has a rigorous zero-set theorem but costs one more

Write S=Ns=f²−Delta*t² and G=V²−y². Replace only the auxiliary coefficient

    Delta²*t²  by  Delta*(f²−1).

If P denotes the product of the other six factors, excluding Na and S, then

    Fnew−Fold = P*S*Delta*(S−1)*G.

This is an exact off-zero identity. Moreover the two complete polynomials have identical **integer** zero sets, without restricting to canonical witnesses. At any integer zero of either complete product-minus-one, S is an integer unit. Since Delta=(a+2)²−1 is0 or3 modulo4, S cannot equal−1, so S=1. The two auxiliary coefficients then coincide. The same argument applies in both directions. This retains the entire strong condition rather than deleting it or assuming it before factor recovery.

The original source already computes Q=Delta*t² for S and obtains Delta*Q with one multiplication. The substituted source still needs Q for S and now also needs f²−1 before multiplying by Delta. Thus the apparent reuse of f² adds one subtraction; the fully pruned source has88=48M+40A. There is no free comparison or suppressed finalizer.

## 5. Executable evidence and limitations

`complete87_joint_norm_scout.py` emits all four complete schedules into its JSON receipt. Five exact symbolic identities cover direct composition, both cancelled roots, first-norm reassociation and the full substituted-auxiliary correction. The unconditional negative-strong-unit exclusion is checked on all64 modulo-four triples, supplementing the short proof above.

Each complete schedule is checked on256 supplied assignments, half signed, across four fixed bases. These total1,024 full polynomial evaluations and512 signed cases. The substitution row checks its complete correction; the other rows check exact output equality. Every gate is an ancestor of the final output and all nineteen witnesses plus ordinary inputx remain present. No imported universal zero or complete universal Pell witness is materialized by these numerical fixtures.

Reproduce with

    python complete87_joint_norm_scout.py --root /path/to/native-stream-queue --expect complete87_joint_norm_scout.json

or explicitly write a receipt with`--output`. Saved receipt comparison is recursively type-sensitive, so BooleanTrue cannot alias integer1. The helper contains no hard-coded temporary path and performs no parent imports or parent writes. It charges the literal circuits, not a symbolic simplifier's expression length. The only defensible conclusion is that these four plausible sharing mechanisms do not lower the complete87-operation bound. A saving elsewhere, or a different norm-composition circuit, remains open.

Root independently reviewed the complete emitted rewrites, all five algebraic
identities and the unconditional modulo-four zero-set argument. A fresh
repository replay matches the saved receipt. This bounded negative result
leaves the established87-operation universal bound unchanged.
