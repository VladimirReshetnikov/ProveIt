# A complete universal polynomial in 84 operations

The [complete source](complete84_scaled_strong_output.py) and [receipt](complete84_scaled_strong_output.json) compute a universal polynomial in **84=47M+37A operations**, with the same **18 strictly positive witnesses**, ordinary positive input and valid fixed-program numeral recipe as [normalized85](complete85_auxiliary_bezout_projection.md). Its exact total degree is **187** on every inherited admissible fixed-program slice; the naive gate-degree upper bound is197.

One multiplication disappears by using the already paid main coefficient in the auxiliary block and scaling the complete output. There is no coordinate elimination or new inverse map. The entire new polynomial satisfies

    F84 = Delta * F85                                      (1)

on the identical supplied coordinates, as an identity over every commutative ring. The actual source has Delta>0 on its complete positive witness domain, before any polynomial equation is imposed. Thus the two complete positive integer zero sets coincide exactly. This lowers the operation count from85 to84 while increasing exact degree175 to187; the older lower-degree tradeoffs remain available. It is not a lower bound over all circuits, and it does not change the separate74-operation comparison-system construction.

## 1. The actual coefficient sharing

Use the parent source meanings

    c = R10a, a = R12, Delta = A,
    c² = c2, Delta*c² = Ac2, f² = L16,
    t = i*c², Q = Delta*t², Kaux = Delta*Q.

The source's register A is the discriminant Delta, not the Pell parameter a+2. The parent auxiliary and strong factors are

    Na = Kaux*(V²−y_aux²)+y_aux²,
    Ns = f²−Q,
    V = c(Tf−1)−R*f²,

where T=`auxiliary_quotient` and R=`r_lhs` remain fully paid. The complete source already computes c² and Ac2 for the main norm. Its private old coefficient/strong block has five rows:

    ic2 = i*c²
    ic22 = ic2²
    strong_difference = Delta*ic22
    R16 = Delta*strong_difference
    norm_strong = f²−strong_difference.

These cost4M+1A. Replace them by the four literal rows

    aux_coefficient_root = i*Ac2
    R16 = aux_coefficient_root²
    scaled_f_square = Delta*f²
    norm_strong = scaled_f_square−R16.

They cost3M+1A. Exact polynomial identities give

    R16_new = (i*Delta*c²)² = Delta²*i²*c⁴ = R16_old,
    norm_strong_new = Delta*f²−Delta²*i²*c⁴ = Delta*Ns.   (2)

All other factors, including the complete new Bezout quotient V and the auxiliary norm Na, are unchanged. In particular f², c² and Ac2 retain every original consumer. The source does not treat any variable product, coefficient or square as a free input.

The checker authenticates all five old definitions and the paid c², Ac2 and f² producers. No removed private intermediate has an external consumer. The old norm_strong has only one consumer: the final multiplication `seven_units`. All79 other non-output rows are preserved literally, followed by a topological reorder where necessary.

## 2. The complete finalizer and all-value identity

Write P for the product of the six retained factors: the first norm, main norm, input norm, auxiliary norm, index factor and transport factor. This notation is for proof only; all six factor producers and all six finalizer multiplications remain in the saved circuit.

The old and new outputs are respectively

    F85 = P*Ns−1,
    F84 = P*(Delta*Ns)−Delta.

Thus (1) holds as an exact polynomial identity, using no unit equation, sign assumption, division or positivity. The literal final row changes from

    polynomial = seven_units−1

to

    polynomial = seven_units−A.

The helper proves both identities (2) by exact sparse coefficient arithmetic. It separately expands the two complete finalizers at their seven factor ports and Delta, proving (1). The unchanged row definitions and private consumer checks lift these cuts through the actual full sources.

The new factor list is **not** asserted to consist of seven units at a zero. Once the parent theorem is recovered, its six retained factors equal1 and the scaled strong factor equalsDelta. Directly inferring seven unit equations merely from the new product equalingDelta would be invalid; the proof below instead cancels the known positive multiplier in the complete identity.

## 3. Positive-zero equivalence and inherited universality

The positivity of Delta follows directly from retained source definitions. For a valid fixed program B−1=`Bm1` is positive, and J=`Jrep`, w and s are strictly positive witnesses. Therefore

    q=(B−1)J+1 > 0,
    X=wq > 0, Y=sq³ > 0,
    a=XY+Y=Y(X+1) > 0,
    Delta=a²+4a+3=(a+1)(a+3) > 0.                       (3)

This uses neither a norm equation nor an already decoded history, and it precedes invocation of the parent positive-zero theorem. Over the integers, (1) and (3) imply

    F84=0  if and only if  F85=0

on every supplied positive tuple in the inherited valid compiler slice. The map in both directions is the identity on all18 witnesses and the ordinary input. Consequently the parent's full ordinary-input universality theorem transfers directly, including every fixed-program hypothesis, normalized strong-rank argument, input loader and positivity condition. There is no restriction to canonical Pell fibers, refreshed heights or selected histories.

The six fixed numeral ports are still `Bm1,Kconstant,twice_cell_bits,inner_bits,MC,MF`. They retain the parent's complete compiler recipe, including its shifted MF convention. The arithmetic helper accepting a numeral assignment for a coefficient identity does not certify that arbitrary numeral values encode a valid program.

There is deliberately no unrestricted signed-zero equivalence claim. At Delta=0, (1) makes the new output zero regardless of the parent output. The receipt includes an explicit signed off-domain arithmetic assignment with Delta=0, F84=0 and F85=−649. This illustrates the boundary; it is not a positive/compiler counterexample. The all-ring identity itself remains true there.

## 4. Fully paid source ledger

The saved circuit includes one full84-row array, every supplied port and the final output. All rows and all free ports are live. Its ledger is

| Part | M | A | Total |
|---|---:|---:|---:|
| Complete seven-factor producer core |41|36|77|
| Six product multiplications and final subtraction |6|1|7|
| Complete polynomial |47|37|84|

The parent totals48M+37A=85. The sole net saving is one multiplication in Section1; the final subtraction ofDelta costs exactly one addition/subtraction, just as the old subtraction of1 did. Reusing an existing register as its operand introduces no new gate. No comparison, input condition, witness, loader cost or finalizer is omitted.

## 5. Uniform exact degree187

Every supplied witness and the ordinary input have degree1. Each of the six fixed compiler numerals has degree0. The pinned [parent source review](review_complete85_auxiliary_bezout_source.md) proves the parent's exact degree175 and its complete uniform leading homogeneous form; its [separate mathematical review](review_complete85_auxiliary_bezout_math.md) supports the positive-zero theorem.

Put

    Q0=(B−1)J, k0=eta+zeta, gamma0=rho+sigma,
    C1=Q0−F−Z−alpha−twice_cell_bits*x,
    Ttransport=w*C1−transport_quotient*Q0.

The retained source gives a degree6 with leader `w*s*Q0⁴`, so Delta has exact degree12 with leader

    Delta_top = w²*s²*Q0⁸.

Multiplying the established parent leader by Delta_top gives the complete new leader

    32 Q0^111 h gamma0 delta² i⁴ k0^13 w^18 s^31
       * Ttransport * T² * f².                         (4)

The lowercase delta in (4) is the retained input-modulus witness; it is distinct from the discriminant Delta. The variable T is the auxiliary quotient, not the transport quotient.

Formula (4) is nonzero uniformly for every admissible fixed-program slice. For example, its monomial

    J^112*h*rho*delta²*i⁴*eta^13*w^18*s^31
       *transport_quotient*T²*f²

has coefficient `−32*(B−1)^112`, which is nonzero because B−1>0. No equality that holds only on polynomial zeros is used in this degree argument. Polynomial multiplication in the integral-domain coefficient ring gives exact degree175+12=187.

The seven actual factor degrees are

    22,18,32,60,7,2,46.

The first six inherit their entire parent polynomials. The final factor is exactlyDelta times the old degree34 strong factor, hence has degree46. These sum to187. Subtracting degree12 Delta at the final row cannot cancel the degree187 leader. The gate recurrence, which ignores the parent main/input cancellations, gives the separate upper bound197.

Two full dense univariate coefficient executions at different diagnostic numeral assignments and moduli attain187, check all seven factor degrees and verify the coefficient identity F84=Delta*F85. They corroborate the source but are not substitutes for the uniform proof (4), nor are the diagnostic numerals claimed to instantiate valid compiler programs.

## 6. Scope of the executable evidence

This is a bounded standard-library source/receipt CLI, not a maintained general packet API. It authenticates nine immediate parent/review files and all twelve source/proof pins declared by the frozen85 receipt, for21 checked dependencies. The actual files are read as bytes or JSON; no predecessor Python, archived program, old builder or historical suite executes.

In addition to the general coefficient and full-finalizer identities, the receipt records64 complete signed evaluations, including32 rational assignments, retained value checks, the signed Delta=0 boundary, both dense coefficient diagnostics and the literal exact-versus-upper degree metadata. These are algebra checks, not materialized enormous native Pell witnesses.

Run from any working directory:

    python3 complete84_scaled_strong_output.py --root /absolute/path/native-stream-queue --expect /absolute/path/complete84_scaled_strong_output.json

`--output PATH` writes the deterministic receipt. Normal and `python3 -O` execution use the same explicit exception checks and recursively type-exact receipt comparison. The writer and fresh read-only normal/optimized exact replays from `/` pass. No existing or frozen repository file is modified by this construction.
