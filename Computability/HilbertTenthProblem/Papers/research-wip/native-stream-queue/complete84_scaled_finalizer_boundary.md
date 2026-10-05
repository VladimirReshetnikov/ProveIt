# Polynomial scaling cannot shorten this complete84 finalizer boundary

No gate saving is obtained. There is a precise new obstruction: after the exterior five-factor product has been computed, the entire residual needs at least **seven binary arithmetic gates**, even if it is multiplied by **any nonzero polynomial in the six available ports**. The original residual attains seven with 3M+4A. The resulting fully paid source is a rearrangement of complete84, still **84=47M+37A**, with its same 18 positive witnesses and degree187.

This is a restriction on a specified interface, not a lower bound for the full source. It allows mixing the final subtraction with the two norm factors and arbitrary polynomial output scaling. It does not allow additional exterior registers as operands, interleaving the exterior-product construction with the seven-gate computation, changing supplied coordinates, or replacing the residual merely by an unrelated polynomial with the same positive zeros.

## 1. Prior work and the new boundary

The actual saved `complete84_scaled_strong_output.json` and its proof were read inertly. The prior exact five-gate joint-factor bound fixes four squared/coefficient ports and targets the product of the two norms. The auxiliary nine-gate frontier concerns producing V, Q and the scaled strong factor from their roots. The older complete86 joint census covers a declared six-monomial partition/Horner grammar, and the85/155 deformation replaces the auxiliary coefficient using the strong unit equation. None is rerun here. This note instead allows a polynomial multiple of the **entire product-minus-discriminant residual**, including its final subtraction.

Use these six already paid source values as the only nonscalar inputs of the new cut:

| Formal symbol | Actual value or producer |
|---|---|
| P | `norm_triple * norm_index * norm_transport` = P5 |
| U | `scaled_f_square` = Delta*f² |
| Q | `R16` = S², S=`aux_coefficient_root`=i*Ac2=Delta*i*c² |
| A | `H2` = V², V=c(Tf−1)−R*f² |
| B | `aux_y2` = y_aux² |
| D | source register `A` = Delta=(a+1)(a+3) |

Formal A and B in this table are squared ordinate ports; neither is the source discriminant register or a radix. P is **not** a free new witness or an existing free register: its two multiplications are paid separately below. All roots, squares, quotient producers, main-norm consumers and supplied coordinates remain in the source.

The target is

    F = P*(U−Q)*(Q*(A−B)+B)−D.                         (1)

For every nonzero polynomial H in k[P,U,Q,A,B,D], we consider computing H*F. Here k is any characteristic-zero field, arbitrary scalar constants are allowed, and each binary addition, subtraction or multiplication costs one gate. Division and fused operations are absent. The lower bound applies whether or not a chosen multiplier preserves the relevant zero set.

This scaling family contains meaningful zero-preserving possibilities. On the actual strictly positive integer domain, Delta>0 and Q,U>0 before any equation is imposed. Also U−Q is nonzero: Delta lies strictly between the consecutive integer squares (a+1)² and (a+2)², so Delta*f²=S² with positive integers f,S is impossible. Likewise Na=Q(A−B)+B is nonzero, since Na=0 would give (S*V)²=(S²−1)y_aux², whereas the literal source gives S=i*Delta*c²≥8, and S²−1 is nonsquare. Thus multiplication by D, Q, U, U−Q or Na would preserve the whole supplied positive integer zero set. These observations supply no free division and do not simplify the gate obligation for the resulting polynomial.

## 2. Four additions are unavoidable, also after scaling

For a polynomial g, write Newt(g) for the convex hull of its exponent support. Start with scalar constants and monomial input ports. In a circuit with a additions/subtractions, the support of every nonzero register lies in an affine coset of one common vector space of dimension at most a. This follows by induction: multiplication adds two cosets without enlarging their direction space; addition takes the union of two cosets, requiring at most one new direction, the difference of their offsets. Cancellation only deletes support points. Zero registers cause no problem. Consequently

    additions(g) >= affine dimension of Newt(g).        (2)

Expand (1):

    F = P U Q A − P U Q B + P U B
        − P Q² A + P Q² B − P Q B − D.                 (3)

Its support has affine dimension four. For an explicit independent minor, use exponent-coordinate order (P,U,Q,A,B,D), base point P Q B, and the support points P U Q A, P U Q B, P U B and D. On the coordinate columns P,U,Q,A their four differences form

    [ 0  1  0  1 ]
    [ 0  1  0  0 ]
    [ 0  1 −1  0 ]
    [−1  0 −1  0 ],

whose determinant is nonzero. The dimension is at most four because every support point satisfies P-exponent+D-exponent=1 and A-exponent+B-exponent−P-exponent=0.

For nonzero polynomials over a field,

    Newt(H*F) = Newt(H) + Newt(F).                       (4)

For completeness, a generic linear weight selects unique vertices on each factor's support; their product coefficient is nonzero and exposes the corresponding sum vertex. Varying the generic weight gives all vertices of the Minkowski sum. This proves (4), including cases with cancellation among other terms. The sum contains a translate of Newt(F), obtained by fixing any point of Newt(H). Its affine dimension is therefore at least four. Equations (2)–(4) prove that **every nonzero H*F needs at least four additions/subtractions**. This is not an enumeration of selected multipliers.

## 3. Three multiplications are unavoidable

The degree of F is four, with highest homogeneous part

    F4 = P*Q*(U−Q)*(A−B).                              (5)

Its four linear factors are pairwise nonassociate. Thus F4 is not a scalar multiple of a polynomial square.

With at most two multiplication gates, allowing arbitrary additions freely cannot produce a quartic with this leader. Before the first multiplication all registers are affine. To obtain degree four, that product must have degree two, and both operands of the second multiplication must have quadratic leading parts proportional to that same first quadratic leader. Hence the second product's quartic leader is a scalar times its square. Later additions either preserve a scalar multiple of that quartic leader or remove the second product's contribution entirely, leaving degree at most two. Neither case produces (5). Therefore F, and every nonzero constant multiple of F, needs at least three multiplications.

If H is nonconstant, the integral-domain degree law gives

    degree(H*F) = degree(H)+4 >= 5.

Two multiplications produce degree at most four regardless of the number of additions or reused intermediate registers. Thus nonconstant H*F also needs at least three multiplications. Together with Section2:

> Every nonzero polynomial multiple H*F needs at least 3M+4A, hence at least seven gates, in this six-port model.

The statement means separate lower bounds M≥3 and A≥4; it does not say that every multiplier attains seven. The seven-gate schedule for H=1 is

    strong = U−Q
    gap = A−B
    weighted_gap = Q*gap
    auxiliary = weighted_gap+B
    joint = strong*auxiliary
    scaled = P*joint
    residual = scaled−D.

Thus the minimum across all permitted nonzero polynomial multiples is exactly seven. No positivity assumption or unit equation enters this circuit bound.

## 4. Binding the formal ports to the actual source

Treating the six cuts as formally independent does not invent a relation-free source that the real six cuts fail to satisfy. On any valid fixed-program slice, the six actual cuts are algebraically independent over the field generated by the other dynamic supplied ports, with s,f,i,T,y_aux,tau_root omitted. This assertion concerns polynomials in the remaining variable ports, not a fixed numerical tuple, and it does not grant access to the other75 computed registers.

One direct triangular argument orders the six variables as

    s, f, i, T, y_aux, tau_root

and the six cuts as D,U,Q,A,B,P. With the other supplied ports as coefficients:

- q and X=wq are independent of these six variables; Y=s*q³, so a=Y(X+1) is nonconstant linear in s. Hence D=(a+1)(a+3) is nonconstant in s.
- U=D*f² has nonzero leading coefficient in the next new variable f.
- Q=D²*i²*c⁴ has nonzero leading coefficient in the next new variable i, with c=kY+eta a nonzero polynomial in s.
- A=[c(Tf−1)−R*f²]² has nonzero leading coefficient c²*f² in the next new variable T. R may depend on the other supplied data but not on T.
- B=y_aux² introduces the next new variable.
- P=(tau_root²−first_product)*Nmain*Ninput*Nindex*Ntransport has nonzero leading coefficient in tau_root. The last four factors are nonzero polynomials: for example their displayed source definitions have nonzero quadratic coefficients in sigma or rho, or nonzero linear coefficients in h or transport_quotient, respectively.

Successively comparing highest powers of each new variable proves that substitution of these cuts cannot annihilate a nonzero polynomial in the six formal ports. This is the elementary triangular-polynomial independence argument; it requires no numerical native zero. Positivity is unnecessary for it, though the valid recipe ensures nonzero radix constants.

The source has additional paid registers containing roots and products of the cuts. Giving such registers to the circuit would change the model. The independence observation does **not** exclude using them to save a gate, and does not turn the seven-gate cut result into an unrestricted source lower bound.

## 5. Complete static source and paid ledger

The new receipt reads the full original84 array only as inert data. It guards the literal discriminant, quotient, coefficient, squared-ordinate, exterior-factor and nine replaced definitions. It preserves the other75 rows literally, and appends the two paid products

    boundary_p5_index = norm_triple*norm_index
    boundary_p5 = boundary_p5_index*norm_transport

followed by the seven-gate schedule of Section3. These two products cannot be supplied for free: in the original source the exterior factors are interleaved with Na in the product chain. Within the present protected two-stage model, forming the product of the three available exterior factor ports requires two binary multiplications. No interleaving or donor reuse beyond that model is claimed to be excluded.

| Part | M | A | Total |
|---|---:|---:|---:|
| Literal retained prefix |42|33|75|
| Paid P5 construction |2|0|2|
| Complete six-port residual |3|4|7|
| Fully paid source |47|37|84|

All84 rows and all25 supplied ports are live. The six fixed numerals, ordinary input and18 positive witnesses are unchanged. Expansion of the **new nine-row finalizer only** at its eight original ports gives precisely the original complete product-minus-Delta expression. Literal preservation of all other definitions lifts this identity through the source. Consequently the polynomial, all its zero tuples, inherited positive-domain universality and exact degree187 remain unchanged for this attaining H=1 schedule. There is no new lower-count source or new degree theorem.

The restriction is consequently complete but narrow: any approach that retains this75-row prefix, separately purchases P5 by the two products, and then computes a nonzero polynomial multiple at just the six ports cannot reach83. A strategy that shares a P5 intermediate, uses an extra computed root, changes factor producers, uses a rational chart with a justified integral inverse, or proves a different positive-zero equivalence is outside it.

## 6. Evidence and limits

The fresh standard-library helper records the complete attaining84 array, prefix/tail ledger, liveness and literal source guards. Its new polynomial arithmetic verifies the seven-term residual, quartic leader, exact support rank, full finalizer cut identity and a few non-exhaustive multiplier illustrations. The all-multiplier theorem is the proof in Sections2–3, not a finite search or a claim of formal machine verification. The original saved arrays and helpers are never evaluated or imported; no old helper or copied source program runs. No huge native zero, numeric compiler fixture or supplied program is materialized.

The six inert source/proof pins are recorded in the receipt: actual84 JSON/MD, joint four-port bound, auxiliary nine-gate frontier, old86 joint census and85 reduced-degree proof. The old internal finalizer note was read as background; this proof and receipt do not depend on its execution or inclusion. The fresh normal and optimized executions from `/` passed and produced byte-identical receipts before freeze. Outputs are exclusively created in `/tmp`; no repository file is modified.
