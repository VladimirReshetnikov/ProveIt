# Independent source review of the auxiliary-product-only 83 chart

**PASS, with no finding.** The complete source has 83 live operations, comprising 46 multiplications and 37 additions/subtractions, 18 positive witnesses, and uniform exact degree 185. Supplying the auxiliary product independently preserves every parent zero but destroys the inherited representation: the square-preserving extension gives full positive zeros at every positive ordinary input. This is a refuted candidate, not a new universal bound.

## Frozen evidence and method

The reviewed author files are [source](complete83_auxiliary_product_collapse.py), [receipt](complete83_auxiliary_product_collapse.json), and [proof](complete83_auxiliary_product_collapse.md), with SHA256 pins:

| File | SHA256 |
|---|---|
| Author PY | `48cfce3e30fe2d1118a17b328962d987595dd604e37411c299ce8f7382b88a6c` |
| Author JSON | `0045c588a9053903c6e99a8362efa2ccef320bc5b057f2beda6419d0fc593af0` |
| Author MD | `a224d930f94a3888b4208147dc54d90127999342313120a5239e40408e948d50` |

I read the complete new helper and proof, the complete current84 proof, Sections 1–5 of the all-input82 proof, and the new [mathematical transfer review](review_complete83_auxiliary_product_collapse_math.md). The [fresh independent checker](review_complete83_auxiliary_product_collapse_source.py) authenticates the author trio and every one of the eleven dependency pins in its frozen receipt. It reads the parent arrays as JSON data and independently reconstructs the edit, full finalizer, liveness and coefficient expansions. No predecessor or archived Python was imported or executed. The author helper was executed only after its fresh generation passed.

The independent [receipt](review_complete83_auxiliary_product_collapse_source.json) contains the pins, small ledgers, coefficient hashes and monomial counts. It does not save the large expanded factor arrays. The full unbounded outer-family theorem is inherited from the pinned proof; this review does not repeat historical compiler verification.

## Literal source and all-value maps

The exact parent84 array loses only

    auxiliary_Tf = auxiliary_quotient * f.

Its consumer becomes `auxiliary_Tf_minus_one=auxiliary_product-1`; the supplied quotient name is replaced by the supplied product U. All other rows are identical, including `L16=f*f`, every retained use of f, every factor producer and all seven finalizer operations. The finalizer is precisely the product of the seven stated factors minus the paid discriminant Delta. The complete core costs 40M+36A, and the finalizer costs 6M+1A. The independent closure traversal reaches all 83 producers and all 25 supplied ports; the ordinary input and six fixed numeral ports are unchanged.

Literal row induction therefore proves, over every commutative ring,

    F83prod(U=T*f) = F84,
    F83prod(f,U) = F82(F_aux=f*f,U_aux=U).

The checker also reconstructs the entire82 array by removing the retained square and renaming U to the old product port, and checks the corresponding supplied-port sets. These are identities of whole polynomials, including every finalizer. No positive integral inverse T=U/f follows from either identity.

## Independent uniform coefficient calculation

All 25 supplied ports are independent formal variables in the fresh polynomial interpreter. The six fixed numerals have weight zero; the other nineteen ports have weight one. No numerical compiler specialization or equation imposed only at zeros is used. Expanding all seven actual factor producers gives:

| Factor | Exact degree | Full coefficient monomials |
|---|---:|---:|
| First | 22 | 70 |
| Main | 18 | 518 |
| Input | 32 | 1,175 |
| Auxiliary | 58 | 96,821 |
| Index | 7 | 19 |
| Transport | 2 | 16 |
| Scaled strong | 46 | 2,459 |

Thus 101,078 factor monomials were checked independently, including the main and input cancellations. Put Q=Bm1*Jrep, k=eta+zeta, gamma=rho+sigma, and

    Nt_top = w*(Q-F-Z-alpha-twice_cell_bits*x)-transport_quotient*Q.

The product of the seven independently extracted leading forms is the following 838-monomial polynomial:

    32*Q^111*h*gamma*delta^2*i^4*k^11*w^18*s^29
      *Nt_top*[k*s*U-(Q-F)*f^2]^2.

Here delta is the input witness, not the discriminant. The f-free monomial

    Jrep^112*h*rho*delta^2*i^4*eta^13*w^18*s^31
      *transport_quotient*U^2

has coefficient `-32*Bm1^112`. This remains nonzero for every valid fixed-program slice because Bm1>0, independently of the other fixed numerals. The final subtraction has degree 12 and cannot cancel this leader. The exact complete degree is therefore 185, not merely a diagnostic lower bound or the naive gate upper bound of 195. The fresh checker verifies every displayed factor leader, their complete product, the coefficient just exhibited, and the literal finalizer.

## Projection and complete-collapse proof challenge

The stronger sector equivalence in author Section 2 is valid, with its stated restrictions: fix the fourteen positive outer witnesses and a valid compiler slice, assume c is odd and R>0, and refresh all four auxiliary witnesses f,i,U,y. The literal polynomial factors as

    Delta*(P5*Na*Ns-1),
    Ns=f^2-Delta*i^2*c^4,
    Na=S^2*(V^2-y^2)+y^2,
    S=Delta*i*c^2, V=c*(U-1)-R*f^2.

Delta is positive before any zero equation and is 0 or 3 modulo 4. The unscaled strong factor Ns is never 3 modulo 4: it is a square if Delta=0 modulo 4 and a sum of two squares if Delta=3. The auxiliary factor is V^2 modulo 4 when S is odd, and y^2 when S is even. Cancelling positive Delta and using the integer product equal to 1 therefore forces Na=Ns=1 and P5=1. This argument does not infer unit values directly from a product equal to Delta.

Conversely P5=1 makes its main norm a unit. The same modulo-4 argument excludes its negative sign, and its literal positive root supplies c=psi_A(p) for the integer Pell base A>1. Set m=2cp, f=chi_A(m), z=psi_A(m), and i=z/c^2. The expansion of `(chi_A(p)+c*sqrt(Delta))^(2c)` proves c^2 divides z: the linear radical term contains 2c^2, and every higher odd term contains c^3. Thus i is positive integral, the retained square is genuine, and Ns=1.

For v congruent to R modulo c and to 3 modulo 4, the positive odd Pell quotient V=chi_S(v)/S is integral and congruent to -R modulo c. Since f^2 is 1 modulo c, U=1+(V+R*f^2)/c is positive integral, recovers the actual V expression and gives Na=1. Such v exists because c is odd. This establishes the stated iff while allowing all four auxiliary witnesses to change. It does not assert a projection with i fixed.

The pinned all-input82 proof constructs exactly the required positive outer tuples, with all five factors individually 1, c odd, R>0 and p>R, at each ordinary input on each inherited valid compiler slice. Its construction precedes its old auxiliary completion. The new extension therefore yields full positive zeros of this83 source, not just auxiliary components or failed witness inverses. No accepting computation is assumed. The failure of f|U on these tuples follows separately from the parent84 rank conclusion p=R if a positive inverse existed; it is not used to infer the language failure.

## Replay and limits

Fresh normal and optimized runs of the author helper from `/` reproduce the exact frozen author receipt. Its 14 positive auxiliary examples and 2,048 residue cases are bounded supplements, not materialized full compiler zeros. Fresh normal and optimized runs of the independent checker also reproduce its exact receipt. All executable checks use explicit exceptions and remain active under `-O`.

After installation beside the author and dependency files:

    python3 review_complete83_auxiliary_product_collapse_source.py --root /absolute/native-stream-queue --expect review_complete83_auxiliary_product_collapse_source.json
    python3 -O review_complete83_auxiliary_product_collapse_source.py --root /absolute/native-stream-queue --expect review_complete83_auxiliary_product_collapse_source.json

During review, `--author-dir /tmp` selected the frozen author trio while `--root` selected installed immutable dependencies. This is a bounded source/proof audit, with no public compiler API certification, no global operation lower bound, and no conclusion about unrelated83-operation candidates or independent-gamma83.
