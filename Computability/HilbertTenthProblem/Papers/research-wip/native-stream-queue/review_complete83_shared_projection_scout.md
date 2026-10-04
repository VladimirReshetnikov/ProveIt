# Independent source review: shared projection in 83 operations

**PASS within the declared source scope.** The emitted circuit has **83=46M+37A operations**, **18 positive witness coordinates**, and **exact degree187 on every inherited valid fixed-program slice**. Its all-ring forward identity with the frozen84 source is correct. This review does not establish a new universal83 bound or eliminate the missing divisibility condition from the inverse.

I read the complete fresh author helper and receipt, and the complete frozen84 companion and its source-review note as inert text. The reviewer executes only its own new code and interprets the emitted arrays as data. Neither author nor predecessor programs are run or imported.

## Complete source and identity

Write `a=R12`, `H=a4m5=4a+3`, and `U=shared_projection`. The edit replaces the old witness `rho` by U. It deletes the old `gamma_sum=rho+sigma` and `modulus_multiple=rho*H`, changes `gam` to `sigma*H`, and computes the main root as `(D1+U)+gam`. The input root becomes `exponent_partial+U`. Removing one multiplication and one addition, then inserting the main-root addition, gives a net saving of one multiplication.

The independent checker reconstructs all83 rows directly from the authenticated84 array, verifies the consumer sets of rho and both deleted intermediates, and checks all79 literally unchanged definitions. It checks unique registers, legal integer constants, dependency order, every live gate, all25 live free ports, the18-witness list, ordinary input x, all six fixed numerals and all seven factors. Every scalar multiplication in the emitted graph remains charged. The six factor-product gates and final subtraction of the actual discriminant A are checked literally, including the interleaved early products.

At the five named formal boundaries `D1,H,rho,sigma,exponent_partial`, separate exact sparse expansions prove

    D1+(rho+sigma)H = (D1+rho H)+sigma H,
    exponent_partial+rho H = exponent_partial+U  when U=rho H.

These are coefficient identities over the integers, hence over every commutative ring. The reviewer binds the formal atoms to the actual equal upstream expression IDs. U is bound to the actual expression `rho*a4m5`, using the authenticated paid H producer. It then interprets both entire DAGs using exact tuple interning, with the proved main-root cut normalized at its join. This proves **105 retained value equalities**, including every factor and the complete final output. The one common value excluded is `gam`, which intentionally changes; its complete consumer set rejoins at the proved main-root cut. No digest equality or sampled assignment is used as a substitute for algebraic equality.

Thus, for all supplied old coordinates and all fixed numeral values,

    F83(shared_projection=rho*(4a+3), other ports unchanged) = F84.

On the inherited positive interface, the unchanged upstream definitions give a>0 and H>0 before any equation is used. Consequently every old positive zero maps to a positive new zero. Conversely, a positive new zero with **H dividing U** gives the positive integer witness `rho=U/H` and hence an old positive zero. The unconstrained new source does not contain that divisibility requirement. No unrestricted positive inverse, same-coordinate zero equality, or ordinary-input universality claim follows from the forward identity alone.

## Uniform degree proof

All18 witnesses and x receive degree1; the six fixed-program numerals receive degree0. The reviewer treats the latter symbolically, rather than testing only sample compiler numerals.

The two norm cancellations are expanded from the actual emitted definitions. For the main norm, put `E=X+U+sigma H`, where `X=wn2` and `c=R10a`. Then

    (ac+E)^2-(a^2+H)c^2 = E^2+2acE-Hc^2.

For the input norm, put `kappa=index_rhs` and `E'=W+U`. Then

    (a*kappa+E')^2-(a^2+H)kappa^2
      = E'^2+2a*kappa*E'-H*kappa^2.

Independent sparse expansion checks all ten terms of the first expression and all six terms of the second against the source. These are the only places where the leading-form interpreter needs to replace a cancelling gate pair by an expanded identity. All other leading additions are checked not to cancel. The resulting exact factor degrees are

    22, 18, 32, 60, 7, 2, 46,

which sum to187; subtracting degree12 A cannot cancel that leading form.

Let

    Q0=Bm1*Jrep, k0=eta+zeta,
    C1=Q0-F-Z-alpha-twice_cell_bits*x,
    Ttransport=w*C1-transport_quotient*Q0,
    T=auxiliary_quotient.

The independent leading-form computation expands and verifies the whole84-term polynomial

    32 Q0^111 h sigma delta^2 i^4 k0^13 w^18 s^31
       *Ttransport*T^2*f^2.

In particular, after fixing the six compiler numerals, the monomial

    Jrep^112*h*sigma*delta^2*i^4*eta^13*w^18*s^31
       *transport_quotient*T^2*f^2

has coefficient **−32*(Bm1)^112**. The checker verifies that no other symbolic coefficient term merges into this monomial after the fixed numerals are specialized. It is nonzero on every admissible slice because Bm1>0. This proves the uniform exact degree187 without a generic-numeral or diagnostic-line assumption.

Twelve complete signed/rational evaluations, six using nonintegral rationals, additionally check 1,260 retained-value equalities. They support the symbolic proof but are not positive halting witnesses and are not its justification. No complete positive native witness tuple is materialized.

## Pins and replay scope

The source audit pins the author helper and receipt:

- `complete83_shared_projection_scout.py`: `2ff8bede5f08b0bc452ca50a432ebc6dbcad5ddd18bd5da5acc2b1d5b189ae9c`.
- `complete83_shared_projection_scout.json`: `dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c`.

The frozen84 parent PY/JSON/MD pins are recorded in the reviewer receipt. All are byte-authenticated; predecessor Python is never executed. The fresh review helper's normal writer and optimized exact replay pass. No repository or Git mutation, build, supplied script, predecessor replay, or external literature check occurs.

Reviewer helper: `/tmp/review_complete83_shared_projection_scout.py`, SHA256 `d1eb2d0182ad82a95d21264cfceb1b25cad8f2fd946463a0013013d1c78a540a`.

Reviewer receipt: `/tmp/review_complete83_shared_projection_scout.json`, SHA256 `4444d1af7e0c8f9161bb0b0f91e882e83566b07b1e1782e24179967bb8c9ae4e`.

The companion proof may address additional structural questions. This source review covers only the complete arithmetic, the all-ring forward map, its conditional inverse, and uniform exact degree; it supplies no new universal polynomial theorem.
