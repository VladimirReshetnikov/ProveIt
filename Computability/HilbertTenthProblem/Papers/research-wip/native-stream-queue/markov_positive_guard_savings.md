# Positive guards remove the Boolean residual from the Markov counter graphs

The ZERO/DEC selector is already forced by the other equations and the **strictly positive integer** domain. Removing its separate Boolean residual improves the direct one-step polynomial from12 to **8=3M+5A**, and the linked homogeneous one-step polynomial from26 to **22=11M+11A**, without new witnesses. The complete fixed-duration sources improve from13T+3 to **9T+1** in direct coordinates and from19T+4 to **15T+2** in homogeneous coordinates, saving4T+2 gates in each family for every fixed T≥1.

This is an arithmetic improvement to the two-action counter example, not to a universal compiler. Both history families still recognize exactly the positive inputs x≤T. Their numbers of coordinates and rows grow with T; no fixed-arity unbounded-history or operation-minimum claim is made. Root supplied the redundant-Boolean observation and the history counts; this packet independently binds the domains, constructs the complete arrays and verifies their algebra and ledgers.

## 1. Prior interface and scope

The frozen `markov_projective_counter_step.md` uses counter hats C=c+1 and the actions

- ZERO: C=1 and C'=1;
- DEC: C≥2 and C'=C−1.

Its separate selector equation was `(B−1)(B−2)=0`. Its matrix masks represent the homogeneous identity and decrement matrices divided by a fixed q. The older cosine lift has q=7, while the accepted sine lift realizes the same matrices with q=5. Every multiplication by either fixed numeral remains charged here. The arithmetic proofs below work for any fixed integer q≥2; only q=5 and7 are tied to these particular mask constructions.

The prior counter-guard scan also read `residue_affine_factored_counter_step.md`. That result bounds a finite selector using an **additional positive complementary witness**, and handles a prime-encoded counter program through divisibility conditions. It does not give the no-new-witness ZERO/DEC elimination used here. The projective scale and the initial integrality requirements from the old Markov packet are retained.

## 2. Exact direct graph: eight gates

Supply strictly positive integers C,C',B. Put

    t=B−2, u=C−1,
    z=t*u, r=C'−u+t.

Use the polynomial `F=z²+r²`. If F=0, both residuals vanish. When u=0, the transition gives C'=−t>0, while t≥−1 is an integer; hence t=−1, B=1 and C=C'=1. When u≠0, the zero guard gives t=0, B=2, and C'=u=C−1>0, so C≥2. These are exactly ZERO and DEC. Conversely each legal labelled step makes both residuals zero. This proves equality of the complete positive-integer graph, not just its projection on endpoints.

The literal source is

    u=C−1; t=B−2; z=t*u;
    partial=C'−u; r=partial+t;
    zz=z*z; rr=r*r; F=zz+rr.

The residual producers cost1M+4A; two squares and one join give **3M+5A=8**. Only B is existential at the supplied endpoints C,C'. The exact degree is4, since z² has nonzero quartic leader B²C².

The old transition `C'−C+B−1` is exactly r. Thus, as an all-value polynomial identity,

    F_old = F + [(B−1)(B−2)]².                        (1)

These are different polynomials, with the same zero tuples on the specified positive-integer domain. The Boolean equation is recovered by the proof above, not discarded without replacement.

**Remark 1 (essential domain).** Strict positivity and integrality cannot be weakened silently. The new residuals vanish at `(C,C',B)=(1,2,0)` if B=0 is admitted, at `(1,0,2)` if C'=0 is admitted, and at `(1,1/2,3/2)` for positive rational selectors. None is a legal integer counter step. These are boundaries of the theorem, not errors in the positive-integer graph.

## 3. Homogeneous local graphs and integer linkage

First supply strictly positive integers X,H,X',H',B. Put

    t=B−2, u=X−H,
    z=t*u,
    r=qX'−u+tH,
    s=qH'−H.                                         (2)

Use `F_raw=z²+r²+s²`. When u=0, r=0 forces t<0, so B=1 and t=−1; the scale equation then gives X=H and X'=H'. When u≠0, z=0 forces B=2; r=0 gives u=qX'>0, and the scale equation gives

    X'/H' = X/H−1.

This proves exactly the two guarded positive-ratio actions. It does **not** make arbitrary ratios of positive supplied integers integral.

The producers in (2) cost4M+5A: `t`, `u`, `z`, `tH`, `qX'`, two transition additions, `qH'`, and the scale subtraction. Three squares and two joins give **14=7M+7A**, degree4, with one positive selector witness B at the four supplied homogeneous endpoints.

For the same integer-counter endpoint interface C,C' as the old26-gate local packet, append both paid residuals

    L=X−HC,  L'=X'−H'C'.                              (3)

Each link adds one product, one subtraction, one square and one join to the common SOS. The complete linked graph therefore costs **22=11M+11A**, degree4, with exactly the old five positive auxiliaries B,X,H,X',H'. The links give integral endpoint ratios and reduce the preceding proof to the direct ZERO/DEC graph. Conversely every direct legal step lifts by any positive H', with `H=qH'`, `X=HC`, `X'=H'C'`.

The linked source uses the homogeneous zero residual t(X−H), whereas the old packet used t(C−1). They are equivalent when L=0 and H>0, but are not the same polynomial off that locus. Write `z_old=t(C−1)` and `b=(B−1)(B−2)`. The exact full-output correction is

    F_linked_new−F_linked_old
      =(H²−1)z_old²+2HtLz_old+t²L²−b².                (4)

This follows from `z=H*z_old+tL`; the other link, transition and scale residuals agree. The helper verifies (4) coefficientwise. Same positive zeros are established by the full local proof, not inferred from a nonexistent all-value equality.

**Remark 2 (unlinked ratios and raw scale).** The14-gate graph admits `(X,H,X',H',B)=(3q,2q,1,2,2)`, with ratios3/2 and1/2. This is not an integer-counter step. The linked graph or the integral initialization below is necessary. Also every raw step has H=qH', so fixing H=1 would exclude all positive integer successors for q≥2. The graph uses a freely scaled input ray; it does not normalize the raw Markov output at no cost.

## 4. Complete direct histories

Fix T≥1. The ordinary input x is a strictly positive integer. Supply the same2T positive witnesses as before:

    C_1,...,C_T, B_0,...,B_(T−1).

Mathematically the initial hat is C_0=x+1. Its only needed difference is `u_0=C_0−1=x`, so no initialization addition or subtraction is emitted. For j≥1 emit `u_j=C_j−1`. At every step use

    t_j=B_j−2,
    z_j=t_j*u_j,
    r_j=C_(j+1)−u_j+t_j.

Add the endpoint residual C_T−1, square all2T+1 residuals and join once. The general ledger is

| Direct-history block | M | A |
|---|---:|---:|
| Step residuals, with u_0=x |T|4T−1|
| Endpoint |0|1|
| 2T+1 squares and2T joins |2T+1|2T|
| **Complete source** |**3T+1**|**6T**|

Hence the cost is **9T+1**, exact degree4, with2T positive witnesses. The highest-degree square of the first guard contains B_0²x². Other squares cannot cancel all highest real homogeneous terms.

Applying Section2 inductively gives exactly the legal counter path: decrement while positive, then stay zero. Thus a zero exists precisely when x≤T. The counter hats and selectors are unique for an accepted x. Conversely the path `C_j=max(x−j,0)+1`, with B_j=2 while x>j and B_j=1 otherwise, satisfies every step and the endpoint precisely in that range.

On identical supplied coordinates, the old initialized polynomial and this new polynomial obey (1) summed over all T selectors. The exact SOS relation is therefore

    F_direct_old = F_direct_new + sum_j b_j²,
    b_j=(B_j−1)(B_j−2).                                (5)

Its reverse zero implication uses strict positivity as above. The old13T+3 schedule loses2T multiplications and2T+2 additions, giving the complete4T+2 saving. No deterministic first-DEC substitution or selector-witness elimination is used in this ledger.

## 5. Complete homogeneous histories

Supply the same3T+1 positive witnesses as the old raw history:

    H_0, X_1,H_1,...,X_T,H_T, B_0,...,B_(T−1).

The implicit initial numerator is `X_0=H_0(x+1)`. The first guard and transition need only

    u_0=X_0−H_0=H_0*x,

computed by one multiplication. For j≥1 emit `u_j=X_j−H_j`. At each step use (2) with those u_j, and add X_T−H_T as endpoint. There are no supplied intermediate counter quotients and no uncharged X_0 row.

The positive-integer proof of Section3 forces B_j=1 or2 at every step. The scale and numerator equations give

    X_(j+1)/H_(j+1) = X_j/H_j−(B_j−1),

where at j=0 the right initial ratio is exactly x+1. Thus every subsequent ratio is integral by induction. Its strict positivity makes it an integer hat at least1, and the homogeneous guard has the direct ZERO/DEC meaning. The endpoint ratio is1. This proves soundness for **every** positive integer assignment to the supplied ports.

Conversely, for the legal direct path and any positive H_T, set

    H_j=q^(T−j)H_T,  X_j=H_j*C_j.

All supplied coordinates are positive integers and satisfy the new residuals. These are witness-existence formulas at a fixed duration, not a free POWER gate or a variable-length computation hidden in the source. Every zero necessarily has `H_0=q^T H_T`. Thus the homogeneous language is also exactly x≤T, with a positive scale fiber rather than a unique full witness tuple.

| Homogeneous-history block | M | A |
|---|---:|---:|
| u_0=H_0*x and all step residuals |4T+1|5T−1|
| Endpoint |0|1|
| 3T+1 squares and3T joins |3T+1|3T|
| **Complete source** |**7T+2**|**8T**|

The total is **15T+2**, saving4T+2 against19T+4, with unchanged3T+1 witnesses. The exact degree is6: the first guard is `(B_0−2)H_0*x`, and its square has monomial B_0²H_0²x² with coefficient1. All other residuals have degree at most2, so they cannot cancel that degree6 leader. Formula(5), with the raw history polynomials, holds as well after the literal initialization substitution; it is checked at the full polynomial level.

Relative to the improved direct history, this homogeneous schedule still costs6T+1 more operations and T+1 more positive witnesses, with higher degree. Changing q=7 to the legitimate q=5 sine lift changes the scale size, not these paid counts. The matrices and masks supply no universal language claim for this two-action example.

## 6. Full arrays, evidence and boundaries

The new standard-library helper emits fourteen complete arrays, totaling368 paid rows: direct local; raw unlinked and linked local for q=5,7; direct histories T=1,2,4; and raw histories for both q at those durations. Every row and supplied port is live. It independently expands all new residuals and full SOS outputs as sparse integer polynomials, checks their exact degrees against the formulas, and verifies the old/new mathematical corrections (1), (4) and (5). The old saved arrays are parsed only for declared ports and ledgers; they are never evaluated, reconstructed for execution or imported.

Fresh bounded tests cover384 direct local tuples,71,680 homogeneous local tuples,1,080 linked cases with true and false guards/transitions,80 constructed history assignments including x>T,35 valid histories and622 single-port rejection perturbations. They also evaluate both numbered domain boundaries on the **new** arrays. These checks supplement the unrestricted positive-integer proofs and all-T ledgers; they are not evidence for universality or an operation lower bound.

The exact pinned context is:

| Inert file in native-stream-queue | SHA-256 |
|---|---|
| `markov_projective_counter_step.md` | `01003a2063d442fa71d4a5e80dfd8218edb7940c22fcc90d6b847079fd63a5d2` |
| `markov_projective_counter_step_checks.json` | `ec34cd98a4330ba04c90c7304bc446950bb85ddbc206771684f1159aec678396` |
| `review_markov_projective_counter_step.md` | `8945e419b6349660e74929194f298d078bcabde58cea7f098aaceb2bb131c986` |
| `residue_affine_factored_counter_step.md` | `60250f0f6d12f7583b5de747c82d0d91205eab98ca0f4095992d458aaf8a951f` |
| `markov_sine_lift.md` | `7b30acebde3c5576773e92030242e4e8db1d00530fa9d7733b4ac8796270d1b2` |

The old counter note, its proof review and the residue-affine counter note were read in full; the sine-lift interface was read through line145. No source, archived, supplied, predecessor or frozen helper/build was executed or imported. Only newly authored graph code and mathematical checks ran. All files were authored in `/tmp`, and no repository/Git object changed. Fresh ordinary and optimized executions from `/` passed and produced byte-identical receipts before freeze.
