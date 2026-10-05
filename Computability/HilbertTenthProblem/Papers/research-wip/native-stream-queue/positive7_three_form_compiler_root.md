# A complete positive7 compiler with three selected forms per relator sign

For r>=1 fixed presentation relators, the complete positive7 compiler now selects three nonnegative forms per signed relator slot instead of four raw coordinates. The two signs share their computed form inputs. This reduces the selected-field count to 52+6r and the prescribed native lane count to ell=62+8r. With lambda(t)=floor(log2 t)+popcount(t)-1, the certificate costs

    (277+50r+lambda(ell))M+(550+62r)A.

Its 23 comparisons require 23M+45A for one combined finalizer. The complete polynomial therefore costs

    (300+50r+lambda(ell))M+(595+62r)A
      =895+112r+lambda(62+8r) operations,                  (1)

with 96+8r positive existential coordinates. Relative to the preceding complete plane compiler, the exact operation saving is

    10r-1+lambda(62+10r)-lambda(62+8r),

and there are two fewer positive witnesses per relator. The changed relation preserves ordinary-input projection through a new simultaneous state/form proof; it does not preserve the old full witness tuple or final polynomial.

For r=0 use the unchanged preceding 903-operation, 96-witness source. There is then no relator form to compute or select. Formula (1) is stated only for r>=1. The actual universal presentation and its numerical r remain unmaterialized, so neither branch gives a new numerical universal bound. The complete general84 result remains unchanged.

## 1. Fixed integer recipe for shared positive forms

The [three-form selection proof](positive7_three_form_relator_selection_pascal.md) gives a common integer row basis for each fixed relator matrix P=[p,q;s,t] in SL2(Z) and its inverse. In the inherited three-coordinate congruence representation, the right invariant is w0=(2q,p-t,-2s). For noncentral P, normalize it to a primitive vector and use the integer-plane Bezout construction, transposed, to obtain two integer rows u,v spanning all integer rows orthogonal to that invariant. Undo any preparatory coordinate permutation in u,v. There are fixed integer matrices E_plus,E_minus of size 3 by 2 with

    S(P)-I3=E_plus*[u;v],
    S(P^-1)-I3=E_minus*[u;v].

For P=I or -I use u=(1,0,0), v=(0,1,0) and both E matrices zero. This supplies the same uniform source shape without normalizing a zero vector. Gcd, Bezout and exact integer division occur only while preparing fixed numerals.

Use C=[1,0,0,-1;1,1,0,-2;2,0,1,-4], the existing decoder on H4,H5,H6,H7. For each of the two rows ell_j=(u or v)C, choose

    lambda_j=1+max(0,-min_i ell_(j,i)),
    a_(j,i)=ell_(j,i)+lambda_j >=1.

Compute S4=H4+H5+H6+H7 and the two positive form words

    A_j=sum_(i=4..7) a_(j,i)H_i = ell_j H_(4,5,6,7)+lambda_j*S4.

Each A_j is shared by the positive and inverse slots of that relator. Fix M>=1 bounding every a_(j,i) over all relators. The same full positive7 alphabet has common column mass Cmass. Choose a fixed dyadic K>max(Cmass,8+2r,3M+1). The existing kappa_minus_one and program-slice alpha,gamma keep their previous meanings.

The new fixed roles are eight positive form coefficients, two positive offset coefficients and twelve signed E coefficients per relator, plus the shared form_bound M. With alpha,gamma,K,kappa_minus_one there are 5+22r named roles. They must all follow this actual-relator recipe. They are not independent existential choices. Every runtime multiplication by any such role is charged, including zero and unit E coefficients.

## 2. Paid field interface, weighted bound and native call

The eight paired letters retain the preceding 52 raw-coordinate selected fields and the exact 198-row paired action. Each signed relator slot instead supplies positive hats for selected(S4), selected(A1), selected(A2), in that order, indexed 0,1,2. Their raw values are the three hats minus one. There are 52+6r raw selected fields in total; all are explicitly un-hatted and included in Ztot.

The positive supplied coordinates are seven histories H_i, six terminals F_i with terminal 7 aliased to F_1, 8+2r selector hats, 52+6r selected-output hats, two slacks, and 21 freshly named native auxiliary witnesses. Their total is 96+8r. The input remains ordinary x>0, with the inherited computed positive initial vector z=(3,tau,tau^2,2,tau,tau^2,1) and mass S0=2tau^2+2tau+6.

The source computes J as the sum of raw selectors, D=S0+height_slack, B=KD, P_outer=(B-1)J+1 and mu=(D-1)J. It shares the six additions for the full and subset masses explicitly:

    S4=(H4+H5)+(H6+H7),
    S=((H1+H2)+H3)+S4.

This is the same six-addition cost as the old seven-coordinate sum; no separate three-addition S4 producer is charged. The global comparison becomes

    M*S+Ztot+global_slack=P_outer.                         (2)

Its one multiplication by M is paid. The following two additions have the same count as before.

For every relator sign sigma, the three new lane triples are

    (S4,(B-1)S_sigma,Z_sigma,0),
    (A1,(B-1)S_sigma,Z_sigma,1),
    (A2,(B-1)S_sigma,Z_sigma,2).

All Boolean selector lanes, raw paired-letter lanes, aggregate lane (S,mu,S) and height lane (D,D-1,0) retain their meaning. The three packs use radix P_outer and exactly ell=62+8r lanes. Independent Horner schedules cost (3ell-4) of each operation type, since only the highest literal zero of the output pack is omitted. The prescribed scale T=P_outer^ell costs lambda(ell) multiplications.

The complete native certificate still contains 64 rows, 15 comparisons and 21 positive witnesses. Its private header composes raw packs using 16A_pack+12,16M_pack+10,16Z_pack+8 and q=16T; the remaining 57 rows are exact prefixed parent records. Native scale and packs are rebound to the new lane schedule; no old prescribed scale is reused accidentally.

All raw selected outputs and selectors are nonnegative on positive supplied assignments, and all A_j and S4 are positive. Thus the packed native arguments are nonnegative even before imposing (2). On a zero, (2) yields P_outer>1,J>=1,B<=P_outer, and M*S<P_outer. Since 0<S4<=S and 0<A_j<=M*S4<=M*S, every formed input is below P_outer. Selected outputs, ordinary histories, selectors and masks have the same required bounds. This gives native pretyping before any formed-digit interpretation.

The prescribed native theorem yields dyadic P_outer; the height lane gives dyadic D and B. Repunit divisibility gives P_outer=B^n and J=sum_(j<n)B^j for n>=1. The Boolean lanes and checksum, with 8+2r<B, then establish exactly one selected letter per cell. The new lanes select canonical digits of the formed whole integers. They do not yet prove that those digits equal the corresponding linear forms in individual history digits.

## 3. Action recovery and the simultaneous induction

For a signed relator slot compute the two signed selected forms

    T_sigma,j=Z_sigma,j-lambda_j*Z_sigma,0, j=1,2.

Append the three coordinates of E_sigma*(T_sigma,1,T_sigma,2) to the current d,e,f increment accumulators. The eight paired-letter action is unchanged. The same positive7 baseline and fused postprocessor enforce all seven recurrences

    B*V_i=H_i+P_outer*F_i-z_i, i=1,...,7.

When formed digits agree with their intended linear expressions, uncentering and the fixed factorization recover exactly the actual relator difference. Signed intermediate values are allowed, but none is supplied as a positive witness or used as a positive native input.

The proof establishes the needed formed-digit interpretation together with the genuine history. First reduce the recurrences modulo B. Since the initial mass S0<D<B, each lowest history digit equals the corresponding z_i. There is no incoming carry. The S4 digit is its true subset mass; each A_j digit is at most M*S0<MD<B and so equals its true linear expression without a carry. The selected forms now yield the genuine positive action at that cell, whose next total is at most Cmass*S0<B.

Inductively, subtract already recovered lower coefficients from the recurrences. The preceding genuine positive action has total at most Cmass(D-1)<B, so reduction modulo B recovers the next canonical history digits. Previous totals were below D, hence there is no lower carry in S. The current total is already below B, so the aggregate native lane S AND((D-1)J)=S forces it below D. Only then interpret the current formed digits: previous formed coefficients had no carry, and each new one is bounded by M(D-1)<B. Thus their canonical digits match their intended forms. Uncentering recovers the actual action for the next step.

This recovers all pre-states, all relevant form digits and the genuine terminal from the top recurrence coefficient. The argument does not assume linearity of selection, positivity of arbitrary signed action intermediates, or a duration-dependent height bound. The shared F_7=F_1 port imposes the same endpoint condition. Initial coordinates 3 and 1 differ, so no accepting empty word is omitted.

Conversely, for an accepted word choose dyadic D above the masses of its actual states. The bounds K>M and K>Cmass make the history and formed words carry-free at their intended cells. Supply their canonical selected outputs with positive hats. At a paired-letter cell the retained total is at most the state mass; at a relator cell S4+A1+A2 is at most (2M+1) times that mass. Consequently

    Ztot<=(2M+1)S, S<=(D-1)J,
    global_slack=P_outer-M*S-Ztot
      >=[(K-3M-1)D+3M]J+1>0.

All prescribed native identities and bounds then hold, and its converse supplies positive auxiliary witnesses at the new packs and scale. This proves the same accepted-word/ordinary-input projection. The changed fields, new K choice, slack and native packs can require different witnesses; no same-tuple correspondence with the old source is claimed.

## 4. Exact complete-source cost

The positive form producers cost 8M+6A per relator. For each sign, uncentering costs 2M+2A and the 3-by-2 action appends cost 6M+6A: each of its six products is added to its designated existing accumulator. Thus the two signs together cost 16M+16A, in addition to their shared form producers. This pays every offset subtraction and accumulator addition.

| Stage | M | A |
|---|---:|---:|
| Input, mass, geometry, masks and weighted bound | 14+2r | 134+16r |
| Shared positive form producers | 8r | 6r |
| Three formed-input packs | 182+24r | 182+24r |
| Fixed native power | lambda(ell) | 0 |
| Complete native certificate | 33 | 31 |
| Paired action, formed relator appends and fused lift | 42+16r | 189+16r |
| Seven recurrence right sides | 6 | 14 |
| Certificate | 277+50r+lambda(ell) | 550+62r |
| Single combined finalizer | 23 | 45 |

Every comparison residual is charged. The six terminal products still serve seven right sides through F_7=F_1, and the fused action outputs already contain their B factors. The exponent ell changes, so lambda need not change monotonically; the exact difference displayed above includes both binary-chain costs.

| Formal r | ell | lambda | Certificate operations | Polynomial operations | Positive witnesses |
|---:|---:|---:|---:|---:|---:|
| 1 | 70 | 8 | 947 | 1015 | 104 |
| 2 | 78 | 9 | 1060 | 1128 | 112 |
| 3 | 86 | 9 | 1172 | 1240 | 120 |
| 4 | 94 | 10 | 1285 | 1353 | 128 |
| 8 | 126 | 11 | 1734 | 1802 | 160 |

The receipt saves full graphs for r=1,2,4, totaling 3496 rows. The r=3,8 entries are shape censuses, not additional saved graphs. Its r=0 fallback points to the unchanged predecessor source and compact row digest; it adds no unused S4 computation. No finite row census establishes universality or replaces the all-r stage and positive-projection proofs.

## 5. Frozen evidence and numbered boundaries

The original metadata-only emitter `positive7_three_form_compiler_root.py` is 12970 bytes and 249 lines, SHA256 `7d615b6ab34cf186a8858bd22c2c36c6816a7b72a21c2deee701d342789707b1`. Its first receipt `positive7_three_form_compiler_root.json` is 462049 bytes and 24284 lines, SHA256 `8c056b9fc7b75c79677332e5dafac8de7130a2530cc79ae2fc300c862efed195`. Both are frozen after one original emission and must not be replayed.

The builder reads the pinned complete plane receipt and pinned 198-row paired cut only as inert records. It constructs the changed geometry, positive forms and append rows from the new specification, rebinds the native header, and reuses the 121-row recurrence/finalizer suffix with exact increment-name bindings. Every saved row and supplied coordinate is syntactically live, topologically closed, and counted by operation label. No source or coefficient arithmetic, native witness test, degree propagation or predecessor-code execution occurs.

The [independent selection proof review](review_positive7_three_form_selection_aristotle.md) checks the new induction, weighted completion and local costs. The [complete-source review](review_positive7_three_form_compiler_riemann.md) independently binds the new rows, roles, lane meanings, unchanged native core, suffix consumers and full count. External group-universality and native foundations remain inherited dependencies.

**Review remark 1 (selection is not unconditionally linear).** At B=8 and raw history values (5,1,1,1), S4=8. Selecting the lowest cell gives S4 AND7=0, whereas selecting the four values separately and adding gives 8. This refutes a naive unconditional interchange of form computation and selection. It is a local counterexample, not a full compiler zero. The simultaneous induction supplies the no-carry conditions actually needed here.

**Review remark 2 (the old sparse mass bound does not transfer).** The earlier raw-coordinate interface used Ztot<=S. A single formed relator cell on seven ones has S=7 and S4=4; both positive forms have four coefficients at least one, so S4+A1+A2>=12>7. Thus the old bound is false for the new interface. The weighted comparison (2) and Ztot<=(2M+1)S are essential to its completeness proof.

**Review remark 3 (scoped obstruction to two positive homogeneous forms).** For noncentral P, S(P)-I has rank two: if q is nonzero a minor is 2q^2, and if s is nonzero another is 2s^2; q=s=0 would force P=I or -I over the integers. Since C has a unimodular three-column submatrix, W=(S(P)-I)C has rank two and annihilates the positive vector (1,1,2,1). If W factored through two homogeneous linear forms nonnegative on every positive integer four-vector, those forms would have nonnegative coefficients and span the row space of W. Both would then annihilate a strictly positive vector and hence be zero, contradicting rank two. This excludes that precise unconditional homogeneous interface; it is not a lower bound for guarded, affine, nonlinear or state-restricted constructions.

**Review remark 4 (valid conservative producer count and zero-relator scope).** Counting S4 separately would add three additions and give the valid conservative total 898+112r+lambda for r>=1. The explicit shared six-addition schedule proves the three-operation improvement in (1). Neither formula is asserted for r=0, where a new S4 producer would be unused; that branch retains the existing 903-operation source. No dead row is counted as a necessary live computation.

## 6. Preserved research questions

**Open question 1 (numerical universal data).** The local three-form packet's complete-source question is resolved here, while the actual universal relator list, numerical r and coefficient materialization remain open. No numerical improvement of general84 or formal degree bound follows from the symbolic family.

**Open question 2 (credited guarded affine interface).** Pascal suggests centering a signed input form by a fixed multiple of D*J instead of a selected subset mass. A selector might then produce the offset directly, reducing selected fields further. That route requires its own paid pretyping bound, positive completion margin and formed-digit proof. The homogeneous obstruction does not refute it, and no saving from it is included here.

**Open question 3 (further outer sharing).** The hatted global chart, remaining pack/unhat sharing and special coefficient patterns remain candidates. Arithmetic optimality and impossibility outside the explicitly scoped two-form case are not claimed. Earlier wrong counts, support corrections and failed divisor shortcuts remain in their frozen reports and reviews.
