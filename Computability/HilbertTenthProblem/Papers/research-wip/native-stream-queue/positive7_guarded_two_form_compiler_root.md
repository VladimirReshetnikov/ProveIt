# A complete positive7 compiler with guarded two-form relator selection

For r>=1 fixed presentation relators, the complete guarded two-form compiler has

    (280+42r+powcost(62+6r))M+(550+54r)A

in its certificate and

    (303+42r+powcost(62+6r))M+(595+54r)A
      =898+96r+powcost(62+6r) operations                 (1)

in its single ordinary integer polynomial. Here powcost(t)=floor(log2 t)+popcount(t)-1 is the explicitly emitted binary power-chain length. There are 23 comparisons and96+6r positive existential coordinates, separate from the ordinary input x>0. The same fixed alphabet and acceptance relation are used, with a changed witness interface and guard.

Relative to the preceding complete three-form compiler, the exact operation saving is

    16r-3+powcost(62+8r)-powcost(62+6r),                  (2)

and the positive witness count decreases by2r. The power-chain difference is not assumed monotone or free. For r=0 retain the unchanged903-operation,96-witness predecessor source. The actual numerical universal presentation and r remain unmaterialized: this is a symbolic compiler-family result, not a new numerical universal bound. The general84-operation result is unchanged.

## 1. Fixed recipe and exact interface

The [guarded two-form proof](positive7_guarded_two_form_selection_pascal.md) and its [independent mathematical review](review_positive7_guarded_two_form_selection_riemann.md) supply the finite relation. For each actual fixed P in SL2(Z), retain the integer factorization

    (S(P^sign)-I3)C=E_sign*[ell_1;ell_2],
    C=[1,0,0,-1;1,1,0,-2;2,0,1,-4].                     (3)

The common right invariant, primitive integer row basis, original-coordinate permutation reversal and central +/-I convention are those of the three-form compiler. The two ell rows have four entries; each E_sign is3 by2. These are linked fixed numerals prepared from the actual relator, not existential coefficients. All gcd, Bezout and exact divisions belong to fixed preparation, with every resulting runtime coefficient product still paid.

Over all relators and both ell rows, set nminus=max(0,all negative coefficient magnitudes), pplus=max(0,all positive coefficients), lambda=nminus+1 and Cg=2lambda+1. Choose one fixed dyadic K>max(Cmass,8+2r,Cg,lambda+pplus), where Cmass is the common positive7 column sum. The source names lambda as `center_lambda` and Cg as `guard_bound`. Its6+20r roles are alpha,gamma,K,kappa_minus_one,center_lambda,guard_bound plus8 signed `form_ell` and12 signed `relator_E` roles per relator. All six global roles and the actual-relator recipes must retain their stated meanings. No theorem is asserted for arbitrary independent role assignments.

The eight paired letters keep their exact52 raw selected-coordinate fields. Each signed relator slot retains only fields1,2, in the order(A1,A2); its former field0 for selected subset mass is absent. The supplied positive coordinates are seven histories H_i, six terminals F_i with F7=F1, m=8+2r selector hats, N=52+4r selected-output hats, two outer slacks and21 native auxiliaries. Every hat is explicitly reduced by one before use, including zero-valued absent selections. The histories and terminal coordinates themselves remain strictly positive.

Keep the ordinary loader tau=alpha*x+gamma, z=(3,tau,tau^2,2,tau,tau^2,1) and S0=2tau^2+2tau+6. Let J be the raw selector checksum, D=S0+height_slack, B=KD, Pscale=(B-1)J+1, S=sum H_i, mu=(D-1)J and Ztot the sum of every retained raw selected output. The source computes S by a six-addition chain and introduces

    hcenter=lambda*D, Wcenter=hcenter*J, DJ=D*J,
    A_j=ell_j*H_(4,5,6,7)+Wcenter.                       (4)

Each A_j is computed once per relator and shared by both signs. The new comparison is

    joint_bound=Cg*(DJ-S)=Ztot+global_slack=joint_rhs.     (5)

The hatted form of(5) has the new offset N, not the former selected-field count. The literal compiler uses raw unhat values and therefore pays the unhats directly.

## 2. Positive typing before native semantics

Every raw selector and selected output is nonnegative on positive supplied coordinates. At a full zero, the positive slack and(5) imply DJ>S>=7, J>=1 and Ztot<Cg*DJ. These implications do not use native semantics or history recovery. Since -nminus*S<=ell_j H<=pplus*S,

    0<lambda*DJ-nminus*S<=A_j<=(lambda+pplus)DJ<Pscale.

For any integer T<K and D,J>=1, Pscale-TDJ=[(K-T)D-1]J+1>0. Applying this with T=1,Cg,lambda+pplus proves the required whole-word bounds for S, Ztot and the formed inputs. Individual histories, selectors and selected outputs are consequently below Pscale. D,J,mu and the masks have the inherited elementary bounds, with Pscale>=B>D.

There are m Boolean selector lanes, N selection lanes, one aggregate lane(S,mu,S) and the height lane(D,D-1,0), totaling ell=62+6r. Each relator lane is(A_j,(B-1)S_sigma,Z_sigma,j). Pack all three sides at radix Pscale. At every full zero, each lane is nonnegative and below Pscale, so the packed native parameters(T,A_pack+1,M_pack+1,Z_pack+1), with T=Pscale^ell, are positive and properly bounded.

Only then invoke the complete prescribed-AND positive projection theorem. An integer sum of residual squares first forces every comparison, including(5); there is no need for an off-guard positive-host embedding. Computed forms can be negative on arbitrary positive supplied tuples. No supplied coordinate's positive domain is weakened, and no native equation is removed.

The native theorem gives dyadic T, hence dyadic Pscale because ell is a fixed positive integer and Pscale>1. Lane separation yields all AND identities. The height lane makes D dyadic, so B is dyadic. The repunit identity gives Pscale=B^n and J=sum_(t<n)B^t for n>=1. Because m<B, Boolean selector checksums are carry-free and select exactly one letter per cell. Form lanes at this point select canonical digits of whole formed words; they do not yet establish their intended affine digit formulas.

## 3. Simultaneous recovery and positive completion

For each relator sign the source pays one selected center Q_sigma=hcenter*S_sigma, then computes

    T_sigma,1=Z_sigma,1-Q_sigma,
    T_sigma,2=Z_sigma,2-Q_sigma.                         (6)

Since hcenter=lambda*D<B and selectors have0/1 digits, Q_sigma has exactly the constant center digit at the selected cells. Both signed forms share this paid product. Append E_sigma*(T_sigma,1,T_sigma,2) into the three existing d/e/f increment accumulators. The exact198-row paired action and common positive baseline are unchanged.

Retain the seven recurrences B*V_i=H_i+Pscale*F_i-z_i. Modulo B they first recover the initial history cell because S0<D<B. At any recovered state of mass a<D,

    0<lambda*D-nminus*a
      <=ell_j*h_(4,5,6,7)+lambda*D
      <=lambda*D+pplus*a<=(lambda+pplus)D<B.              (7)

Thus its affine form coefficients have neither carry nor borrow. Selection and(6) recover the genuine signed forms; (3) recovers the actual relator difference. The paired action, baseline and lift give the actual positive next state, whose total is below Cmass*D<B.

Inductively subtract known lower recurrence coefficients and recover the next history cell modulo B. Its preceding genuine update already bounds the mass below B. Earlier state masses were below D, so the aggregate has no incoming carry; the aggregate AND lane sharpens the current recovered mass to<D. Only now apply(7), using the previously proved absence of lower form carries/borrows. This recovers its formed digits and true action. Higher unrecovered signed coefficients cannot affect the lower modular argument. The top coefficient gives the genuine positive terminal, without a prior terminal range assumption. The F7=F1 alias enforces the same acceptance; initial coordinates3 and1 reject an accepting empty word.

Conversely, for an accepted finite word choose fixed G=max(1,all p_1+p_2), where p_j bounds the positive coefficients of ell_j, and a dyadic D>(Cg+G)*a_max above the largest state mass. All form coefficients then obey(7). A paired cell contributes at most its mass a to Ztot; a relator cell contributes at most G*a+2lambda*D. Each global-slack coefficient therefore satisfies

    Cg*(D-a)-zsel >= D-(Cg+G)*a>0.

Their packed sum is the positive slack in(5). Histories, endpoints, masks and selected hats satisfy the relation, and the native converse supplies fresh positive auxiliaries at the changed packs and scale. Recurrences telescope. This proves ordinary-input/accepted-word projection in both directions. Old witness values, native auxiliaries, slack or radix need not be preserved; no full-polynomial identity with the parent is claimed.

## 4. Complete source, gates and boundary bindings

The new emitter reads only the frozen three-form JSON as inert records. It copies the six-row input/mass prefix and the exact198-row paired cut. It constructs all current unhats, checksums, six mass additions, centers, guard, masks, signed form producers, three packs and new prescribed power. Its native block has all64 rows: seven freshly rebound header rows q=16T,16A_pack+12,16M_pack+10,16Z_pack+8, followed by the exact57 parent rows. All15 native comparisons and21 auxiliaries remain.

Each relator producer pair costs8M8A. Each signed slot pays1M2A for the shared center and two differences, then6M6A for the3-by2 action fully appended to the existing accumulators. Both signs therefore cost14M16A after their producers. Zero/unit fixed coefficients remain charged.

The33 fused postprocessor rows are copied under the six final increment bindings; the20 recurrence-right-side rows are unchanged, with six Pscale*F products serving all seven recurrences. The23 comparison list is rebuilt: its first pair is now[joint_bound,joint_rhs], while its other22 pairs match the parent. All68 finalizer rows are explicitly emitted from that list, so comparison_residual_0 subtracts joint_rhs, not the old lane_scale. Its square and the final sum stay present.

| Disjoint stage | M | A |
|---|---:|---:|
| Input, mass, geometry, shared centers, guard and masks | 17+2r | 134+12r |
| Two centered form producers per relator | 8r | 8r |
| Three guarded-input packs | 182+18r | 182+18r |
| Fixed prescribed power | powcost(ell) | 0 |
| Complete native certificate | 33 | 31 |
| Exact paired cut | 30 | 168 |
| Guarded relator appends | 14r | 16r |
| Fused positive lift | 12 | 21 |
| Seven recurrence right sides | 6 | 14 |
| Certificate | 280+42r+powcost(ell) | 550+54r |
| Residuals, squares and sum | 23 | 45 |

The prefix uses4M2A for centers and guard in place of1M2A. Removing2r selected fields saves4r unhat/total additions. Each of three Horner packs loses2r appends, saving6r of each operation. The power is regenerated from the fixed new exponent; no old scale register is reused just because its name happens to coincide. These uniform grammar counts prove(1) for every r>=1, rather than extrapolating saved instances.

| Saved full graph r | ell | powcost | Polynomial M/A | Operations | Positive witnesses |
|---:|---:|---:|---:|---:|---:|
| 1 | 68 | 7 | 352 / 649 | 1001 | 102 |
| 2 | 74 | 8 | 395 / 703 | 1098 | 108 |
| 4 | 86 | 9 | 480 / 811 | 1291 | 120 |

The receipt contains3390 complete rows for these three graphs. Its r=3,8 entries are structural censuses only; r=0 binds the exact earlier903 source through the predecessor receipt. The emitter checks topological closure, distinct supplied/computed names, allowed operations, fixed roles and liveness of every supplied port and computed row. These are structural checks, not numerical or symbolic execution of a saved arithmetic graph.

## 5. Retained boundaries and open work

**Review remark1 (negative form versus whole pack).** The guarded proof's shear P=[1,1;0,1], J=0, H4=3 and all other histories1 gives A1=-2. It refutes unconditional individual-form positivity. The [root domain clarification](positive7_guarded_form_domain_clarification_root.md) retains the earlier imprecise pack-negativity wording and proves that this example's whole left pack is79+D>0. It is excluded by the guard and is not a full compiler zero. The present composition uses only guard-established input positivity and lane bounds.

**Review remark2 (valid earlier schedule).** The28M24A independent-shift local schedule remains valid. One global center and one selected-center product per sign give the adopted22M24A local schedule, including the changed shared guard work. Neither schedule is an arithmetic lower bound. The prior homogeneous two-form obstruction is unaffected because this construction uses affine centering and a restricted guard domain.

**Open question3 (further exact action reductions).** Pascal's separate proposal to exploit the integral quotient action linking a relator and its inverse is under proof review. It is not used by this source and receives no saving here. Any replacement must pay its fixed-coefficient products and accumulator consumers in a complete composition.

**Open question4 (numerical universal datum and stronger claims).** A numerical fixed universal presentation, its actual integer matrices and r, a numerical universal operation count, source degree and arithmetic optimality are not established. Inherited group-universality and native foundations retain their previous review scope; no new external theorem audit is claimed. The local guarded complete-source question is resolved by this explicit composition only to the extent confirmed by its separate independent source and proof reviews.

The emitter and its first receipt are frozen. The receipt SHA256 is99e59b73bf1e6a9b0810f8ed862fefe62af00842edafd216e1c0420881ea7784; its only source input is the preceding three-form receipt8c056b9fc7b75c79677332e5dafac8de7130a2530cc79ae2fc300c862efed195. The new original emitter ran once for metadata-only row construction and structural checks. No supplied, archived, committed, predecessor or frozen code was executed/imported; no saved source/coefficient arithmetic, degree propagation, scientific sampling, native witness experiment or build was performed. The emitter must not be rerun or imported after freezing.
