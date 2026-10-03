# Report33: transfer to the asymmetric signed19 orientation children

Authored scope note, 2026-10-03. Status: source comparison and proof supplied for independent review. This is a new supplement; delivered Report33 and its audited proof are unchanged. No new degree, operation-bound, height, or counting claim is made.

## 1. Exact source boundary

The current sources are frozen at `9fa99be93fb479294d5d5a2458e59e5fba8444b6` in `VladimirReshetnikov/ProveIt`, under `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/`.

The saved asymmetric packet changes exactly one producer in each of raw30, positive22 and signed20:

    old: wn2 = w*n2, n2=q^3
    new: wn2 = w*q

Thus the exponent pair changes from `(3,3)` to `(1,3)` in `X=wq^a, Y=sq^b`. The supplied w has no other consumer. All supplied coordinates, fixed numerals, comparisons and finalizer conventions are preserved. The Report33 cached symmetric JSON is byte-identical to the current pinned symmetric JSON, with Git blob SHA1 `6aaaf69a6104ebfffd9e08a6331166c661a60847`.

In signed20 the definitions remain

    C=q-alpha-2dx, W=C-Z, gamma=rho+sigma,
    k=eta+zeta, E=XY, c=kY+eta.

No new `F+Z<q` guard appears. The older normalized87/coupled88 source instead has `C=q-F-Z-alpha-2dx`; its stronger guard and different coordinate interface must not be imported here.

The valid current signed20 parents still supply **positive r**, have twenty positive supplied coordinates and retain all nine comparisons. Their native inverse-scale proof uses that positive r. This note does not contradict those parents or change their domains.

## 2. Define the eight prospective children precisely

For either scale, there are four signed20 orientations, indexed by `(epsilon,nu)` in `{0,1}^2`. Write

    T2=(ic^2)^2, K=Delta(f^2-1), U=jc-r, V=of-c.

Every orientation retains both `T2=K` and `U=V`. Its auxiliary norm comparison is

    C_epsilon*(U_nu^2-y^2)=1-y^2,
    C_0=T2, C_1=K, U_0=U, U_1=V.

Consequently the four choices are: `(0,0)` original; `(1,0)` coefficient only; `(0,1)` root only; `(1,1)` both. Signed20 has no E-binding, kY-binding or input-gap orientation switch.

For each of these four parents at each scale, define its index-eliminated child by substituting

    r=R=k-hXY-1

everywhere and dropping only the now-identical first-index comparison `k=r+1+hXY`. This defines four symmetric and four asymmetric children. It is a mathematical construction, not a claim that new eliminated source packets were published upstream.

The exact nineteen supplied child coordinates are

    Jrep,F,alpha,zquot,f,h,i,j,o,s,w,tau,eta,zeta,y_aux,Z,delta,rho,sigma.

The retained comparisons are transport, packing with R, the first Pell norm, the main Pell norm, the strong auxiliary comparison, the chosen auxiliary norm, `jc-R=of-c`, and the input norm. All nineteen supplied coordinates remain required to be strictly positive; R is computed and has no independent positivity guard.

## 3. Transfer theorem and proof

Let `G_(3,3)^(epsilon,nu)` and `G_(1,3)^(epsilon,nu)` denote the complete sums of squares of the eight residuals just defined. Define Phi on their supplied coordinates by

    w_new=q^2*w_old,

leaving every other supplied coordinate, the ordinary input and fixed numerals unchanged. Then, for each of the four orientations,

    G_(1,3)^(epsilon,nu)(Phi(v)) = G_(3,3)^(epsilon,nu)(v)

as an all-value polynomial identity over every commutative ring.

Indeed, q is independent of w and `(q^2*w_old)*q=w_old*q^3`. Hence X is unchanged, as are Y, E, k and every later computed quantity for the same orientation. In particular `R(Phi(v))=R(v)`. The complete literal r-consumer inventory is `r+1`, `jc-r`, and the packing comparison. Substitution covers all three. The first-index residual becomes identically zero on both sides, so deleting its square preserves the identity. Thus index elimination and the scale coordinate change commute.

Within either scale the four children have the same comparison-zero locus over every commutative ring, and the same SOS-zero locus over the reals. Both protecting comparisons remain after elimination:

    T2=K, jc-R=of-c.

On their common locus the chosen auxiliary coefficients and roots agree, regardless of the sign of R. All other residuals are unchanged. This proves both directions of zero equivalence without assuming positivity of the deleted index. Equivalently, equation orientation and the r-substitution commute algebraically.

Now fix any compiler and positive ordinary input covered by the audited Report33 theorem. Take its infinite family of strictly positive supplied-coordinate zeros of the original symmetric signed19 child, with `R=-p<0`. Its strong and linear auxiliary comparisons hold exactly, so the same tuples zero every symmetric orientation. Applying Phi yields zeros of all four asymmetric children, with the **same negative R** and every supplied coordinate still strictly positive. Phi is injective on positive tuples because q is unchanged and positive. Therefore each child has infinitely many such zeros at each positive input.

The generalized compiler supplement transfers under exactly its stated algebraic fixed-numeral hypotheses as well. The forward identity needs no inverse-divisibility theorem and no new Dirichlet or Pell construction.

## 4. Limits

This establishes failure of positive-index restoration for these corresponding signed19 children only. It does not assert an integer inverse on every asymmetric-child zero, a counterexample to the retained-positive-r parents, or applicability to raw29, positive21, normalized87 or coupled88. Parent polynomial degrees and operation ledgers are not being assigned to the children. No family-height or counting theorem is asserted here.

## 5. Source bindings and reproducibility

Primary pinned sources:

- [Asymmetric transfer proof](https://github.com/VladimirReshetnikov/ProveIt/blob/9fa99be93fb479294d5d5a2458e59e5fba8444b6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_asymmetric_scale_transfer.md)
- [Asymmetric literal JSON](https://github.com/VladimirReshetnikov/ProveIt/blob/9fa99be93fb479294d5d5a2458e59e5fba8444b6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_asymmetric_scale_transfer.json)
- [Equation-orientation proof](https://github.com/VladimirReshetnikov/ProveIt/blob/9fa99be93fb479294d5d5a2458e59e5fba8444b6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_equation_orientation_census.md)
- [All 56 literal orientation packets](https://github.com/VladimirReshetnikov/ProveIt/blob/9fa99be93fb479294d5d5a2458e59e5fba8444b6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_equation_orientation_census.json)
- [Independent orientation review](https://github.com/VladimirReshetnikov/ProveIt/blob/9fa99be93fb479294d5d5a2458e59e5fba8444b6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete74_equation_orientation_census.md)
- [Symmetric literal parent](https://github.com/VladimirReshetnikov/ProveIt/blob/9fa99be93fb479294d5d5a2458e59e5fba8444b6/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_factored_first_norm.json)
- [Report33's historical eliminated packet](https://github.com/VladimirReshetnikov/ProveIt/blob/2dde7850ffeb9c923a7bd92e3f2ee2b5af0e36ff/Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.json)

SHA256 of the three decisive current JSON files:

    symmetric: 7ebfa54d3846d1c3a6ff7b8e5cd143f3ac80f8299b51698a9f45681d3524eb28
    asymmetric: 14816c4da8738e3c27cc1ec0217c450075c0e47b20d77ec4c4d8159aac24dc88
    orientations: 627568df8674e3fbe32bac6881a9ef89587a902ed25476b2a541f1eff0875559

The unchanged Report33 proof SHA256 is `b109e2fd1142cdad84a5b519acc5dc5055160f1d8e7617d648a561538fd956cd`; its independent audit is included. The generalized supplement SHA256 is `69f64c16aed4f9b962ec82553186ffc25cae79cb6808bfe0a3e6136797c0ae60`; its audit is also included.

`SOURCE-MANIFEST.json` gives all source URLs, origin pins, byte sizes and SHA256/Git-blob hashes. `MANIFEST.json` covers the complete authored packet. The newly authored `check_static_sources.py` authenticates the five JSON inputs, verifies the sole scale change in all three interfaces, checks all eight signed20 orientation producer maps and protections, and matches Report33's exact r-elimination. It treats arithmetic rows as inert descriptions; it imports no upstream Python and executes no arithmetic schedule. The saved `static-receipt.json` records these checks. The proof above, together with Report33, supplies the infinite-family conclusion.
