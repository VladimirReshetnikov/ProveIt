# Grouping two protected norms gives111 operations at degree30

The [complete emitted polynomial](complete113_main_input_units111.py) costs **111=53M+58A operations**, has **24 strictly positive existential witnesses**, and has exact degree **30**. It preserves the full positive integer zero set of the selected [113-operation degree28 parent](complete74_gap_selective_projection113.md), on exactly the same supplied coordinates and fixed ordinary input. The [receipt](complete113_main_input_units111.json) contains every certificate and finalizer gate.

This trades two additions for two degrees. It does not improve the74-operation multi-comparison bound or the86-operation universal polynomial bound. The new111/30 and113/28 points are both nondominated in the specified combined operation/degree catalogue; all earlier86/179 through98/44 points remain available. This is one fixed grouping of two equations in the default24-witness parent, not another general partition search.

## 1. The two actual protected norms

The selected parent retains positive a and c, and computes

    H=4a+3, Delta=a²+H,
    q=(B−1)Jrep+1, X=w*q³,
    d=X+a*c+ga*H,
    kappa=twice_cell_bits*x+inner_bits+delta*Delta,
    mu=W+a*kappa+rho*H.

Its actual source register `A` denotes Delta. Define the already paid root norms

    Nmain=d²−Delta*c²,
    Ninput=mu²−Delta*kappa².

The two old comparisons are Nmain=1 and Ninput=1. For every integer a,

    Delta=a²+4a+3 is0 or3 modulo4.

If Delta=0 modulo4, either norm is a square modulo4 and cannot be−1. If Delta=3 modulo4, either norm is the sum of two squares modulo4 and again cannot be−1. This elementary sign exclusion applies to arbitrary integer roots and ordinates; it uses no parent comparison, Pell classification or positive-coordinate restoration.

Replace the two old comparisons by the single equation

    Nmain*Ninput=1.                                (1)

At an integer zero of the complete new SOS, (1) holds and both factors are integers. Each is therefore+1 or−1. The modulo4 exclusions force both to be+1, restoring both old comparisons. All other old residuals are unchanged. Conversely, every old zero gives both factors1 and hence a new zero. This proves equality of the complete integer zero sets, and in particular of the declared positive zero sets on the unchanged24 supplied witness coordinates.

The comparison product must equal **positive one**. Two unconstrained negative units would satisfy that product while violating both separate equations; their separate residual squares would sum to8. Here those factors cannot be negative units because their actual coefficient is the guarded Delta above. No real-witness zero-equivalence is asserted from this modular argument.

## 2. Literal full-source rewrite and accounting

The parent source has two private output-side rows:

    R15=Ac2+1,             Ac2=Delta*c²,
    norm_rhs=scaled_kappa2+1, scaled_kappa2=Delta*kappa².

Their sole consumers are the main and input comparisons. Replace them, at the same one-addition/subtraction cost each, by

    main_unit=L15−Ac2,       L15=d²,
    input_unit=mu2−scaled_kappa2, mu2=mu².

Add one multiplication `paired_norm_unit=main_unit*input_unit`. The parent comparison positions7 and12 become one comparison `paired_norm_unit=1` at current position7. The other eleven residuals remain exactly identical. All source definitions, root-gap coordinates, input bounds, both ratio slacks, strong equation, markers, masks, synchronization and fixed program numeral meanings remain inherited without change.

The full comparison schedule therefore costs76=41M+35A instead of75=40M+35A. The number of comparisons falls from13 to12. Paying a residual subtraction, a square, and the final sum for all12 comparisons gives

    76+12+12+11=111=53M+58A.

The additional certificate multiplication cancels the removed residual square multiplication. Removing one residual row and its sum contribution saves two additions overall. Every current gate is live, every fixed-numeral use is charged, and every supplied input/witness/numeral port remains present. There are no additional witnesses, hidden zero tests or uncharged equations.

The current packet explicitly maps all13 parent comparisons to the12 child comparisons. Both grouped members are marked as restored unit equations, rather than as polynomial identities with the new residual. It also supplies an updated map from the original19 raw comparisons. The original parent maps and graph-restoration definitions are retained only under historical provenance.

## 3. Complete off-zero relation

Let S be the sum of the other eleven residual squares. The full old and new polynomials are

    F113=S+(Nmain−1)²+(Ninput−1)²,
    F111=S+(Nmain*Ninput−1)².

Their exact all-value difference is

    F111−F113
      =(Nmain−1)*(Ninput−1)
       *(Nmain*Ninput+Nmain+Ninput−1).              (2)

The checker expands (2) as a literal polynomial identity, verifies the actual two norm forms, and checks all eleven retained residual expression DAGs. It then checks the full emitted finalizers. Equality of zero sets in Section1 does not mean equality of these two polynomials off zeros.

The parent’s positive triangular graph restoration and first-root-gap inverse remain available after both old norm equations are recovered. Hence the entire established fixed-program universal theorem applies for the same ordinary positive input x. Runtime remains existential and unbounded. There is no new computational-substrate assumption or universal input decoder.

## 4. Exact degree30 uniformly in the fixed program

The source keeps a and c as independent degree-one positive witnesses. Let b=B−1. The highest homogeneous parts are

    Xtop=b³*w*Jrep³,          dtop=Xtop,
    kappatop=delta*a².

Thus Nmain has exact degree8 and leading form

    b^6*w²*Jrep^6.

For Ninput, put v=W+rho*H. The exact cancellation

    (a*kappa+v)²−(a²+H)*kappa²
      =v²+2a*kappa*v−H*kappa²

shows degree at most7. Only the last term reaches that degree, giving the leading form

    −4*delta²*a^5.

The product therefore has exact degree15 with leading form

    −4*b^6*w²*Jrep^6*delta²*a^5.

All eleven other residuals have degree at most14 by the unchanged parent source. Squaring the grouped residual supplies the unique top homogeneous form of the whole polynomial:

    16*b^12*w^4*Jrep^12*delta^4*a^10.               (3)

It is nonzero for every admissible fixed b>0. Therefore30 is the exact formal degree on every fixed program slice. Literal source propagation alone gives32 because it misses the input-norm cancellation; the packet distinguishes that syntactic upper bound from the proved degree30.

The degree checker authenticates the complete packet and verifies the literal cones used above. It also expands the entire emitted polynomial in Q[t,b], scaling every varying coordinate by t and the root gap by3t. The leading coefficients of the main norm, input norm, product, and whole polynomial are respectively b^6,−4,−4b^6,16b^12 at degrees8,7,15,30. These exact source expansions corroborate the uniform symbolic argument; an unproved fixed-base specialization is not the degree proof.

## 5. Canonical APIs and replay boundary

The emitter authenticates the frozen113 source/receipt/proof and its nine pinned immediate provenance files before reading the complete parent JSON. It imports no historical module and uses no mutable canonical cache. `canonical_parent(root=...)` selects only the default q,C,k,d,kappa,mu projection. `rewrite(supplied,root=...)` requires recursive exact-type equality with that complete parent, not merely matching norm rows. `build`, `checked`, `polynomial_source` and `degree_certificate` similarly operate on the complete canonical source.

`evaluate(packet,values,signed=False,root=...)` requires the exact full coordinate dictionary and strict integer types. The default domain is positive input, witnesses and numeral ports. The explicitly Boolean signed option permits integer algebra checks; it does not certify arbitrary numeral ports as a valid compiled program. All public packets and source lists are fresh. Mutating Boolean/float coefficients, stale maps, ledgers, source containers or appended dead gates is rejected. `python -O` is rejected.

Replay needs only the Python3 standard library:

```sh
python3 complete113_main_input_units111.py \
  --root /path/to/native-stream-queue \
  --expect complete113_main_input_units111.json
```

For a private preinstallation replay, a missing parent file may be found beside the script; any file present at `--root` must match its pin and cannot be bypassed by that fallback. The deterministic receipt does not depend on absolute paths. `--output PATH` writes a fresh receipt.

The receipt records the complete76/111 paid schedules,24 witnesses,12 comparisons, full degree certificates, eleven exact retained residual DAG identities,96 full off-zero corrections including48 signed and16 rational cases,1056 retained residual-value checks, all64 residue-class sign checks,50 malformed caller rejections, four defensive-copy checks, twelve warm parent-pin rejections, and an optimized-mode rejection. The zero-equivalence proof is the integer-unit and modulo4 argument, not a finite search for native zeros. No enormous positive Pell tuple is materialized, and no unchanged historical author suite is rerun.

Author writer and fresh read-only receipt replay pass. Existing sources and the frozen113 family remain unchanged. The possible asymmetric-scale extension is outside this packet and has no claimed transfer theorem here.
