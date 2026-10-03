# Independent downstream561 review

Status: PASS for frozen Python `c4411ccfc9b62b1d8efe366686b99d4287031378b3acc0f5c07a1c10c52ef126`. The audited parent611 Python is `3208cefa385789f2a7774bd348316a99e57f841154c40eed065e159bad4d20ce`. This review covers the full downstream source, both actual emitted packets and complete finalizers, the fifteen-field positive graph, the exact comparison map and SOS correction, current metadata and public source/assignment contracts. It does not reprove all inherited native Pell, unbounded-history, or ordinary program-encoding theorems.

## Graph and positivity

The ordinary compiler deletes exactly fifteen supplied coordinates and their defining comparisons. The map is acyclic in the actual reordered source. At a parent zero the removed comparisons force precisely this map, so projection is injective and the retained comparisons imply the child equations. Conversely restoration of any positive child zero yields a positive parent zero. The following positivity holds throughout the positive child domain, before imposing a zero, native power typing, or any rule-word interpretation.

Write the retained positive input slack as `s_x`. The input field is `q=x+s_x>=2`, hence `Q=q^32>=2^32`, `B=2^31 Q>=2^63`. The index field is `J=B+index_beta>B`, and `P=(B-1)J+1>0`. With positive `h=quotient_hat` and `z`, the restored field is

```
Ahat=(Q-1)(h-1)+z+1>=2.
```

The exact old congruence becomes an identity because

```
[(Q-1)(h-1)+z+1]+Q=(Q-1)h+z+2.
```

Both native copies set `s=2*odd_half+1>=3`, `k=eta+zeta>=2`, `c=Y*k+eta>0`, `a=Y*(X+1)>0`, and `d=X+a*c+ga*(4*a+3)>0`; their supplied `w` and computed scale are positive. The AND additionally sets `r=F0+q_native*F1+q_native^2*F2+q_native^3*F3>0`. Its first three fields remain positive supplied coordinates, while its existing fourth-field expression is `F3=16*Ahat-8>=24`. These are the actual retained definitions, including all hatted-field offsets. Independent interval propagation on the literal emitted source certifies positive lower bounds for all fifteen targets and stores them in the receipt.

No arbitrary parent tuple is asserted to lie on this graph. `project_assignment(..., require_graph=True)` checks it; `require_graph=False` merely forgets the fields. The all-signed restoration remains an algebraic map and is not a positivity theorem over signed inputs.

## Actual arithmetic and complete correction

The retained powers give `v170=P^2`, `v181=P^3`, `v184=P^6`, and `v192=P^28`. Thus the old `v254=P^5` and `v267=P^34` are computed as `v181*v170` and `v192*v184`. Four private multiplication gates disappear. These are all-value polynomial identities.

The old tape residuals have the literal form `2*A-64*D*C`. The child uses `A-32*D*C`, sharing the single paid `32*D` product. Thus each old tape residual is exactly twice its new counterpart; this saves one multiplication overall. All other retained residuals agree exactly after the graph restoration. Each removed residual vanishes identically after restoration; the shifted quotient identity above handles the only defining comparison requiring affine simplification.

Let `F_old` and `F_new` be the complete emitted sums of squared comparisons, and let `r_L,r_R` be the child tape residuals. On every integer or rational child tuple,

```
F_old(restore(v))=F_new(v)+3*(r_L(v)^2+r_R(v)^2).
```

This proves the same zero set on the restoration graph over the reals, and the claimed positive-coordinate bijection follows from the positivity and unique definitions above. It is not equality of the complete polynomials on an unchanged tuple. The raw interface needs no coordinate map but still has this nonzero SOS correction away from its zero set.

The full independent ledger is:

| Interface | Parent | Child | Comparisons | Positive witnesses |
|---|---:|---:|---:|---:|
| Natural raw half tapes |368=131M+237A|363=126M+237A|11|51|
| Positive ordinary input |611=239M+372A|561=219M+342A|31|87|

The ordinary certificate has469=188M+281A gates, followed by31 squares and61 subtraction/addition gates. Its fifty-operation saving is five certificate multiplications plus45 finalizer operations for fifteen removed residuals. Reconstruction of the shifted quotient adds one subtraction and deletes the old congruence-left addition, for no net certificate cost. Parameters, fixed program numerals, existing program orientation, and all retained witness domains are unchanged. Universality remains an inherited valid-program-slice statement, not a claim about arbitrary positive program tuples or an improvement of the separate87-operation universal bound.

The exact-degree calculation propagates formal degrees and modular leading coefficients through the whole source. The added conservative fixed-parameter dependency tracking verifies that its nonzero top coefficient is independent of all fixed program numerals. The retained history native residual still attains degree968, and its square gives1936; no smaller degree is claimed. The parent compiler's original upper-bound-only metadata remains untouched.

## Source contracts and independent checks

All public packets and source exports are defensive copies. Canonical checking compares exact scalar/container types. Signed evaluation is explicit, raw `L0,R0` allow zero, and every other supplied coordinate is strictly positive by default. Actual parent descriptors are pinned with type-sensitive hashes, not only their generator source.

Two draft contract gaps were fixed before the frozen source: warm cache access now propagates the parent's lineage/source checks, and saved receipt comparison uses exact types instead of Python's Boolean/integer equality. Cold loader regressions in the author receipt exercise both no-file and foreign-root module poisoning. This independent review read those repairs but does not count the author's two cold replays as its own tests. No unresolved source/API issue was found.

The standalone independent helper accepts `--source` and `--root`, pins both source files before import, and emits a deterministic receipt. Its independent interpreter and reconstruction of both literal SOS finalizers check160 full correction identities, including72 signed integer cases and16 rational cases,4560 individual residual maps,144 public restore/project roundtrips,72 positive restorations,510 malformed-input rejections, and six defensive-copy checks. It also verifies closure, liveness, exact free-coordinate sets, every ledger operation and all fifteen positivity cones. These finite tests supplement the all-value source argument; no full imported universal zero or astronomical Pell witness was materialized.

Example replay:

```
python review_u15_downstream561.py --source /path/to/u15_packed_downstream561.py --root /path/to/native-stream-queue --expect review_u15_downstream561.json
```

The full companion author note was independently read at SHA256 `7ebfef9648175c4c5b6769b39004190bd6970fad3f54312a1b4c10554929b85c`. All six sections agree with the actual source and proof: the signed integer graph bijection, its positive restriction, every intermediate ledger, the loader residual degree bound726, the two leading-coefficient pairs and fixed-parameter independence are correctly scoped. Its intended sibling link to the611 note resolves in the maintained directory. No correction requested. The independent helper writer and fresh exact saved-receipt replay both passed.
