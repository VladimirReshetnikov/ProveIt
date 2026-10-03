# Ordinary first roots in the complete asymmetric grouping families

The [source](complete86_first_root_partitions.py) extends the proved
[complete86 first-root change](complete86_factored_first_root.md) to the
thirteen existing asymmetric factor bases. Besides reproducing86/179 and
87/135, it improves four points of the previously established finite
operation/degree frontier:

| Complete polynomial operations | M | A | Exact degree | Certificate gates | Equations | Selected base |
|---:|---:|---:|---:|---:|---:|---|
|88|47|41|123|87|1|Linear input, coupled eight units|
|91|48|43|102|83|3|Linear input, coupled seven and strong comparison|
|92|48|44|80|81|4|Original asymmetric ordinary seven and strong comparison|
|95|48|47|54|81|5|Linear input, coupled seven and strong comparison|

Every source has19 supplied **strictly positive** witnesses and the same
ordinary positive input and valid fixed-program slice as its respective
parent. The full positive zero sets correspond bijectively through one
coordinate change. This is a complete circuit result: all norm, transport,
input and finalizer gates are included. The best polynomial operation
bound remains86; the separate74-operation comparison construction is
unchanged.

The earlier [three-base family](complete75_asymmetric_factor_partitions.md)
and [ten linear-input/auxiliary-gap bases](complete75_asymmetric_linear_gap_tradeoffs.md)
are the exact finite scope. The latter already use **X=wq,Y=sq³**; this
packet consumes their actual asymmetric source receipts, rather than the
older symmetric X=wq³ sources. Other coordinate changes, factor choices,
finalizers or general arithmetic circuits are outside the census.

## 1. The literal first-root replacement

In all thirteen bases, the actual source computes

    q=(B−1)J+1, X=wq, Y=sq³, E=XY,
    k=eta+zeta, kY=k*Y, L=E*(kY)=X*Y²*k.

Here L is source register `first_root_base`. The old positive coordinate
g is `tau_gap`; the new positive coordinate T is `tau_root`. The old
first norm and its replacement are

    N0 = g² + L*(2g−k),
    N0' = T² − L*(L+k).                             (1)

The complete six-gate block for N0 costs3M+3A: g²,L,2g,2g−k,
L(2g−k), and the final addition. The new five-gate block costs3M+2A:
T²,L,L+k,L(L+k), and the final subtraction. Exactly one addition is
saved. The emitter checks the literal six parent rows, the actual
X,Y,E,k,kY producers, and that g occurs only in its square and double.
It keeps every other core row unchanged.

The triangular coordinate maps are

    T=L+g,       g=T−L.                             (2)

Since L does not depend on either g or T, these maps are inverse over
integers, rationals and polynomial rings. Expanding (1) after (2) proves
an **all-value identity of each complete grouped polynomial**. This is
not same-coordinate polynomial equality: the first-root coordinate has
changed. The other eighteen witnesses, ordinary x and fixed compiler
numerals are unchanged. No computation of the inverse gap is charged to
the new circuit because it is only a proof map, not an evaluated port.

## 2. Positive restoration before invoking a parent theorem

For a partition into nonempty groups, let G_j be the product of its
factors. Every factor occurs exactly once. Let Q_l be the retained
ordinary comparison residuals. The two permitted complete finalizers are

    sum_l Q_l² + sum_j (G_j−1)²,                     (3)

and, with distinguished group a,

    G_a * (1+sum_l Q_l²+sum_(j!=a)(G_j−1)²)−1.      (4)

At an integer zero of (3), all displayed residuals vanish. At an integer
zero of (4), its nonnegative integer sum S satisfies G_a(1+S)=1.
Therefore G_a=1 and S=0, so again every group product is1 and every
retained comparison holds. In particular each factor, including N0',
is an integer unit: **N0'=+1 or−1**. No individual positive sign is
assumed at this stage.

Now start with any complete new positive zero. The actual computed
L is positive and k=eta+zeta is at least2. Thus

    T²−L² = L*k + N0' >= 2−1 > 0.                  (5)

Since supplied T is positive, T>L. Consequently g=T−L is a strictly
positive integer **before any parent norm, rank, word-typing or input
lemma is invoked**. Restoring this one coordinate gives a positive tuple
of the selected old grouped source. The complete identity from Section1
makes its old output zero. Its already proved full parent theorem now
applies, including all protected norm signs and ordinary-input semantics.

This order also handles the auxiliary-gap bases. Their computed ordinate
y=V+e may be negative on arbitrary positive supplied tuples. We do not
assume it positive to restore g. The old auxiliary-gap theorem, applied
only after g has been restored positive, proves the needed positivity
in its established dependency order.

Conversely every old complete positive zero has L>0, so T=L+g>0.
The all-value identity gives a new zero. The two maps are inverse;
hence this is a **bijection of complete supplied positive zero sets
within each selected base**. It retains arbitrary admitted witness
fibers, not only a chosen canonical Pell extension. The old within-base
grouping proof supplies that every individual factor equals+1 at old
positive zeros; retained strong and linear comparisons remain literal.
No assertion identifies supplied tuples across different strong treatments
or auxiliary coordinate systems.

The inverse map need not preserve positivity off the zero set. For
example T=1 with all other positive coordinates1 has L>1. The public
positive inverse consequently rejects such a tuple. Integer and rational
off-zero graph identities are arithmetic checks, not a claim about signed
or real universality. The anchor argument specifically uses integrality.

## 3. The thirteen authenticated bases and complete ledgers

Use factor order N0,N1,N2,N3,Nk,Nt,Ns,L for coupled eight-unit bases,
replacing L by L0 for uncoupled bases. Seven-factor bases omit Ns and
retain the full comparison Qs=(ic²)²−Delta(f²−1)=0. Six-factor bases
also omit L0 and retain U−V=0. The parent identities are Ns=1+Qs
and L0=1+V−U. In the first three rows below, the ordinary-comparison
base likewise omits Ns. The source selects actual coupled or uncoupled
parent rows before pruning their unused ancestors; it does not replace
L by L0 using an off-zero unit assumption.

| Base | Exact new factor degrees in source order | Core M/A | Retained residual degrees |
|---|---|---|---|
|Asymmetric normalized eight|22,18,32,56,7,3,34,7|41/37|none|
|Asymmetric ordinary eight|22,18,32,24,7,3,22,7|40/39|none|
|Asymmetric ordinary seven|22,18,32,24,7,3,7|40/37|22|
|Linear coupled eight|22,18,20,24,7,3,22,7|40/40|none|
|Linear uncoupled eight|22,18,20,24,7,3,22,6|40/41|none|
|Linear coupled seven|22,18,20,24,7,3,7|40/38|22|
|Linear uncoupled seven|22,18,20,24,7,3,6|40/39|22|
|Linear six|22,18,20,24,7,3|40/37|22,6|
|Gap coupled eight|22,18,20,20,7,3,22,7|40/41|none|
|Gap uncoupled eight|22,18,20,20,7,3,22,6|40/42|none|
|Gap coupled seven|22,18,20,20,7,3,7|40/39|22|
|Gap uncoupled seven|22,18,20,20,7,3,6|40/40|22|
|Gap six|22,18,20,20,7,3|40/38|22,6|

For core cost C, n factors, m retained comparisons and g groups, the
group-product certificate costs C+n−g and has m+g equations. Both
complete finalizers cost

    C+n+3m+2g−1,                                  (6)

except m=0,g=1 with that group anchored: the finalizer is simply G−1,
and the complete cost is C+n. This exception reproduces the complete86
and87 outputs exactly. The checker compares their entire expression DAGs
to the frozen [complete86 source and receipt](complete86_factored_first_root.json).

Every gate in every emitted core, certificate and polynomial is live.
All fixed-numeral multiplications, squares, binary sums and subtractions
are charged. Every new grouped source has exactly the corresponding old
schedule's multiplication count and one fewer addition; no group product
is silently reused or re-evaluated without being charged.

## 4. Exact degrees, finite census and the combined frontier

All supplied witnesses and x have degree one; compiler numerals have
degree zero. Put Q=(B−1)J and k0=eta+zeta. The actual highest form of L is

    L_top=w*s²*k0*Q⁷, degree11.

Thus N0' has the nonzero highest homogeneous form

    −w²*s⁴*k0²*Q¹⁴, degree22.                    (7)

Its old gap-coordinate factor had degree12. Every other factor and
retained comparison has exactly its parent's polynomial, independently
of the removed g coordinate. Their exact degrees and uniform highest
forms therefore transfer directly from the pinned asymmetric proofs.
For clarity, the linear-input factor N2 has highest form
4delta(2rho−delta)w³s³Q¹², degree20; the gap N3 has highest form
2e f² k0 w²s³Q¹¹, degree20. The ordinary strong residual has degree22
and the retained linear residual has degree6. The source verifies the
actual factor and residual leading coefficients with literal full
polynomial expansions, without substituting a leading-term shortcut.

These leading forms are nonzero for every admissible fixed program:
B−1 is nonzero, the displayed variable factors are nonzero polynomials,
and Ctop=Q−F−Z−alpha−2dx in the transport form has coefficient−1 on F.
The proof is uniform in valid compiler numerals; the finite expansions
are checks of this symbolic argument, not its replacement.

If group weights are s_j and the largest retained residual degree is r,
products add degrees in the integral domain of real polynomials. Sums
of real polynomial squares cannot cancel their highest terms. Hence

    SOS degree    = 2max(r,s_0,...,s_(g−1)),
    anchor degree = s_a+2max(r,{s_j:j!=a}).         (8)

In the empty residual case the anchor has its own degree. Formula (8)
is exact, not a syntactic upper bound or a zero-set substitution.

The restricted-growth enumerator places each next factor in an existing
group or one new last group. Every unordered partition has exactly one
such construction. It enumerates all anchors and the SOS choice for
every partition. Across the three plus ten bases this is **29,631
partitions and149,336 finalizer choices**. Each ordered objective stream
has a deterministic digest in the [receipt](complete86_first_root_partitions.json).
All101 best-by-operation-count plans are actually emitted and checked;
the thirteen frontier representatives below have their complete sources
saved. The code does not claim to save or execute149,336 full circuits.

The exact frontier within the new first-root family alone is

    86/179,87/135,88/123,89/119,90/114,91/102,92/80,
    93/76,94/64,95/54,96/50,97/48,98/44.

The union with the entire frozen asymmetric grouping frontier is

    86/179,87/135,88/123,89/113,90/109,91/102,92/80,
    93/72,94/62,95/54,96/50,97/48,98/44.

Thus89/119,90/114,93/76 and94/64 from this packet are dominated by
retained older constructions; their family-local status does not turn
them into global improvements. The four additional improvements in the
opening table have these literal plans:

- 88/123: one anchored product of all eight linear coupled factors.
- 91/102: linear coupled groups (N0,N1,Nk,Nt), (N2,N3,L), with degrees50,51,
  plus the full degree22 strong residual, finalized by SOS.
- 92/80: original asymmetric ordinary groups (N0,N1), (N2,Nk), (N3,Nt,L),
  with degrees40,39,34, plus the full degree22 strong residual, by SOS.
- 95/54: linear coupled groups (N0,Nt), (N1,Nk), (N2,L), (N3), with
  degrees25,25,27,24, plus the full degree22 strong residual, by SOS.

Optimality here means only the exact nondominance of the finite families
and literal schedules specified above. It is not an arithmetic or degree
lower bound for universal Diophantine equations. No wider grouping,
affine-recoding, norm or auxiliary-root optimization is included.

## 5. Reproducibility and guards

The implementation uses only the Python standard library and reads
24 pinned source, receipt and proof files. It executes no historical
Python module. From a checkout, with ROOT the WIP directory, run

```sh
python3 /path/to/complete86_first_root_partitions.py \
  --root "$ROOT" --expect /path/to/complete86_first_root_partitions.json
```

When installed beside its parents, the default root is the script's
own directory and a no-argument invocation performs a fresh typed
receipt comparison. `--output PATH` writes a receipt. Assertions-disabled
Python (`-O`) is rejected.

The public `canonical_parent`, `base`, `build`, `checked`, `evaluate`,
`coordinate` and `polynomial_source` APIs authenticate the selected full
canonical source and metadata. Recursive type-sensitive equality rejects
float/Boolean aliases, modified coefficients, no-op/incorrect parents,
changed weights and stale comparison interfaces. Canonical partitions
use increasing indices and groups ordered by their least member. Parent
caches are private; returned packets are defensive copies. Every access
rehashes the frozen sources, including on a warm cache.

`evaluate` accepts exact integer assignments with every supplied input,
fixed numeral and witness present; its default requires them all positive.
The admitted fixed compiler contract is inherited, not inferred merely
from this arithmetic type check. `signed=True` is an explicit arithmetic
mode. `coordinate` supplies the triangular integer maps; `positive=True`
checks both ends and can reject inverse maps away from zeros. Low-level
`execute` and private degree/circuit helpers are arithmetic utilities,
not alternative canonical validation entrypoints.

The deterministic author checks include808 full graph/manual-finalizer
identities (404 signed,101 rational),968 factor/comparison/output DAG
cuts,5,992 individual factor identities,190 factor and18 retained-residual
degree expansions,26 complete frontier polynomial expansions at two
primes,138 local positive inverse fixtures covering both unit signs,
1,415 malformed packet rejections,52 malformed plans,39 no-op/wrong
parents,13 rejected positive off-zero inverses,13 copy-isolation checks
and two warm-cache pin rejections. These checks do not materialize a
full accepting universal Pell tuple. Soundness, completeness and the
unbounded-duration ordinary-input interpretation follow from the
parametric proof in Sections1–2 and the unchanged authenticated parent
theorems. No external horizon, free universal input decoder or weakened
native obligation is introduced.
