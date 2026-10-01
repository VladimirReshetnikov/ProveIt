# Computed positive selector ports remove eight witnesses and equations

The [shared sparse matrix compiler](group_shared_sparse_matrix_compiler.md)
already computes the eight physical selector outputs from its edge hats.
Using those expressions directly removes their eight supplied positive
coordinates and eight comparison equations. The literal certificate
retains every arithmetic gate and costs

    3m+3h+p+222+f_flow-3min(h,3).

It now has **39 equations** and **m+59 strictly positive existential
witnesses**. Its single sum-of-squares polynomial costs

    3m+3h+p+338+f_flow-3min(h,3),                      (1)

exactly24 operations less than its parent, and retains exact degree
**12m+112**. The complete ordinary-input relation is unchanged, with
a bijection of positive solution sets given by erasing or reconstructing
the eight selector coordinates.

The parameters m=2^h, p and f_flow refer to the same fixed macro table
and literal sparse-flow schedule as before. In particular f_flow<=2L
for total nonempty macro length L. No numerical universal subgroup
alphabet is instantiated by these formulas.

## 1. The eight affine positive graph coordinates

For physical letter i+1, let I_i be the fixed set of controller edges
with that label and let k_i be its size. The parent already computes
the port expression

    Phi_i=1+sum_(e in I_i)(Ehat_e-1).                  (2)

Its actual implementation is: the fixed1 when k_i=0, the edge hat
itself when k_i=1, or the sum of its k_i hats minus the fixed numeral
k_i-1 when k_i>=2. These are the existing paid p port operations;
there is no new evaluation of(2).

For arbitrary strictly positive edge hats, every term Ehat_e-1 is
nonnegative. Hence

    Phi_i>=1                                         (3)

before any checksum, typing, adjacency or other equation is assumed.
An entirely unused physical letter simply has Phi_i=1. This is the
unconditional positivity needed to replace a supplied positive field.

The parent compares Phi_i with Shat_i. Substitute Phi_i for every
occurrence of the supplied Shat_i, then delete that comparison and
the Shat_i coordinate. Perform this for all eight ports. Every other
supplied coordinate, fixed program numeral and ordinary input x is
unchanged. The decoded nonnegative selector becomes the computed
quantity Phi_i-1; no extra decoding gate is introduced.

## 2. Acyclic literal source after substitution

The parent evaluates some history and mask instructions before the
old port definitions because Shat_i was an independent input there.
Direct substitution therefore requires a topological reorder.

Each Phi_i depends only on supplied edge hats and fixed integers. It
does not depend on a history word, a selected-source product, a native
kernel output, B or another physical selector. Thus all port expressions
can be evaluated first if needed; replacing their uses creates no cycle.
The computed history register B=8q_geom^2 likewise remains available
before any dependent controller or mask instruction.

The [source](group_computed_selector_ports.py) substitutes the existing
literal port registers or constant aliases into the parent instructions,
then uses a stable topological sort. It emits each original instruction
exactly once, with the same operation. It adds no copy gate, evaluates
no uncharged expression, and does not fold newly constant operations.
The source checks every operand's availability and records the original
position of each instruction in the new order.

All eight equations remain represented as identities after substitution:
each becomes Phi_i=Phi_i. They are then omitted from the comparison list.
The remaining39 comparisons keep their parent order, with the same
operand substitution.

## 3. Exact polynomial identities and the positive bijection

Write z for all retained supplied coordinates, including the ordinary x.
Let Phi(z) append the eight affine port values(2). On arbitrary integer
assignments, evaluation of every retained source register in the new
schedule agrees with its parent evaluation at Phi(z). This follows by
induction through the topologically ordered dependency graph.

If R_j are the47 parent residuals and R'_j the39 retained ones, then

    R'_j(z)=R_j(Phi(z))             for retained j,
    R_j(Phi(z))=0                  for the eight ports. (4)

Consequently the new39-term SOS is identically the parent's47-term SOS
after this affine substitution, as an integer polynomial. This is an
identity with a specified coordinate map, not a claim that two
polynomials in different variable lists are literally the same source.

For positive z, (3) makes every appended coordinate positive. A new
positive zero therefore extends to a parent positive zero. Conversely,
any parent positive zero already satisfies Shat_i=Phi_i, so erasing
the eight coordinates produces a new positive zero. Reconstruction
returns exactly the erased values. These two maps are inverse on
the complete positive solution sets, including noncanonical choices
of all remaining Pell witnesses.

No equation is needed to establish positivity in this argument. Signed
off-zero evaluations support the polynomial identities in(4), but are
not used as positive witness extensions.

## 4. The complete trace proof still has the same dependency order

The parent scalar bootstrap is unchanged. Its independently proved
linked-geometry core types q_geom and B; the joined AND source types P;
and the repunit relation supplies their common duration. The positive
native domains remain valid because each computed Phi_i is positive.

The crucial low-mask bound still precedes Boolean selector typing.
With E_e=Ehat_e-1, the controller checksum gives

    sum_e E_e=J, E_e>=0.

The computed selector satisfies

    S_i=Phi_i-1=sum_(e in I_i)E_e, 0<=S_i<=J.

Thus `(B-1)S_i<=P-1` follows exactly as before, now directly from
the definitions and checksum. This allows the joined binary regions
to be separated without assuming the Boolean conclusion in advance.

The shared typing kernel then recovers the edge digits, the unchanged
flow comparison recovers the chronological path, the computed physical
ports give the corresponding mutually exclusive letters, and the
selected-source and canonical-history arguments finish the trace.
The same one-vector lemma fixes the final matrices. Both native cores
retain their independent positive coordinates and their original
scales. No geometry, controller, product, digit-range or endpoint
obligation becomes external again.

The full positive converse can equivalently be read through the
bijection in Section3: take any parent accepting word and positive
witness tuple and erase its eight physical port coordinates. Its
original ordinary input and all other witnesses remain unchanged.
For a macro list containing fixed subgroup generators and inverses,
the complete subgroup-membership theorem therefore persists with the
same `r=alpha*x+beta`. The numerical universal-alphabet limitation is
also unchanged.

## 5. Exact operation counts and degree

Let f_M,f_A be the inherited sparse-flow multiplication/addition costs.
Let delta_M,delta_A be the already proved geometric register savings:
`(1,2)` for h=1, `(3,3)` for h=2, and `(5,4)` for h>=3. Every
certificate gate is retained, so its split is still

    certificate_M=m+2h+101+f_M-delta_M,
    certificate_A=2m+h+p+121+f_A-delta_A.              (5)

Only the supplied domain and comparison list change: m+67 becomes
m+59, and47 becomes39. The literal SOS now uses39 subtractions,
39 squares and38 summation additions, costing39M+77A=116 operations.
Hence its exact split is

    polynomial_M=m+2h+140+f_M-delta_M,
    polynomial_A=2m+h+p+198+f_A-delta_A.               (6)

The difference from the parent's47M+93A compilation is8M+16A=24
operations, proving(1). All fixed-numeral products and squares remain
charged; the count reduction is not obtained by omitting a residual
while silently retaining its constraint.

Every Phi_i is affine in retained variables, so substituting it cannot
increase total degree. The unique highest residual is still the joined
kernel's first norm, with degree6m+56 and highest form

    w_selection^2*s_selection^4*k_selection^2
      *(16P^(m+8))^6.

It does not involve the removed Shat coordinates. It is nonzero after
substitution, and all other residuals remain of smaller degree.
Squaring therefore gives exact degree12m+112. Supplied coordinates
have degree one and compiler numerals degree zero; no zero-set
identity such as P=B^t is used to measure degree.

For example, the same ten-letter fixture has m=16,h=4,p=4,f_flow=19.
Its certificate still costs296 operations, while its polynomial falls
from436 to412 operations. It has75 positive witnesses and degree304.
These are audit-table values, with no universality assertion for that
particular alphabet.

## 6. Reproducible evidence

The [receipt](group_computed_selector_ports.json) records six complete
source DAGs, the exact affine port aliases, the reordered original
instruction positions, deleted residual indices, retained39 comparisons,
positive coordinate lists and literal ledgers.

On1,536 supplied assignments, the checker extends the parent with the
independently expanded formulas(2), then compares every retained
register, every retained residual and the complete parent/new SOS.
It checks that the eight deleted residuals vanish identically under
that extension. Among these cases,1,152 have every supplied coordinate
positive and explicitly check every Phi_i>=1;384 signed cases audit
only polynomial identities. Empty macro lists, absent letters,
single-edge ports and multiple-edge ports are included.

Weighted offset evaluations for m=2,4,8,16 verify the exact degree and
highest coefficient of the actual reordered DAG. These finite checks
supplement the general graph-substitution proof; they do not generate
or claim full astronomical Pell witness tuples.

Run the source normally to compare the deterministic receipt, or with
`--write` to regenerate it. All parent sources remain unchanged.

Two independent full proof/source/default reviews passed without findings.
They checked unconditional port positivity, the affine graph bijection,
the eight identically vanishing residuals, acyclic operand substitution
and unchanged gate multiset, both native domains and the scalar mask
bootstrap, and the exact witness/equation/operation/degree ledgers.
One review additionally tested 384 full graph substitutions on 96
separately generated tables with h=1 through6, including 192 positive
extensions and 192 signed identity cases. Every retained register,
all 39 residuals and the complete parent SOS agreed under the independent
port formulas. Neither review treats those finite checks as full Pell
witness construction.
