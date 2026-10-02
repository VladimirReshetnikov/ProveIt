# Centered state arithmetic gives a complete 611-operation polynomial

Centering the two numerical state projections at7 reduces the complete
[621-operation compiler](u15_packed_grouped_projections621.md) to
**611=239M+372A operations**. The raw natural half-tape interface costs
**368=131M+237A**. Every comparison residual and the entire final polynomial
remain equal on **all integer assignments**, including signed tuples.
All supplied coordinates and their semantic domains are unchanged.

| Interface | Certificate | Comparisons | Positive witnesses | Complete polynomial |
|---|---:|---:|---:|---:|
| Natural initial half tapes |336=120M+216A|11|51|368=131M+237A|
| Positive ordinary input, fixed program numerals |474=193M+281A|46|102|611=239M+372A|

The [compiler](u15_packed_centered_states611.py) emits all gates, comparisons,
metadata and finalizers; the [receipt](u15_packed_centered_states611.json)
contains both complete sources and exact identity certificates. The formal
degree upper bound remains1936. No exact-degree, optimality, or improvement
of the separate global87 bound is claimed.

## 1. Actual paid centered projections

Retain the parent's fixed29 rule indices, including its B/J numerical state
permutation. Put E_i=edge_i-1 and J=sum E_i. The parent's source-state pairs
are already computed and reused in all eligible coefficient groups.
For the *supplied hats*, define

```
S_q=sum_(i:source(i)=q) edge_i,
T_q=sum_(i:target(i)=q) edge_i.
```

Every nontrivial sum below is computed by the actual DAG and charged; the
fourteen shared source-state pair sums are emitted once and used in J as
well. The zero-coded groups, omitted from the old positive-coefficient
state projection, are now included wherever needed. The center7 groups
have coefficient zero and need no separate state-projection sum.

Define the two signed deviations by symmetric differences:

```
Qdev=sum_(k=1)^7 k*(S_(7+k)-S_(7-k))-6,
Ndev=sum_(k=1)^7 k*(T_(7+k)-T_(7-k))+17.
```

These offsets follow from the actual relabeled29-rule table:

```
sum_i source(i)=209,  209-7*29=6,
sum_i target(i)=186,  186-7*29=-17.
```

Consequently they are literal affine identities

```
Qdev=sum_i (source(i)-7)E_i,
Ndev=sum_i (target(i)-7)E_i.
```

Each symmetric projection uses the coefficients1 through7, so multiplication
by1 is a copy and the other six multiplications are paid. Every difference,
coefficient-group sum, final summation and hat-offset correction is paid.
Signed intermediate values are allowed in an integer polynomial; these
computed registers are not new positive existential coordinates.

The active register metadata names them **Qdev and Ndev**. It does not expose
old Q or N names with changed meanings. The relations

```
Q=7J+Qdev,  N=7J+Ndev
```

are mathematical identities used in the proof; the compiler does not emit
the two full projections or an extra7J register.

## 2. State transport uses a computed polynomial identity

The parent's actual state residual, after its earlier B/J permutation, is

```
R=B*N-Q-P.
```

The complete source already computes

```
P=(B-1)J+1.
```

This is a definition on every supplied tuple, not an equation assumed to
hold only at a solution. Substituting the affine identities above gives

```
R=B*Ndev-Qdev+7(B-1)J-P
 =B*Ndev-Qdev+6P-7.
```

The new comparison is therefore

```
B*Ndev+6P=Qdev+7.
```

Its difference is exactly the old residual on every integer assignment.
The new comparison costs two multiplications and two additions; the old
one cost one multiplication and one addition. These two additional operations
are included in the final ledger.

The proof uses no one-hotness, dyadic radix, native AND, positivity, Pell
norm or halting assumption. In particular it does not substitute a semantic
equality into a polynomial away from its zero set. Every other residual is
unchanged, so the full sum of squared residuals is the same polynomial.

## 3. Complete source proof and exact savings

The constructor authenticates the frozen621 Python source by SHA-256

```
8cadeb24c695b1956cd5cb25f93d41261065ddc45c116d7c9b0d0e3d7e4906d3
```

The parent's authenticated lineage, sibling-import isolation and complete
canonical packets are retained. The constructor rebuilds the actual raw
source using the shared pairs, fixed centered projections and the new state
comparison, then appends the unchanged complete ordinary loader and the
frozen paid tag/truth-field transformation. The complete finalizer is rebuilt.

For both full interfaces the exact identity certificate establishes:

- The unchanged affine forms J,S,Dir,W,WD and the two explicitly centered
  affine forms Qdev,Ndev, including their full hat offsets.
- Exact downstream expression-DAG identities for all nonstate comparisons:
  ten raw and45 ordinary, plus all other common semantic registers.
- The actual emitted state residual `B*Ndev-Qdev+6P-7` and the actual computed
  geometry `P=(B-1)J+1`, followed by exact polynomial expansion of their identity.
- The literal complete SOS finalizer for both the parent and child, proving
  equality of the entire final polynomial rather than merely its zero set.

The paid source-state/target-state blocks and state comparison have these
literal operation counts:

| Block | Parent621 | Centered611 | Difference |
|---|---:|---:|---:|
| Q projection / Qdev |13M+14A=27|6M+14A=20|7 fewer M|
| N projection / Ndev |13M+23A=36|6M+25A=31|7 fewer M,2 more A|
| State comparison operands |1M+1A=2|2M+2A=4|1 more M,1 more A|

Everything else has the same cost. Thus13 multiplications are removed and
three additions/subtractions are added, for a net saving of10 operations.
The identical11/46 residual finalizers remain fully charged. Constants and
copies are free; every emitted binary addition, subtraction or multiplication,
including by a numerical coefficient or fixed program numeral, costs one.
All emitted gates reach the complete output.

A bounded arithmetic scout also checked center6. Its deviation form ties at
611 operations but costs241M+370A, whereas center7 costs239M+372A. Center7
was chosen for fewer multiplications at the same total. Restoring full Q,N
at either center costs612 operations. This is a comparison of these concrete
schedules, not a lower bound or optimality claim. The maintained compiler
uses only the fixed center7 schedule and runs no search.

## 4. Domains, metadata and inherited universality

No parameter or witness is added, removed or renamed. The raw interface
still has natural supplied L0,R0 and51 strictly positive witnesses. The
ordinary interface still has positive x, four fixed positive program numerals
and102 positive witnesses, with46 comparisons. Its complete loader and input
padding convention are unchanged.

Because the entire polynomial is identical on all integer tuples, its
zero set is identical on the declared natural/positive domain. The full
unbounded first-halt theorem and the effective valid-program-slice
universality theorem transfer directly from621. No fresh native extension
or witness transformation is required for this arithmetic step. The earlier
native and loader proofs remain the existing prerequisites; this packet adds
no external horizon, typing predicate, order assumption or unpaid operation.
Arbitrary positive program tuples are not newly asserted to encode programs.

The current metadata replaces the old Q/N projection names with Qdev/Ndev,
records center7 and its comparison, identifies621 as the canonical parent,
and retains the correct source lineage. It does not inherit a stale graph
parent descriptor. The private canonical cache is exposed only through
explicitly private `_context` and `_bundle` helpers; public exports are copied.

## 5. Public API and reproducibility

The documented public APIs are

```
build(ordinary=False, *, root=None)
canonical_parent(ordinary=False, *, root=None)
checked(packet, *, root=None)
polynomial_source(packet, *, root=None)
evaluate(packet, values, *, signed=False, root=None)
identity(packet, values, *, signed=False, root=None)
verify(root=None)
```

The sibling layout works by default. An explicit root points to the directory
holding the baseline and retained dependencies; during isolated review the
pinned621 file may sit beside this script. Public access authenticates that
file and the parent's retained lineage. Flags must be exact Booleans, packets
must have their complete canonical scalar/container types, and assignments
must contain exactly the declared exact-integer coordinates. Formal signed
evaluation is explicit. `identity` returns the common full output and all
comparison residuals after checking both complete sources.

The research compiler requires assertions enabled and rejects `python -O`
at import. This matches its research-proof contract. Public validation and
source pins additionally use explicit exceptions. No general hostile-Python
sandboxing claim is made.

Run a fresh read-only receipt comparison with

```
python u15_packed_centered_states611.py --root /path/to/native-stream-queue
```

Only `--write` regenerates the adjacent receipt. The author writer checks128
complete polynomial identities, including64 signed tuples and3,648 individual
residual identities;1,153 malformed object/assignment rejections; six defensive
copy checks; and two cold no-file/foreign-loader isolation regressions. Exact
symbolic certificates are rebuilt for both full sources. Literal closure,
liveness and degree propagation are checked by the pinned finalizer.

The finite replays supplement the all-value source proof. They do not
materialize full native Pell witnesses or search an unbounded witness space.
The ledger retains the inherited1936 formal degree upper bound and makes no
new exact-degree assertion.

## Independent review and inherited exact degree

The [independent review](review_u15_centered611.md) passed the actual old/new
state comparisons, both computed P definitions, all remaining residual DAGs,
and both literal complete finalizers. Its all-value polynomial identity
transfers the separate [exact-degree1936 proof](u15_packed_exact_degree1936.md)
through621 to this circuit. The frozen source metadata remains upper-bound-only.
