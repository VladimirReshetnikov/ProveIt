# Peer review: shared CRT with prime-supported lifting

Status: **PASS for the ordinary arithmetic modification and exact candidate.**
I found no missing coprimality, positivity, witness-bound, or empty-index
condition in the frozen proof. No Lean work was performed. The inherited
C222/refutation calibration and an internal object-ZFC proof remain distinct
dependencies; finite polynomial checks do not discharge them.

| Nonnegative-integer equation | Variables | Quadratic rows | Exact degree | Quartic terms | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Received affine variant | 3,614 | 2,954 | 4 | 15,996 | 127,778,545 |
| Prime-lift affine variant | **3,609** | **2,949** | **4** | **15,752** | **127,285,349** |
| Received retained-wire variant | 6,183 | 5,523 | 4 | 17,430 | 1,993 |
| Prime-lift retained-wire variant | **6,180** | **5,520** | **4** | **17,421** | **1,992** |

These are actual complete collected quartics over nonnegative integers.
They are not unrestricted-integer equations without a domain conversion.
There are no newly supplied native coefficient ports. The same closed
numerical C222 calculus and sealed refutation target are retained.

## Why removing the factorial-size bound is sound

For nonnegative-coefficient polynomials `E,F`, index bound `N`, and
coordinate bounds `u_j`, set

```
H = E(N,z,u)+F(N,z,u)+N,  T=H!,
d_i=1+(i+1)T,            B=product(i<N,d_i).
```

Suppose the encoded certificate gives `B | binom(A_j,u_j+1)`,
`B | 1+(C+1)T`, and `E(C,z,A)=F(C,z,A) mod B`.
For each `i<N`, a prime `p | d_i` exists. It is coprime to `T`, hence
`p>H`. Multiplying, rather than cancelling, the range divisibility gives

```
p | (u_j+1)! binom(A_j,u_j+1)
  = product(r=0..u_j, A_j-r).
```

Primality supplies a root index `w_j<=u_j` with `A_j=w_j mod p`.
This argument does not need `p>u_j`. If `A_j<=u_j`, the numerator has an
actual zero factor and the integer identity still holds. Cancelling the
nonzero residue `T` in the index congruence gives `C=i mod p`. Monotonicity
then makes the two decoded values congruent modulo `p` and each at most
`E(N,z,u)+F(N,z,u)<=H<p`; they are equal as integers.

Thus the old condition `H>=u_j+1` was needed only by the old completeness
argument. It is not needed by soundness, and the new proof never asserts
the generally false bounded-root conclusion modulo a composite `d_i`.

## Why the stronger CRT periods prove completeness

Since `H>=N`, the original `d_i` are pairwise coprime. For a fixed column
write `R_j=(u_j+1)!` and define its prime-supported factor

```
R_ij = product(p prime dividing d_i, p^v_p(R_j)),
M_ij = d_i*R_ij.
```

Then `R_ij | R_j`, `gcd(d_i,R_j/R_ij)=1`, and the prime supports of the
`M_ij` remain disjoint as `i` varies. Finite CRT can therefore impose
`A_j=w_j^(i) mod M_ij` for all rows. Adding a sufficiently large multiple
of `product_i M_ij` makes `A_j>u_j`, while retaining every strengthened
congruence. These encoded columns are not themselves bounded witnesses:
their residues supply the bounded local witnesses.

The falling numerator contains `A_j-w_j^(i)`, so its valuation at each
prime `p|d_i` is at least `v_p(d_i)+v_p(R_j)`. Equivalently,
`d_i R_ij | R_j binom(A_j,u_j+1)`. Cancel the positive `R_ij`, then
cancel the coprime factor `R_j/R_ij` modulo `d_i`. This yields the required
binomial divisibility modulo `d_i`; pairwise coprimality yields it modulo
`B`. This cancellation is licensed even when `gcd(B,R_j)>1`.

The index `C` has an independent CRT construction using the original
`d_i`. Strengthened column congruences imply the evaluation congruence
modulo each original modulus, so all columns and the index are compatible.
Prime factorization is used only to prove existence of the encodings;
it is not a new operation in the final quartic.

A plain `+B` shift would be wrong: for `B=3,u=2,A=1`, the binomial is
initially zero but `binom(4,3)=4` is not divisible by three. The lifted
period is nine, and `binom(10,3)=120` has the required divisibility. The
frozen proof explicitly uses the stronger period.

For `N=0`, the modulus product is one. The row condition is vacuous and
all three certificate conditions are automatic; choose any `A_j>u_j`
and any nonnegative `C`. This includes the possible value `H=0` in the
abstract theorem. It does not authorize a zero argument at an actual
specialized positive-power call: the concrete compiler has `t=t0+1>=1`.

## Concrete source bounds and positive-power specialization

The three formula labels remain bounded by `m`. The other ten local
coordinates may be bounded by an independent `U`, since a finite proof
and its accumulator/beta witnesses are selected before `U` is chosen.
Taking `U` at least their finite maximum suffices; no relation `U>=m` is
needed. Replacing `m+U` by `U` does not alter the local predicate or force
any encoded column to be below `U`.

The literal signed-split arithmetic computes `P=E-F` using natural
constants, addition, multiplication, and their nonnegative pair versions.
Consequently both `E` and `F` have nonnegative coefficients separately,
even when the underlying residuals have negative coefficients. Bounding
the local coordinates therefore bounds both sides separately; no
monotonicity of `P` itself is assumed.

An independent DAG builder interpreted the pinned literal calculus using
only addition and multiplication. All 461 reachable arithmetic nodes
have nonnegative constants and topological dependencies. At the proposed
bound substitution their only leaves are `N,x,y,m,M0,U`; neither encoded
columns nor the encoded index enter `H`. This checks the absence of a
circular witness bound and the structural monotonicity used above.

For the actual compiler `H=E+F+t>=t>=1`. The column parameterizations
`A_j=alpha_j+1` and strengthened CRT representatives make every range
binomial's upper argument positive; each lower argument `u_j+1` is
positive even when `U=0`. The unchanged ordered static audit verifies all
55 specialized power calls, all sixteen binomial calls, and the two
factorial calls on the patched source. The existing Pell power graph
retains its side conditions; the new CRT theorem does not weaken them.

## Exact replay evidence

The authenticated parent ZIP has SHA256
`61582dab90e880049e61ff1a5c49386747cd063de15e18411a20f327b9559ba1`.
The candidate checker verifies that the patched compiler differs in
exactly two stated expressions; every calculus, source, power graph, and
arithmetic auditor is byte-identical to the original archive. The builder
and all four complete polynomial/residual hashes are recorded in the
accompanying JSON.

I independently reran normal and `-O` candidate checks in isolated copies.
Both verify full quartic expansion and metrics, complete nonnegative
affine restoration, the static power induction, the literal power graph,
and the candidate's 2,856 strengthened-CRT controls, including 1,380
noncoprime-factorial cases. The unchanged exact calculus auditor also
passes in both modes. Normal and `-O` generator `--check` runs regenerate
all candidate outputs byte for byte. Original archives and candidate
files were not modified by these replays.

The separate `shared-prime-lift-peer.py` uses prime factorization and
Legendre's factorial-valuation formula, rather than the candidate's
repeated-gcd routine. Its controls cover 810 strengthened CRT cases,
including 465 with factorial noncoprimality, 675 with `u+1>H`, and 162
empty-index cases. It also checks 8,214 prime-root extractions, including
3,351 with `u>=p`, and the unsafe plain-`B` shift. Normal and `-O` receipts
agree apart from the mode field. These controls supplement the unbounded
proof above; no finite sample stands in for that proof.

The new construction preserves the same refutation predicate by the
ordinary finite-CRT argument. Proving its full consistency equivalence
inside the encoded object-ZFC calculus is still a separate task, as the
candidate correctly states.
