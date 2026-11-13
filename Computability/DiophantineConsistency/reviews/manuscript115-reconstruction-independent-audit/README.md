# Independent review of manuscript 115's reconstructed 12-variable circuit

The independent audit actually exited 0. Receipt SHA-256:
`7c2280abbe67a3fd499f77193490d98c5c3d6f3aaf1a320d8542dae2dfb882ab`.
It independently authenticates the 45-file manifest, all 27 present files and
all 18 missing destination-to-historical-blob mappings against the fixed Git
commit. Both detached reconstruction invocations, ordinary and optimized,
actually exited 0 and each ran the unmodified restored supplement checker in
both modes with exit 0. Running the incomplete supplement directly exited 1.
The review itself rejects optimized Python.

The pinned parent has 96 live binary gates; the child has 95 (52 multiplications,
25 additions and 18 subtractions). The reviewer checks complete topology,
liveness, input and port lists, output, exact changed-row sets and all consumers
of cut-internal nodes. Independent sparse integer-polynomial expansion verifies

```
M*g31 + qm*Y - q3*(1+k*qm)*Bt
    = M*(g31-k*Bt) + qm*Y - q3*Bt,   M=q3*qm.
```

Only the certified cut output `Z` escapes its changed internal nodes; all
other corresponding rows agree. Induction over the remaining DAG therefore
proves the two literal polynomials equal for all integer inputs and all four
integer ports, hence gives the same positive-integer zero set. This is a finite
graph identity; it does not establish the parent's source calibration.

The degree-70 claim can be checked independently, and this review does so:

1. Treat all four ports as coefficients. The graph gives `deg(M)≤4`,
   `deg(ell)≤4`, `deg(k)≤1`, `deg(Bt)≤2` and `deg(q3)≤3`. Expanding the
   certified cut gives `Z=M*ell+B` with `deg(B)≤7`. The exact identity
   `Z²−M²(ell(ell+k)+1)=2*M*ell*B+B²−M²(ell*k+1)` bounds `A0` by 15.
2. Write `Dstar=U*a*c+L`; the checked rows give `deg(U)≤3`, `deg(a)≤2`,
   `deg(c)≤2` and `deg(L)≤6`. Since `Delta=a²+4a+3`, cancellation of the
   two leading squares bounds `A1` by 13.
3. The checked tail is `h=(1−Q)(V+n)²+Q*V²−1`, identically
   `V²+2(1−Q)Vn+(1−Q)n²−1`. With `deg(Q)≤6`, `deg(V)≤6` and
   `deg(c⁴)≤8`, this bounds `h` by 13 and the polarized residual `N` by 42.
   The final product `(1+A0)(1+A1)(1+N)−1` therefore has degree at most 70.

All three cancellations are independently expanded as exact free-ring
polynomials, and the graph rows and remaining degree propagation are checked.
For the lower bound, every witness is replaced by the same variable `x` and
the complete 95-gate graph is evaluated using the **exact four recovered
port bytes**. Its `x^70` coefficient is 794 modulo 1009, 738 modulo 1013,
and 683 modulo 1019. Any one nonzero residue proves the integer coefficient
is nonzero, so the full multivariate polynomial has degree at least 70. The
upper and lower bounds prove exact degree 70 for this bound tuple. These are
finite calculations and ordinary algebra, not a Lean theorem.

All four decompressed payload hashes match the manuscript 98 binding; beta is
`2^590069−1`, and the `MF_source` payload is used as the already shifted port.
The alternate `compact44_bfs` tuple agrees on beta, MC and MF but its K0 raw
hash `4364134a…` differs from the reconstructed K0 `c6d523bd…`. The
port-parametric graph identity applies to either tuple, while a fixed-port
source claim needs the correct complete binding.

The inherited free-J ordinary equivalence is **not independently proved** by
this review. Its supplied arithmetic argument, earlier Pell/rank and
integrality results, and native/compiler/refutation calibration remain a
substantial chain to check; equality with a parent graph and a matching payload
hash do not themselves establish those claims. No object-theory iPRA proof or
arbitrary-checker equivalence is claimed. The original review's fixed-recipe
and provenance boundaries also remain.

The first reviewer attempt completed its checks and wrote a provisional
receipt but exited 1 while printing its hash because a `Path` was passed where
bytes were required. That unsuccessful receipt is retained explicitly; the
corrected review ran from the beginning. A subsequent successful intermediate
review was strengthened to check that no cut-internal node escapes except via
`Z`, and the final successful review reran all checks.
