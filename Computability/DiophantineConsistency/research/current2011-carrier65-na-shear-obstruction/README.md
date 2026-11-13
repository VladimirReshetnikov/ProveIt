# Auxiliary-factor shear and a direct-alias obstruction

This is a source-only observation about the 65-live-operation, 14-positive-coordinate carrier equation. It gives an exact zero-preserving transformation and proves a narrow obstruction to sharing a particular family of transformed nodes with the existing graph. It **does not find an equation with fewer than 65 operations**, prove minimality, or provide a Lean proof. The established fact `Na = 1` on zeros already appears in the independently audited carrier proof; the auxiliary-factor shear and the direct-alias argument below are the observations recorded here.

Run `python3 research/current2011-carrier65-na-shear-obstruction/check.py` from `Computability/DiophantineConsistency/`; its deterministic stdout is recorded in `result.json`. It pins the independently audited incoming graph and proof, the maintained graph, and all four maintained coefficient files by hash. It checks that both graphs have exactly the same 65 ordered operations, are topologically valid, all gates reach the output, and have counts 16 additions, 12 subtractions, and 37 multiplications. It verifies the dependency and factorization shapes used below, all 64 residue triples modulo 4, and two exact formal ring identities by a small integer-polynomial implementation. These finite checks support the proof; they are not a substitute for its unbounded arguments or a source-current Lean rebuild.

## Existing equation and the unit anchor

Use the exact node names in the pinned graph, and write

```
D  = Dc2 = Delta*c²
S  = normalized_S = i*D
Ns = f² - Delta*i²*c⁴
Na = y² + S²*(V²-y²)
F  = N0*N1*Na*Nt*scaled_Ns - Delta
   = Delta*(N0*N1*Na*Nt*Ns - 1).
```

The second equation follows because `scaled_Ns = Delta*Ns`. All coordinates are positive integers and the four authenticated integer ports are positive. In particular `a = E+Y > 0`, so `Delta = a²+4a+3 > 0`. Thus `F = 0` forces the five displayed integer factors in the parenthesized product to be units, in particular `Na ∈ {−1,1}`.

For **all integers** `S,V,y`, the number `Na` cannot equal `−1`: if `S` is even, `Na ≡ y² (mod 4)`; if `S` is odd, `Na ≡ V² (mod 4)`. A square is 0 or 1 modulo 4. Consequently every original zero satisfies `Na = 1`. This does not depend on `z` or on the signs of `S`, `V`, or `y`.

## A sound z-shear

Let `h` be any integer polynomial in the original 14 coordinates with fixed integer coefficients, and put

```
z'  = z + h*(Na-1)
Nt' = transport_partial - z'*qm
F'  = N0*N1*Na*Nt'*scaled_Ns - Delta.
```

The original DAG has exactly two z-dependent nodes before aggregation: `zqm` and `Nt`. Therefore `N0`, `N1`, `Na`, `Ns`, `Delta`, and `qm` in this definition retain their original values. Direct ring expansion gives

```
F' - F = -qm*h*(Na-1)*N0*N1*Na*scaled_Ns.
```

If `F = 0`, the unit argument yields `Na = 1`, and hence `F' = F = 0`. Conversely, if `F' = 0`, the same factorization and unit argument apply to `Nt'`, which is still an integer: `Na = 1`, giving `F = F' = 0`. In this reverse direction the polynomial value `z'` can be **any integer** away from the zero set; it is not treated as a positive witness and its positivity is never assumed. The original coordinate `z` remains positive in both equations. This is pointwise equivalence on the same positive-coordinate domain, not merely an existential implication.

The literal instance `h=1` introduces `Na-1` and `z+(Na-1)` and can be scheduled as a 67-gate graph: move `zqm` and `Nt` after `Na`, then retain the original aggregate. No reduction is claimed; further algebraic refactoring would require its own exact validation.

## Direct original-node alias obstruction

Work over the integral domain of integer polynomials in the 14 coordinates with the four ports fixed to the authenticated positive integers. `S=i*D` is independent of `y`, and `D=Delta*c²` is independent of both `i` and `y` and is nonzero: evaluation at all coordinates 1 gives positive `Delta` and `c`. Hence `1−S²` has positive degree in `i` and is a nonunit. Also `(1−S²)+S²=1`.

Set

```
A = Na-1 = (1-S²)*y² + S²*V² - 1.
```

Here `S` and `V` are independent of `y`. Let `t` be **any y-free polynomial**, and let `h` be **any nonzero polynomial**, possibly involving `y`. Then the y-degree of `t+h*A` is `deg_y(h)+2`, because the coefficient ring is an integral domain and `1−S²` is nonzero. It cannot equal any y-free original pre-aggregation gate. The only y-dependent gates among the first 60 are, exactly, `y²`, `V²−y²`, `S²*(V²−y²)`, and `Na`. Each has y-degree 2, so equality with one would force `h` to be y-free. Comparing y² coefficients then gives:

- For `y²` or `V²−y²`, `(1−S²)*h = ±1`, impossible because `1−S²` is a nonunit.
- For `S²*(V²−y²)`, `(1−S²)*h = −S²`, impossible because the two factors `1−S²` and `S²` generate 1, while `1−S²` is a nonunit.
- For `Na`, cancellation gives `h=1`; comparison of the y-free terms then gives `t=1`.

Therefore, whenever `t≠1`, **no** expression `t+h*(Na−1)` with nonzero polynomial `h` can equal an original pre-aggregation gate. This applies, for example, to the new `z'` above; it also applies to `Na−1` by taking `t=0` and `h=1`.

This is an algebraic direct-alias statement for a single new node and the original 60 pre-aggregation gates. It does not rule out several coordinated changes, newly introduced shared gates, equality only after imposing additional constraints, alternative factor encodings, a smaller circuit, or a different zero-equivalent equation. The output factorization, port bytes, and graph are checked externally from pinned files; no binding to rendered TeX/PDF or new kernel-checked theorem is asserted.
