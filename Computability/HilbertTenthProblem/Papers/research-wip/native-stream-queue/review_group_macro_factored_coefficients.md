# Independent review of the two native coefficient factorizations

**PASS; no correction requested.** Each of the five saved macro-controller sources has an exact, same-coordinate full-polynomial rewrite saving two multiplications. The smallest saved shared-controller polynomial becomes **412=167M+245A**, with **75 positive witnesses and 47 comparisons**. Its comparison circuit becomes **272=120M+152A**. This is the named three-code fixture, not a numerical universal bound.

The [independent checker](review_group_macro_factored_coefficients.py) authenticates the complete [author trio](group_macro_factored_coefficients.md) and the frozen [five-source parent](group_macro_automaton_sharing.md). The [review receipt](review_group_macro_factored_coefficients.json) records complete source reconstruction, local coefficient proofs, downstream polynomial identities and literal paid ledgers. Neither author Python nor historical builders or suites are executed.

## 1. Actual coefficient cones and supplied coordinates

The two actual prefixes are `selection__` and `geometry__`. In each one, the parent already pays

```
E=X*Y, V=k*Y.
```

Its private four-instruction coefficient block computes

```
E2=E*E; S=E2+X; V2=V*V; coefficient=S*V2.
```

The child replaces that block by

```
L=E*V; next=L+k; coefficient=L*next.
```

Independent coefficient expansion in formal X,Y,k proves

```
(E²+X)(kY)² = X²Y⁴k²+XY²k² = L(L+k).
```

The equality is unconditional over every commutative ring. It requires the actual already-paid definitions E=XY and V=kY, which the reviewer checks literally in each source. In all ten cones, k is the supplied positive auxiliary with that prefix; it is not a computed `eta+zeta` substitute. The latter relation is an equality at zeros, not an off-zero identity. Ten explicit off-zero diagnostics detect the incorrect replacement of supplied k by that sum.

The removed E2, S and V2 registers have exactly their specified private source consumers and no direct comparison consumer. The common coefficient output retains its original name. The new two internal names are fresh. I independently reconstruct the entire child instruction sequence by inserting the three new instructions at the old coefficient output and deleting exactly the four old instructions. This matches each saved array literally.

The old E and V producers remain paid and live. Each local block changes from 3M+1A to 2M+1A. The two native first roots remain the actual triangular roots `tau*(tau+1)`, including their paid additions and multiplications. No root convention, comparison, coordinate or input loader is changed.

## 2. Entire residual and finalizer identity

After independently proving the two coefficient identities, the reviewer gives each corresponding old/new coefficient output the same formal expression marker. An exact expression DAG then proves equality of every common computed register in the complete sources. The marker is justified only after the literal cone and independent coefficient proof above pass; no author-provided cut certificate is accepted as a premise.

All 47 comparison pairs, every supplied parameter and auxiliary, the edge tables, codes, graph size, input affine constants, flow plans, radix margin and other nonarithmetic packet data are unchanged. The reviewer reconstructs every residual subtraction, square and accumulation instruction in both the old and new finalizers. This verifies 235 residual identities and five complete polynomial identities at the same supplied tuples.

Consequently each rewrite preserves its parent's zero set on every common domain, including the advertised positive integer domain. There is no new positivity restoration or existential witness choice in this factoring step. The ordinary input remains x and its complete affine loader is paid inside each verified source.

This does not identify the polynomials of different controller graphs. The parent’s language theorem relating its disjoint and shared automata is inherited separately; its different witness sets and native scales are not equated here. No large native Pell witness is materialized or needed for the exact polynomial transfer.

## 3. Complete paid ledgers

Every form still has 47 comparisons. The explicit SOS tail costs 140 operations: 47 residual subtractions, 47 squares and 46 additions. All instructions and supplied ports are live.

| Graph and flow | Comparison circuit | Complete polynomial | Positive witnesses | Polynomial degree upper bound |
|---|---:|---:|---:|---:|
| Disjoint, dense | 350=156M+194A | 490=203M+287A | 83 | 304 |
| Disjoint, general | 304=132M+172A | 444=179M+265A | 83 | 304 |
| Disjoint, guarded path | 301=130M+171A | 441=177M+264A | 83 | 304 |
| Shared, dense | 290=130M+160A | 430=177M+253A | 75 | 208 |
| Shared, general | 272=120M+152A | 412=167M+245A | 75 | 208 |

Each complete circuit saves exactly 2M and no additions against its own authenticated parent. Thus the fair path-versus-shared comparison becomes 441→412, still a 29-operation graph-sharing improvement, with the separate two-multiplication factoring improvement applied to both sides.

The reviewer independently checks source closure, liveness and all twenty old/new certificate/full-polynomial ledgers. Across the five children, 1,517 certificate gates and 2,217 complete polynomial gates are paid. The 304/208 degree statements are literal propagated **upper bounds**, retained with their proper scope. This packet does not require or assert exact-degree certification.

The parent 414/443 ledgers are retained as historical metadata; the active ledgers describe 412/441 and the other current sources. No old count is presented as the current emitted cost.

## 4. Evidence and limits

The independent receipt records ten exact local coefficient proofs, 2,197 common computed-register identities, 235 residual identities and five whole-polynomial identities. Twenty additional complete off-zero evaluations, including ten rational tuples, corroborate the structural proof. Ten supplied-k diagnostics explicitly violate k=eta+zeta. These evaluations are not the basis for the all-value identity.

The reviewer read the full author proof and the parent scope. The three-code fixture is not a universal subgroup alphabet, so 412 is not promoted as a universal arithmetic bound. No general compiler API, optimality result, arbitrary-controller census or transfer into a later projective kernel is claimed. The supported artifact is a bounded source-pinned CLI review.

Replay from any working directory with standard-library Python:

```
python3 review_group_macro_factored_coefficients.py \
  --root /path/to/native-stream-queue \
  --expect review_group_macro_factored_coefficients.json
```

If the frozen author trio is stored elsewhere, pass `--author-root /path/to/author-trio`. Authentication precedes all packet reads; `--expect` checks recursive exact JSON types and values. No repository files or frozen parent bytes were changed by this review.
