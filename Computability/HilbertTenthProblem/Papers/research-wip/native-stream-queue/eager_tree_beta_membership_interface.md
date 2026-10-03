# A paid sequence-membership atom and the remaining Tree compression interface

The first useful fixed-arity component is small: membership in a **supplied, CRT-coded natural sequence suffix** has a complete 16-gate natural certificate, or 17 gates when guarded by an already computed active port. This replaces a variable-length product only after its row codes have been encoded consistently. It does **not** yet compress the complete Tree family into a counted fixed-arity polynomial.

The source-specific next obligation is to compile **every decoded row's validity and code coherence at once**, for an existential unbounded length. Omitting coherence admits the explicit false Tree result `(program,argument,output)=(4,0,0)`, although the genuine result is 6. The [helper](eager_tree_beta_membership_interface.py) and [receipt](eager_tree_beta_membership_interface.json) emit the complete local circuits and reproduce this obstruction against the actual frozen pointer-product source. No historical compiler is executed, and no repository file is changed.

## Existing coverage checked first

The imported Tree article already states this boundary explicitly: its loader/quantifier discussion at lines 31115–31128 distinguishes a computable input translation and the union of variable-arity formulas from a fixed-arity polynomial. Its lookup/arity questions at lines 31445–31455 request charged bounds, extraction, consistency and unbounded sequence compilation. The independent [original Tree review](review_eager_tree_aebfa.md) makes the same distinction. The latest [pointer-product packet](eager_tree_pointer_product_scout.md) reduces the finite arity but still supplies all row fields independently at external `N`.

The report's memory-log theorems at lines 6927–6946 and 7191–7206 remain external-length families: respectively `10C+2L+3(N−1)` and `24L` auxiliary variables. They are not a fixed-variable lookup primitive. The reviewed [one-coordinate construction](review_one_coordinate_aebfa.md) uses unknowns in `N[X]` of unbounded degree; its bounded scalar export still grows with the degree cutoff. None of these results supplies the missing scalar bridge automatically.

There is already a genuine arithmetic bounded-universal theorem in the repository, beyond a bare appeal to DPRM. [MRDPCore.lean](../../../Lean/Diophantine/Common/MRDPCore.lean) has `boundedForall_dioph` at line 215, using a factorial/CRT certificate, and `recursionTrace_iff` at line 310. [DiophantineTrace.lean](../../../Lean/Diophantine/Common/DiophantineTrace.lean) provides `boundedForall_dioph` at line 52 through the separate `PAListCoding` cipher construction. These are existence/closure proofs, not a saved Tree straight-line source with a full ordinary-input ledger. No Lean build was run for this scout, and no completeness claim about every repository experiment is made.

## Exact fixed-arity suffix membership

For natural `A,b,j`, put

`beta(A,b,j) = A mod (1+(j+1)b)`.

For supplied natural `A,b,i,N,D`, introduce four natural witnesses `h,k,q,s`. Compute `j+1=i+h+2`, and use the three residuals

```
r0 = A - D - q*(1+b*(i+h+2))
r1 = b*(i+h+2) - D - s
r2 = N - (i+h+2) - k.
```

Let `S=r0²+r1²+r2²`. Then

`exists h,k,q,s in N: S=0  iff  exists j with i<j<N and beta(A,b,j)=D`.

Indeed `j=i+h+1` gives the strict lower bound and `r2=0` gives `j<N`. The second row gives `D<=b(j+1)`, exactly `D<1+b(j+1)`. The first row is therefore the canonical Euclidean remainder equation, with a positive modulus even when `b=0`. Conversely a valid index has the natural witnesses

```
h=j-i-1, k=N-j-1,
q=floor(A/(1+(j+1)b)), s=b(j+1)-D.
```

This proof includes empty suffixes. For `i=N−1`, the third row cannot vanish naturally. If an already computed natural active value `a` is supplied, use `a*S`: it has a natural extension exactly when `a=0` or the suffix membership holds. For Tree tags, `a` is already zero or one. Natural nonnegativity permits this guarded nonnegative term to join a sum of other nonnegative terms directly; the construction does not square the entire `a*S` again.

The literal shared schedule is:

```
i+h; +2; b*(i+h+2); +1; q*modulus;
A-D; -q*modulus; b*(i+h+2)-D; -s;
N-(i+h+2); -k;
r0*r0; r1*r1; r2*r2; square0+square1; +square2.
```

The first eleven gates cost `2M+9A`; the finalizer costs `3M+2A`. Thus `S` costs **16=5M+11A**, with four natural witnesses and exact degree **6**. The gated polynomial costs **17=6M+11A**, exact degree **7** when its inputs are independent scalar ports. In particular the quotient term contains the product of `q,b,i+h+2`; claiming this is merely quadratic would be wrong. The helper expands the entire two polynomials and counts every binary gate, including constant additions and the full finalizer. No optimality is asserted.

The targets and active ports are **inputs** to this local ledger, not free computed Tree expressions. Attaching the atom to Tree must still pay their actual circuits and all table constraints. A degree-five Tree target would make the guarded local polynomial have degree at most eleven in those original row fields, independent of `N`; this is only a substituted local upper bound, not a degree claim for the unfinished globally compressed certificate.

The domain matters. At `A=0,b=1,i=0,N=2,D=3`, signed witnesses `h=k=0,q=s=−1` make all three rows zero, but the only suffix entry is `0 mod 3=0`. At `A=1,b=1,i=0,N=2,D=0`, the nonnegative rational assignment `h=k=0,q=1/3,s=2` also zeros the rows without integer remainder membership. These examples are checked. The theorem is natural-integer arithmetic.

## Coding any finite sequence is not yet table verification

Every finite natural sequence `v0,...,v(N−1)` has such a code. For example choose

`b=N!*(1+max(vj))`.

The moduli `mj=1+(j+1)b` exceed their intended digits and are pairwise coprime. A common divisor of `mi,mj` divides `(j−i)b`, is coprime to `b`, and hence divides `j−i`; since every positive difference below `N` divides `N!` and therefore `b`, the divisor is one. The Chinese remainder construction supplies `A` with exactly the desired remainders. The helper constructs these numbers for finite examples. Factorial and CRT computation in this witness generator are **not** paid gates in the 16-gate certificate; the certificate treats `A,b` as supplied code parameters.

A precise uniform intermediate formula is available without growing tuples of outer variables. Use one common `b`, fourteen code integers `A_f`, and `N>=1`: thirteen columns encode the row fields `x,y,z,a,b_local,c,u,v,t0,...,t4`, and the fourteenth encodes `C(x,y,z)`. For every `i<N`, decode the thirteen row fields by the elementary remainder relation, impose the five retained local Tree residuals, and require

`beta(A_C,b,i)=C(x_i,y_i,z_i)`.

Use three guarded suffix-membership atoms on `A_C` for the actual branch targets. Three additional root accesses identify the decoded row-zero triple with the supplied `(program,argument,output)`. The code-column and row-field names here are schematic distinct ports. Last unused `u,v` can be restored to zero before encoding; keeping their sequence entries does not change the represented triples.

This gives an explicit fixed-size formula of the shape

`exists N,b,A_0,...,A_13: RootBindings and forall i<N exists local natural witnesses: LocalRowsAndQueries`.

Both directions follow from CRT encoding of a genuine finite certificate and from decoding all consistent rows plus the strictly forward pointer-restoration theorem. It is not yet one existential polynomial. The first missing **paid compilation** is elimination of that one bounded universal row condition, including all of its local remainder quotients, bounds and branch queries. Sequence existence alone is not the missing theorem.

The repository has a concrete possible route. `MRDPCore.boundedForall_dioph` chooses a factorial scale `T` larger than the polynomial-value/witness bounds, encodes row witnesses and indices by CRT, and checks polynomial congruences modulo a product of CRT moduli. Its source spells out

```
q = (1+(N+1)T)^N + 2,
encodedModuliProduct(N,T)
  = T^N * (N! * choose(q+N,N)) mod (T*q-1).
```

The certificate also includes falling-factorial divisibility to bound decoded row witnesses. Soundness decodes modulo a prime divisor of each CRT modulus and uses the factorial scale to turn congruences into genuine equalities. These safeguards are material, not bookkeeping. Expanding this route into an ordinary polynomial requires actual variable-power, factorial/binomial, divisibility, bound and finalizer subcircuits, with every witness and reuse counted. This scout neither exports that compiler from Lean nor produces the full resulting Tree source. The alternative cipher interface similarly proves closure of code/constant/index/multiplication relations but has not been instantiated here into a paid Tree DAG.

The existing [52-operation exponent component](pell_fixed_affine_exponent52.md) has the specific positive-input contract `Q=8^(32x)`. It is not by itself the variable-base/index power required in the displayed expression; treating it as a generic `Pow(base,index)` would be an interface error. A different existing Pell component might be usable after its full contract, domain shifts and shared gates are compiled, but no such count is inferred here. The separate ordinary-integer-to-universal-Tree loader also remains unpaid.

## Concrete obstruction to dropping code coherence

Take the complete frozen `N=3`, cleanup-enabled Tree packet. Its row fields are:

- root: `x=4,y=0,z=0,a=b=c=0,u=v=1,t3=1`;
- both later rows: `x=y=0,z=1,a=b=c=u=v=0,t0=1`.

All other tags are zero; last `u,v` are absent in the actual child interface. The external triple is `(4,0,0)`. Every one of the actual eighteen retained local/root residuals vanishes. The true row codes are `[400,2,2]`. The root's three target codes are `[2,2,25]`, so its third membership fails and the actual complete pointer-product polynomial is **279841**, not zero.

Encode the unrelated code column `[400,2,25]` instead. All nine guarded beta-membership atoms now have natural zeros: the first two root slots select index one, the third selects index two, and inactive slots are killed by their active coefficient. The remaining actual local/root rows still vanish. Nevertheless the third encoded entry is not the code of its actual row. Directly from the five Tree rules,

`app(4,0)=app(app(0,0),app(0,0))=app(1,1)=6`.

Thus unlinked code integers give an actual false acceptance, not merely a missing proof. The missing equation is the row-by-row code coherence above, along with retaining every decoded row's validity when the row fields themselves are packed.

A separate shortcut also fails: divisibility by `B−D` of `H=product_j(B−Cj)` does not imply some `Cj=D`. With `B=6,D=0,C=[2,3]`, `H=12` is divisible by six although no target is zero. A no-wrap bound such as `B−D>|product_j(D−Cj)|` could rule out nonzero multiples, but enforcing that bound and connecting `H` to the unbounded row table are extra arithmetic work. The source's existing literal zero product has no such composite-divisibility ambiguity.

## Reproducible finite evidence and result

The deterministic standard-library checker authenticates the exact files listed in its `pins` receipt, imports no repository Python module, and emits both complete local polynomials. It checks 81,648 unfiltered natural assignments, 76 explicit lifts, 36 CRT-coded sequences through length eight, 3,240 suffix queries and 336 CRT member lifts; it also verifies both domain counterexamples and the two distinct compression counterexamples above. These checks support the supplied general proofs, not an exhaustive certification of an unbounded Tree compiler.

```sh
python eager_tree_beta_membership_interface.py \
  --repo /path/to/Proofs \
  --expect eager_tree_beta_membership_interface.json
```

`--output FILE` writes the deterministic receipt. Comparison is recursively type-exact, and optimized Python is rejected. The helper records its own source hash and pins the actual parent, imported report, prior reviews and arithmetic interfaces; no external theorem or novelty claim was needed.

The bounded outcome is a **fully counted 16/17-gate sequence-membership interface**, an explicit bounded-universal target formula, and a source-specific obstruction to omitting its consistency condition. There is no new fixed-arity Tree polynomial, numerical universal machine/loader, or competitive universal operation count in this packet.
