# Positive 87/36 ↔ 88/30: direct auxiliary coordinate audit

This bounded audit compares the exact positive-input graphs and identifies
reusable source-level model facts. It does not prove a Lean model map, an
endpoint or an iPRA statement. The graphs have the same 13-coordinate order
except position 11: the 88/30 parent has positive u and the 87/36 child has
positive y. The checker confirms the exact 88→87 row edits, verifies that
the 88 source literal's named rows and inputs match its pinned JSON, and
checks that both graphs' first, main, strong, V and Q fields ignore their
auxiliary coordinate. This source-byte check is not Lean elaboration.

In the difference ring put

```
V = f²*(T*c−R)−c,   Q = Delta*(f²−1),   y = V+u.
Fa88 = y²−Q*u*(y+V),
Fa87 = y²−Q*(y²−V²).
```

The receipt proves `Fa88=Fa87` after substitution as an exact polynomial
identity over the integers, hence in every commutative ring. All three
other residuals are unchanged; each output is the sum of squares of the first,
main, `Fa−1` and strong residuals. Consequently their outputs agree under
this *signed-ring* coordinate substitution. This does not by itself show
that either translated auxiliary coordinate is a positive model natural.

For example, the isolated scalars `V=-3,u=1` make the direct expression
`y=-2`, and `V=3,y=1` make `u=-2`. These are not graph zeros; they show why
separate positivity reasoning is necessary rather than refuting either map.

## Conditional witness interface

The independently source-reviewed but **unelaborated**
`AuxRootModelDraft.positive_aux_coordinate_iff` has the right fact-level
shape. It assumes `1<Q` and `1<V²` in the difference ring, and its old and
direct auxiliary residuals are exactly `Fa88−1` and `Fa87−1`. Its generic
five-square form can represent these four-square outputs by taking the fifth
residual to zero, after proving the actual graph field and output identities.

Under those two strict bounds and either auxiliary zero,

```
(Q-1)*(y²-V²)=V²-1>0,
```

so `y²>V²`. In the 88→87 direction, positive u gives `y=V+ιu>V`; the
square inequality then forces `y>0`. The difference-ring natural-cone
representation supplies a **model-natural positive y** with that cast. In
the 87→88 direction, positive direct y and `y²>V²` imply `y>V`; the positive
difference `ιy−V` has a **model-natural positive u** representation. The
other 12 coordinates stay fixed. No sign or natural representation of V is
assumed, and model-natural truncated subtraction must not be used as though
V were already a natural model element. These source-level witness proofs,
their `nonneg_iff`/order rewrites, and all graph clients remain unchecked.

## Deriving the strict bounds from either actual zero

The exact first, main and strong residuals are common to both literals. For
positive J and represented positive beta, `q=1+J*beta` and
`M=q³*(J*beta)` are positive model naturals. Also `U=Y*q²>0`. The first and
main zero residuals have the signed form

```
Zfirst² = M²*(1+m*(m+1)*k²),  m=X*Y², k=eta+zeta,
Zmain²  = U²*(1+Delta*c²),     c=eta+Y*k.
```

A client can use the source-only
`AuxRingNormExtractionDraft.root_of_scaled_ring_square` (or the underlying
`ArithmeticAdaptiveQuotients2011.scaled_quotient` with signed magnitude) to
obtain model-natural tau and d for the same two norms, regardless of root
sign. This extraction does **not** first require `q³∣Y`; the scale is the
actual positive M. Both exact literal bindings and represented port casts
remain to be shown.

The common strong residual gives, after adding Delta in the difference ring
and reflecting to the naturals,

```
(i*c*c)²+Delta=Delta*f²,    Q=(i*c*c)²,
V+c=f²*(T*c-R),             (X*Y+Y+2)²=Delta+1.
```

The signed rank expression `T*c-R` need not have a natural representation.
The source-only `AuxNormsToBoundsDraft.aux_bounds_of_natural_norms` has these
explicit natural norms, positive X/Y/eta/zeta/i, and signed Q/V bindings as
premises and proposes `1<Q ∧ 1<V²`. Its dependencies include exclusion of
k=2 from the main square, first-Pell descent giving `k≥8XY²+4`, and the
strong-norm/geometry estimates. Those steps do not assume either auxiliary
coordinate's desired positivity or any compact K0 sign. The source-only
ring-residual adapter handles the main and strong normalization, but its
`first_norm_of_ring_residual` expects an **already unscaled natural tau**:
the actual 87/88 scaled first root must first be processed as above. None of
these imported proof scripts or graph bindings has been Lean checked.

A complete model bridge must connect the exact 87/36 graph, the 88 source
graph, all positive Fin-13 coordinate updates, the signed auxiliary fields
and the generic witness theorem, in each direction. The 88/30 source model
and endpoint drafts themselves remain uncompiled and rely on the 88/46 and
retained free-J endpoint ancestry. Coherent model providers, axiom reports,
fixed compact port equality and physical file/PDF semantics are separate
obligations. This audit supplies no end-to-end iPRA/ZFC equivalence.

From `Computability/DiophantineConsistency` reproduce the receipt:

```
python3 -I -S -B research/ordinary13-positive87-to88-aux-model-audit/check.py
```
