# An 82-operation input-root chart with the refuted shared-projection language

Supplying the input Pell root directly gives a complete **82=45M+37A** circuit with eighteen positive witnesses. Its positive zero set is in an exact, same-input bijection with the already refuted shared-projection83 source. Consequently it has zeros at unbounded positive inputs on every original five-adic compiler slice, and infinitely many false positives on the authentic empty-language slice. This is a refuted shortcut, not an improvement to the sound universal84 construction.

The new quotient-gap ordering is also insensitive to the common exponent offset in shared83. Every positive zero of that source satisfies the strict Pell-scale gap bound, including its false zeros. Ordering the two roots more tightly therefore cannot replace the missing divisibility condition. No global arithmetic lower bound or claim about independent-gamma83 follows.

## 1. Literal source edit and complete paid count

Use the actual `complete83_shared_projection_scout.json` packet, whose source has83 rows and whose witness `shared_projection` is denoted U. Its root definitions are

```
X=wn2=w*q, Y=sn2=s*q^3, a=R12=Y*(X+1),
H=a4m5=4*a+3, Delta=A=a^2+H,
c=R10a, kappa=index_rhs=u+delta*Delta,
W=q-F-2*Z-alpha-twice_cell_bits*x,
D=R14=a*c+X+U+sigma*H,
mu=exponent_rhs=a*kappa+W+U.
```

The ordinary input is x. The six fixed numeral ports retain their full original meanings, including `MF=MF_native+B-1`; no numeral is specialized or added. Replace the positive witness U by a positive supplied witness `input_root=M`. Replace the main/input root block by

```
root_coefficient_gap = c-kappa,
root_scaled_gap = a*root_coefficient_gap,
root_projection_gap = X-W,
root_partial = root_scaled_gap+root_projection_gap,
root_with_input = root_partial+M,
gam = sigma*H,
R14 = root_with_input+gam,
mu2 = M*M.
```

The existing `gam` and `mu2` each still cost one multiplication. Delete the seven old definitions `cam2,D1,shared_main_partial,R14,difference_multiple,exponent_partial,exponent_rhs`; insert the six displayed gap/main-root definitions other than `gam` and `mu2`; change only the operands of `mu2`. Reorder the complete DAG topologically. The input norm is now `M*M-Delta*kappa*kappa`. Every other factor, loader, auxiliary producer and finalizer is retained.

The old joint-root block, counting gam but not the root squares, costs3M+5A. The new block costs2M+5A. Thus the full ledger is

| Scope | M | A | Total |
|---|---:|---:|---:|
| All seven-factor producers |39|36|75|
| Unchanged six product rows and final subtraction |6|1|7|
| Complete source |45|37|82|

The companion receipt emits the entire82-row array, eighteen witness names, ordinary input and six fixed ports. Seventy-five old row definitions are literal; `mu2` is the one additional retained identifier with changed operands, and six definitions are newly supplied. Every row and all25 ports are live. No exact degree claim is made for this new nonlinear coordinate chart.

This source is distinct from `complete82_auxiliary_square_product_chart`, which frees two auxiliary products and was separately proved to accept every input. It is also distinct from `complete80_main_root_gap_collapse`, which frees the main-root gap. Those older all-input conclusions are not asserted here.

## 2. The full all-ring identity

Let F83 denote the literal shared-projection polynomial and F82 the new polynomial. Over every commutative ring,

```
F82(M,other ports) = F83(U=M-a*kappa-W,other ports).    (1)
```

Indeed the restored input root equals M, and the old main root becomes

```
a*c+X+(M-a*kappa-W)+sigma*H
 = a*(c-kappa)+(X-W)+M+sigma*H.
```

The two root squares and every downstream factor therefore agree inductively. The retained exterior producers of a,kappa,W are independent of U and M, so this is a triangular polynomial substitution. It does not use a norm equation, division, positivity or a free computed input. The six finalizer multiplications and subtraction of Delta remain literal, so (1) is a whole-polynomial identity.

Conversely, substituting `M=a*kappa+W+U` into F82 gives F83 identically. These are inverse polynomial coordinate changes on unrestricted integer tuples. Their positive-domain restriction requires the following argument; an all-ring identity alone would not suffice.

## 3. Both positive directions, before any native decoding

For the F82-to-F83 direction, only positive integer fixed ports with Bm1>=1 and positive supplied coordinates are needed. Thus q>=2, X>=q, Y>=q^3, a>q and

```
Delta=(a+1)*(a+3)>q,
kappa=u+delta*Delta>Delta,
W<q.                                                (2)
```

The last inequality is literal and requires neither W>=0 nor an outer equation. The complete source has the exact factorization

```
F82=Delta*(Nfirst*Nmain*Ninput*Naux*Nindex*Ntransport
           *(f^2-Delta*i^2*c^4)-1).                 (3)
```

It follows directly from the retained scaled-strong block; changing the main/input roots does not alter it. Since Delta>0, a positive zero makes all seven normalized integer factors units. In particular Ninput is +1 or -1. The latter is impossible modulo4: Delta is0 when a is odd and3 when a is even; in neither case is `M^2-Delta*kappa^2=-1` possible. Consequently

```
M^2-Delta*kappa^2=1.
```

M and kappa are positive and `Delta>(a+1)^2`, so `M>(a+1)*kappa`. The unique inverse coordinate in (1) therefore obeys

```
U=M-a*kappa-W > kappa-W > Delta-q >0.                (4)
```

This proves the F82-to-F83 positive inverse without assuming a positive main root, canonical input index, dyadic q, or the conclusion of the shared83 theorem.

For the other direction, start at any positive F83 zero on a valid inherited compiler slice. The shared83 pretyping proof gives `|W|<q` before the Pell input argument or any dyadic typing. Then `mu=a*kappa+W+U>a-q>0`. This is the sole inherited pretyping fact needed in this direction. Set M=mu. Identity (1) gives a positive F82 zero and restores exactly the original U. We do not assume W itself is a supplied positive witness.

Thus the maps are mutually inverse on the full positive zero sets at every valid compiler slice. The stronger positive-numeral-domain assertion applies only to the inverse (4); no equivalence claim on arbitrary off-recipe numeral tuples is needed.

## 4. The quotient-gap bound also holds off the parent image

Now restrict to an authentic inherited compiler slice. The full shared83 offset theorem gives, on every positive zero,

```
A_Pell=a+2>2^R, R>=49, R and u odd, 3<=u<R,
c_j=psi_(A_Pell)(j), D_j=chi_(A_Pell)(j),
E_j=D_j-a*c_j=2*c_j-c_(j-1),
c=c_R, D=D_R, kappa=c_u, mu=D_u,
X-W=2^R-2^u,
sigma*H=E_R-E_u-2^R+2^u.
```

Here `H=4*A_Pell-5`, while the literal register `A` continues to mean Delta. Neither q being dyadic nor H dividing U is a premise. Put `b1=c_(R-1)` and `b2=c_(R-2)`. The recurrence gives

```
E_R-H*b1=4*b1-2*b2,
E_u<=E_(R-2)<2*b2,
H*(sigma-b1)>4*(b1-b2)-2^R+2^u>0.                  (5)
```

For the last strict sign, `b1>(2*A_Pell-1)*b2>2*b2`, `b1>=2*A_Pell`, and `A_Pell>2^R` give `4*(b1-b2)>2*b1>=4*A_Pell>2^R`.

Define the positive integral proof quotients

```
rho0=(E_u-2^u)/H, gamma0=(E_R-2^R)/H.
```

The offset theorem gives sigma=gamma0-rho0. Also

```
2*H*b1-(E_R-2^R)=(4*A_Pell-9)*b1+2*b2+2^R>0.
```

Therefore the complete strict interval is

```
psi_(A_Pell)(R-1) < sigma < gamma0
                  < 2*psi_(A_Pell)(R-1).            (6)
```

The addition law `c_(j+1)=A_Pell*c_j+D_j` implies `mu=D_u<c_(R-1)`. Hence

```
sigma>mu>kappa>delta>0.
```

These are the same useful root-gap comparisons previously proved for the canonical independent-gamma branch. Here they hold throughout the entire shared-projection zero set. The supplied U is not H*rho0 unless the offset vanishes: the exact relation remains `U=H*rho0-e`, where `e=X-2^R=W-2^u`.

## 5. Refutation and the next-action boundary

The independently reviewed `complete83_rejecting_compiler.md` proves that the literal shared83 source has positive zeros at unbounded x on every original powers-of-five modified75 compiler slice. Its construction uses the actual source export `MF=MF_native+B-1`, constructs all eighteen positive coordinates, and applies to an explicitly specified compiler for the empty language. By Section3, these zeros transfer bijectively to F82 at exactly the same x. Thus F82 has infinitely many false positives on that authentic empty-language slice. No enormous native tuple or historical compiler needs to be evaluated to draw this consequence.

The construction has W=0 and nonzero offset e=-2^u. Yet all inequalities in (6), including sigma>mu>kappa>delta, hold by Section4. Appending or using those inequalities alone cannot force H|U or repair the input marker. This is a precise limitation of the gap-ordering route; it does not rule out a different arithmetic relation that enforces the missing divisibility at a lower paid cost.

**Review remark 1 (retained unsuccessful saving).** The attempted shortcut was: “supply the input root instead of its common projection, use the positive main/input gap to share a multiplication, and recover the required projection by positivity.” The multiplication saving and positive recovery are valid, but the restored object is only U, not the parent integer rho=U/H. The authentic nonzero-offset family violates H|U while satisfying the full gap ordering. Therefore the shortcut preserves the refuted shared83 language. The frozen shared83 scout's earlier wording “unresolved relaxation” is a historical status superseded by the pinned rejecting-compiler theorem, not the present status.

## 6. Binding and evidence scope

The companion JSON binds the full current proof bytes, exact source/proof dependency hashes and stated read spans. It saves the entire newly emitted82-row array and records static topology, liveness, the75 literal rows, the seven removed definitions, the six inserted definitions, the sole retained-row edit and the complete45M37A count. Fresh coefficient arithmetic checks only the handwritten two-root polynomial identity at its eight mathematical arguments. No saved source array is evaluated, no scalar assignment to a complete circuit is tested, and no degree or native-fixture claim is inferred from finite evidence.

The fixed compiler semantics, normalized pretyping, Pell recovery, exact shared offset and actual-compiler false-positive family remain inherited at their stated scopes. This packet proves the new chart equivalence and the extension of the gap comparison; it does not repeat a full compiler or Pell-kernel audit. No supplied, archived, frozen or predecessor code is executed or imported. Only the new metadata/static checker may run before this packet freezes; it is not an authorized future replay suite. No repository or Git mutation is made.

The fresh writer and exact normal/optimized checks from `/` passed before freezing:82 live rows,25 live free ports,45M37A, eighteen witnesses,75 literal retained definitions and both formal root identities. The64 residue cases check only the handwritten mod4 norm-sign exclusion. Root independently read the full draft, shared offset proof, rejecting-compiler theorem and gap proof, and reported no mathematical finding before freeze.
