# The two independent-k norms force k positive under the compact port bounds

For the pinned 84-operation candidate, suppose all witness inputs and all four ports are **ordinary nonnegative integers**, with

```text
beta > 0,  K0 > 0,  MC < beta,  MF < 2*beta.
```

If the graph's first and main norm residuals `A0` and `A1` both vanish, then `n_k > 0`. This is a source-only mathematical argument. It does not assume or establish that zero of the whole product equation forces these two residuals to vanish, and it does not provide a Lean theorem or an iPRA endpoint.

The retained compact source `Lean/DiophantineConsistency/Compact44/C44Short15Facts.lean` states the beta and mask bounds in `port_bounds` and positive K0 in `K_pos`, for its exact compact tuple. These source declarations and their provider ancestry have not been checked by Lean in this audit. The conclusion below is conditional on the displayed port inequalities; no expansion of the compact constants is needed.

## Exact graph expressions

The relevant rows, checked against the candidate, give

```text
b=J*beta, q=1+b, F=n_F+1, alpha=n_alpha+1,
X=q*n_w, s=n_s+1, Y=q^3*s, U=Y*q^2,
C=q-F-alpha, d=X+K0, B=C*d-F,
ell=X*Y^2*k,
Z=b*(ell+k+r-k*B)-B,
A0=Z^2-b^2*(1+ell*(ell+k)),
G=alpha+(q-F)*b,
R=G*(q^2-1)+J*(MC+q*MF),
a=Y*(X+1), H=3+4*a,
Dstar=U*b0+H*(U*gamma-k+R+1),
A1=Dstar^2-U^2*(1+Delta*c^2).
```

Here `k=n_k`, `r=n_r`, `gamma=n_gamma`, and all subtractions are integer subtractions. First, `A0=0` forces `J>0`: if `J=0`, then `q=1`, `C=1-F-alpha<0`, `d≥0`, and `B=C*d-F<0`; the first residual becomes `B²>0`. Thus `b>0` and `q≥2`.

Assume for contradiction that `k=0`. The first residual is `(b*r-B)^2=b^2`, so `B=b*(r-1)` or `B=b*(r+1)`. If `C≤0`, then `B<0`, and the only possibility is `r=0, B=-b`.

## Both first-norm branches bound the actual rank

If `C>0`, then `q=F+alpha+C` with the three terms positive. Hence `q-F≥2`, `alpha≤q-F-1`, and

```text
G = alpha+(q-F)*(q-1) ≤ q*(q-F)-1 ≤ q²-q-1 ≤ q²-2.
```

Also `G>0`.

For the exceptional branch `C≤0`, put `t=-C≥0`. The equation `C*d-F=-b` gives `F=b-t*d`, and the definition of C gives `alpha=1+t*(d+1)`. As `d=X+K0≥1` and `F≥1`, we have `t*d≤q-2`. Therefore the actual graph expression is

```text
G = q+t*(1+q*d)
  ≤ q+(q-2)+q*(q-2) = q²-2,
```

and again `G>0`. This includes the `C=0` case.

Since `J>0` and the mask bounds are strict,

```text
J*(MC+q*MF) < (q-1)*(1+2*q).
```

In either branch it follows that

```text
0 < R+1
    < (q²-2)*(q²-1)+(q-1)*(1+2*q)+1
    = q⁴-q²-q+2
    < q⁴.
```

The second strict inequality holds for `q≥2`. This rank is the candidate's actual computed rank, not an independently chosen scalar.

## Main-norm divisibility contradiction

`A1=0` makes `U²` divide `Dstar²`. Since `U=q⁵*s`, ordinary integer square divisibility yields `q⁵ | Dstar`. At `k=0` the `U`-terms in the displayed `Dstar` expression are multiples of `q⁵`, so

```text
q⁵ | H*(R+1).
```

Moreover `q³ | a`, so `H=3+4*a` satisfies `gcd(H,q⁵) | 3` and that gcd also divides `q`: primes other than 3 dividing q do not divide H, and if 3 divides q then `H` is divisible by 3 exactly once. Cancelling the gcd gives `q⁵/gcd(H,q⁵) | R+1`, hence **`q⁴ | R+1`**. This contradicts `0<R+1<q⁴`.

This proof uses ordinary integer divisibility, prime valuations/cancellation, and signed graph expressions. An arbitrary arithmetic-model formalization needs corresponding signed-to-natural divisibility, square-divisibility, and gcd/cancellation lemmas, together with model representations of the compact port bounds. None is silently assumed here.

## Reproduction and scope

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B research/ordinary13-independent-k-two-norm-kpositive-audit/check.py | cmp - research/ordinary13-independent-k-two-norm-kpositive-audit/receipt.json
```

The checker pins the inputs, verifies the relevant exact graph rows, independently checks nonnegative-coefficient certificates for both bounds on `G` and the strict rank cap, and runs bounded branch and gcd controls. These finite controls do not prove the quantified divisibility argument; that argument is given above. In particular this is not a full graph zero exclusion, a zero-map to the parent graph, a checked source proof in Lean, or a consistency equivalence.
