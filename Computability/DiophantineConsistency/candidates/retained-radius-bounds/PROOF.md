# Two guard signs follow from exact original-row bounds

This is a new sibling of the accepted `retained-radius-integers`
construction. That entire 161-guard packet is unchanged. The present
packet deletes exactly the guards on `shared.A` and
`index_addition.D`; it replaces their sign assumptions by explicit
polynomial consequences of the same original rows. All final variables
range over the unrestricted integers. The inherited natural source and
ordinary refutation calibration are unchanged. Lean remains paused.

Let P be the accepted raw natural system: 1,259 coordinates and 1,177
quadratic rows. Its complete raw-to-667 affine/square equivalence and
ordinary source proof are already established in the pinned parent.
Write r_j for its j-th residual, with zero-based row indices. The new
certificate retains 159 of the parent's 161 seed signs and every
original polynomial row.

## 1. The lower endpoint is n>=2, not merely n>=1

In the actual raw coordinate order,

```
t0 = x_0,  t = x_4,  n = x_5,
A = x_644, T = x_694, D = x_917.
```

The retained guards prove t0>=0 and T>=0. Literal original rows r_0
and r_1 are

```
t-t0-1=0,                 n-t-1=0.
```

Consequently t>=1 and n>=2 at every zero. These statements do not use
a power, factorial or source interpretation. The strict lower endpoint
matters: allowing n=1,T=0 would permit A=1 in the next identity.

## 2. Exact ideal certificates recover A and D

The raw system retains intermediate wires, so its displayed
`base0.T_definition` row alone is not the expanded equation in A,n,T.
The following full integer-polynomial identity is checked from the
literal original residuals:

```
r_644+r_643+r_642-r_640-n*r_639+r_641
                       = 2*A*n-T-n^2-1.                    (1)
```

The coefficient -n is part of the certificate; it is not a constant
row combination or an unproved algebraic simplification. Thus every
zero of P satisfies 2An=T+n^2+1. Since n>=2 and T>=0,

```
T+n^2+1-2n = T+(n-1)^2 > 0.
```

The factor 2n is positive. If the integer A were at most1, equation
(1) would imply 2An<=2n<T+n^2+1, a contradiction. Hence A>=2.

The second exact original-row identity is

```
-r_853-r_852+r_598 = D-A^2+1.                              (2)
```

It proves D=A^2-1>=3, in particular D>=2. The actual bound certificate
stores the conservative lower bound2 for D. Both A and D signs have
therefore been recovered without guards or intended arithmetic meanings.

## 3. What the independent shifted-bound checker proves

A bound step supplies a target x, an integer L>=1, polynomials F,G
independent of x, and a finite original-row combination equal to
`x*F-G`. The checker expands the entire combination, including its
polynomial multipliers, and requires exact equality. It then proves
F>0 and G-(L-1)F>0 from previously established bounds. These imply
x>=L at an integer zero: if x<=L-1, then xF< G, contradicting xF=G.

To check each inequality, substitute X_i=Z_i+l_i for previously
established lower bounds l_i>=0 and expand exactly. Every nonzero
coefficient must be positive, and every variable of odd exponent must
already have a known nonnegative sign. Even powers of arbitrary integer
coordinates need no sign. Strict positivity additionally requires a
positive constant term. These are sufficient unbounded polynomial
inequality proofs, not finite numerical tests.

The four steps are t>=1, n>=2, A>=2 and D>=2. In the A step, shifting
n=z+2 gives

```
F=2z+4,            G-F=T+z^2+2z+1.
```

In the D step, shifting A=a+2 gives

```
F=1,               G-F=a^2+4a+2.
```

Every strict constant and every odd-coordinate premise is visible.
In particular the checker rejects weakening the available n bound to1,
claiming A>=3, using D before A, or replacing the multiplier -n in
(1) by -1.

After these four bounds, replay the parent's full actual-row sign
schedule except its now-redundant t and n sign steps. The remaining
1,096 steps consist of 1,079 positive-monomial implications and17
exact affine-square identities. They are each checked anew against
the original row and earlier known signs. Together the159 guarded
seeds and1,100 derived coordinates cover all1,259 original variables.
No claim of a minimum guard set is made.

## 4. Exact integer conversion and complete signed restoration

For each of the159 seeds append a private quadratic guard

```
x=a^2+b^2+c(c+1).
```

For integer c the right side is nonnegative. Every natural x has such
witnesses by Legendre's three-square theorem applied to4x+1: modulo4
exactly one of its three square summands is odd, giving the displayed
representation after subtracting1 and dividing by4. The witnesses
for different seeds are private. Thus a natural P-zero extends to the
new guarded system, and an integer zero of that system recovers a
natural P-zero by Sections1--3. Both implications are unbounded.

This augmented parent has1,736 integer coordinates and1,336 quadratic
rows. Subsequent projections use the same checked integer rule as the
accepted sibling: a row exactly v-f or its negative uniquely defines
an integer v. Substitute f into every row, including every guard,
and accept only quadratic resulting rows. An identically zero row
can be dropped only after its entire polynomial vanishes. Every
restoring polynomial and the reverse order are retained.

All five certificates have `unconstrained_removed=[]`. Restore the
entire unrestricted-integer parent first, then its159 guards, the
four bounds, and all original sign implications. Negative restoring
coefficients or values are harmless because restoration precedes
natural extraction. No signed restoring polynomial is assumed to
preserve nonnegative values. The inherited raw-to-667 and source
equivalences can then be applied to the resulting natural assignment.

## 5. Complete literal quartics

Each equation is the sum of the squares of all its listed quadratic
rows. Integer zero existence is therefore the simultaneous row-zero
condition. Every collected integer coefficient is independently
recomputed, every declared coordinate occurs, and the exact degree
is four at all five points.

| Integer variables | Quadratic rows | Collected terms | Actual height |
|---:|---:|---:|---:|
| 1,736 | 1,336 | 6,172 | 427 |
| 1,089 | 689 | 5,016 | 4,750 |
| 944 | 544 | 6,780 | 737,653 |
| 880 | 480 | 10,130 | 737,653 |
| 866 | 466 | 10,094 | 938,261 |

Each improves its immediate161-guard sibling by six coordinates, two
rows and28 collected terms, with the same actual coefficient height.
No global simplicity optimum is asserted. Support parameters choose
which exact definitions to project; they never truncate a polynomial.

The independent checker imports no producer, sign selector or optimizer.
It checks the original-row ideal and shifted-bound identities, all
guard/sign steps, all complete signed projections and every final SOS
coefficient. Three arbitrary signed restorations per child compare all
surviving and deleted rows. Ten mutation controls test both the new
bound boundary and the old sign/guard/inverse boundary. Normal and
optimized Python reproduce all literal bytes. These finite controls
supplement the unbounded proofs, not a search for refutations or zeros.

The complete parent bytes, independent inverse control source and
reviewed arithmetic engine are pinned by `PARENT_PINS.json`. The engine
is the immutable407 ZIP with SHA256
`59f847872298260ee35e9d8e4cd0b52d2d78658ac523981fe060e81f40ca4a59`.
The frozen161 sibling, raw natural source and incoming archive remain
unchanged. No Lean, historical H10 emitter or native coefficient
generator is run; this packet supplies no new internal object-ZFC
derivation and does not prove consistency.
