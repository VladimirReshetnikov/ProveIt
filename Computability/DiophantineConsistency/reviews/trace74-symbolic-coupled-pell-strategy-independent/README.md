# Independent mathematical review of the coupled-Pell construction

The reviewed [strategy note](../../research/trace74-symbolic-coupled-pell-strategy/README.md)
has SHA-256 `adc16c02c4a861819bb76ab00bf42b139aafcf5802d5b093b8fc243f86fdbdca`;
its [finite diagnostic](../../research/trace74-symbolic-coupled-pell-strategy/check.py)
has SHA-256 `e2768fb4109ad83700096b1b60130336c632cf48c2afe9bcd65f95df7bedc314`.
The mathematical construction checks out **conditional on** the sibling
scalar/Pell facts, finite external gcd computations and the stated port
and graph correspondence. Under those conditions its ordinary-integer
conclusion is that there exists a positive ten-coordinate valuation with
`Trace74Mask.value74=0` and `F+C≥q` at the specified symbolic beta and
external `K0`, for arbitrary natural `MC,MF`. It is not a Lean-kernel proof, an evaluation of the
huge symbolic tuple, or an independent authentication of every transitive
provider or external payload binding.

The needed numerical inputs include `gcd(c,q²−1)=1`, computed by two
independent algorithms using GMP on the same host, and the two finite
gcd checks for the hash-pinned external `K0` and `H`. Their executable
results are evidence conditional on their implementations and toolchain;
they are not internal Lean theorems. The conclusion concerns the stated
symbolic beta, external `K0` and 74 source, with their correspondence to
the external candidate remaining a separate evidence boundary.

The Pell step matrix `[[z,Delta],[1,z]]` has determinant one, so it
permutes the finite residue pairs modulo `m=c² tau`; the orbit of `(1,0)`
has period at most `m²`, dividing `(m²)!`. Thus the stated positive `t0`
exists explicitly. Addition gives `y_t0 | y_(c t0)`, which supplies the
integer `i`; the norm and doubling formulae give `F0=phi²`, `f=x_(2t)`,
and `Q=(Delta*y_(2t))²`. Since `c|y_t`, `f≡1 (mod c)`.

For odd `u=2j+1`, the quotient `T_u(S)/S` is an integer polynomial.
Its odd-index recurrence and the even-index recurrence for `U_(2j)(z)`
show the asserted polynomial congruence modulo `S²+z²−1`. For the
candidate, `r≡1 (mod 4)` and odd `s` give `j` even, while `x_(4t)≡−1`
and `y_(4t)≡0 (mod f)` give `y_u≡−c (mod f)`. Hence `V0≡−c (mod f)`.
Also `c|t` and the Pell addition formula give `c|y_(2t)` and `c|S`;
the linear term of `T_u(S)/S` is `u` for this parity, so `V0≡r (mod c)`.
Together with `R≡−r (mod c)` and `f≡1 (mod c)`, these congruences make
`T=(V0+c+fR)/(fc)` an integer. The stated sufficiently large odd `s`
makes both `T` and the constructed `v7` positive; all remaining input
coordinates are positive from the sibling construction.

From `H|Kreg`, `h|Breg`, and `D|e`, the constant `N0` is integral and
the proposed `v7` makes `Z=M tau phi yaux`. Direct inspection of the
`Trace74Mask.value74` rows in the captured source
`trace74-boundary-compatible-rebuild/observations/attempt03/stage-01.source.lean`
(SHA-256 `83ad7a62d50b10104099d8769c201c5514ed3afdabcf30ce1df8f4bb7774b7f0`)
shows their final arithmetic is

```text
Q*(Z²−M²*E*F0*V²)+(M²*E*F0−Z²)
  = (Q−1)Z²−M²(E F0)(QV²−1).
```

The auxiliary Pell identity makes this zero after the stated substitutions.
The old-chart substitution `alpha=q−F−C` is an all-ring identity; no
positivity of that synthetic coordinate is used. These checks support the
conditional ordinary-integer construction, but do not elevate its
external computations or historical 74 source to a current-source Lean
certificate or identify every retained external file with Lean ports.

The author's finite checker was rerun and exited zero. The separate
[`check.py`](check.py) was also run with `python3 -I -S -B`: its
`z=2,r=5,c=209,t=1045` example independently tests the actual
`r≡1 (mod 4)`, odd-shift signs and the two modular conditions, and its
sparse-polynomial calculation checks the abstract final-output identity.
Neither finite check materializes the symbolic witness or by itself
proves that the retained 74 graph has a zero. The review does not claim
positive-existence inequivalence of the 74 and 75 equations or resolve
ZFC consistency.
