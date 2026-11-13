# Positive-zero characterization for the free-Pell-gap candidate

For the 64-gate free-Pell-gap candidate, ordinary positive-zero existence is
**equivalent** to the existence of positive coordinates

```
J,F,alpha,z,s,w,n,eta,zeta,gamma
```

making the original literal first, main and transport factors all 1:
`N0=N1=Nt=1`. The fixed ports must satisfy the maintained bounds
`beta>=31`, `K>0`, `0<MC<beta<MF<2*beta`; no full maintained zero is
assumed. This is an ordinary mathematical characterization, not a Lean/iPRA
proof, actual-port seed, full zero, PDF binding, or proof of existential
nonequivalence with the original equation.

## Every candidate zero supplies such a seed

The candidate replaces y by positive t and uses

```
Na' = V² − (S²−1)*t.
```

On a positive candidate zero, Delta>0 and the scaled strong factor is
`Delta*B` with `B=f²−Delta*(i*c²)²`. Cancel Delta: the integers
`N0,N1,Na',Nt,B` have product 1, hence each is ±1.

The previously reviewed consecutive-product Pell obstruction excludes
`N0=−1`; the usual discriminant mod-4 arguments exclude `N1=−1` and
`B=−1`. The relaxed auxiliary factor also cannot be −1, although its old
mod-4 proof no longer suffices. Indeed `S>=3`. If S is odd, `S²−1` is
divisible by 8, and a square cannot be −1 modulo 8. If S is even,
`S²−1=3 mod 4`; at least one of its prime divisors is 3 modulo 4, and −1 is
not a quadratic residue modulo that prime. Thus `Na'=−1` would make
`V²=−1 mod (S²−1)`, a contradiction. All four nontransport units are 1,
so Nt=1 as well. Retain the ten coordinates named above.

## Every such seed has a candidate completion

From `Nt=1` and positive inputs, the usual scalar argument gives `C>0`
and positive R. The seed's main factor supplies
`D²−Delta*c²=1` with `A=a+2>=3`, `Delta=A²−1`, positive D and c>=2.
The independently reviewed generic CRT/Pell completion in
`../free-pell-gap-generic-completion/` then constructs positive f,i,T,t
with the strong and relaxed-auxiliary factors both 1. It can additionally
choose `V²+t` nonsquare. The resulting candidate polynomial vanishes.

The optional nonsquare proves that this completion has no original y with
the **same other coordinates**. It does not say that the original equation
has no zero elsewhere. The scalar e=0 fixed point in
`../current14-free-gap-scalar-e0/` supplies positive scalar/transport data
at the actual ports, but it has not been extended to the first and main
factors; its canonical binomial Y fails q³ divisibility. Thus the actual-port
seed and full candidate zero remain open.

The checker pins the literal source and checks finite nonresidue controls;
it does not replace the unbounded prime-divisor, Pell-unit or CRT arguments.

```
python3 -I -S -B research/free-pell-gap-seed-characterization/check.py > /tmp/free-pell-gap-seed.json
cmp /tmp/free-pell-gap-seed.json research/free-pell-gap-seed-characterization/result.json
```

Independent external review is recorded in
`../../reviews/free-pell-gap-seed-characterization-independent/`. It
normalizes the review-link-only edit in the generic completion README when
checking that packet's earlier pin.
