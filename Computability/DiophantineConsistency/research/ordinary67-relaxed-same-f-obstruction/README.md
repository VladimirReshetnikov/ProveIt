# Relaxed Pell data can fail the same-f reverse map

A zero of the 67/94 candidate would require the relaxed strong equation

```
(i*c²)² = Delta*(f²−1),     Delta = A²−1.
```

The existing `ArithmeticPellIndexDivisibility.relaxed_auxiliary` model theorem, under its main-Pell and large-ordinate hypotheses, supplies an index `m` with `f=χ_m(A)`, `i*c²=Delta*ψ_m(A)` and both `p|m` and `c|m`. These conclusions alone do **not** imply `Delta|i` or `c²|ψ_m(A)`. Consequently they do not by themselves construct an old normalized strong multiplier while keeping the same `f` and `c`.

For a fully expanded standard-integer control, choose `A=3`, `Delta=8`, `p=4`, `c=ψ_4(3)=204`, and `m=204`. Let `f=χ_m(3)` and `y=ψ_m(3)`. Exact integer arithmetic verifies

```
A*Delta² = 192 < c,    p|m,    c|m,
y mod c² = 10404,      i = Delta*y/c² is an integer,
i mod Delta = 2,       (i*c²)² = Delta*(f²−1).
```

Since `y>0` and `f²−1=Delta*y²`, any old positive strong multiplier at the **same** `f,c` would require `y=i_old*c²`, impossible because `y mod c² ≠ 0`.

A second symbolic example also has the original q-cube *scale shape*: `q=3`, `w=2`, `s=1` give `X=6`, `Y=27`, `a=(X+1)Y=189`, `A=191`, and `Delta=36480`. Set `p=6`, so `c=ψ_6(A)=8,134,013,891,706`, and `m=c`. The positive decomposition `c=(eta+zeta)*Y+eta` is given by `eta=24`, `zeta=301,259,773,742`. The large-c bound and the two index divisibilities hold. Modular powering verifies `Delta*ψ_m(A)` is divisible by `c²`, while `ψ_m(A)` is not; the resulting relaxed `i` is `6080 mod Delta`. The enormous values `χ_m(A)` and `ψ_m(A)` are defined by the exact Pell recurrence and are **not** expanded.

The Pell recurrence `(χ_{n+1},ψ_{n+1})=(Aχ_n+Delta ψ_n, χ_n+Aψ_n)` preserves `χ_n²−Delta ψ_n²=1`. Divisibility of `Delta*ψ_m` by `c²` makes the displayed positive `i` an integer, and the relaxed equation follows by squaring. The modular computation uses binary powering modulo `c²`; because `ψ_m = r+c²t`, the residue of `i` modulo `Delta` is exactly `Delta*r/c²` when that quotient is integral.

These are partial standard-integer Pell assignments. They do not satisfy or purport to satisfy all 67/94 graph equations, do not use the actual fixed current-port tuple (the second example has `q=3`), and do not prove a statement in IΣ₁ or refute existence equivalence. In particular, a reverse construction changing `f` or other witnesses is not ruled out.

Reproduce with `python3 -I -S -B Computability/DiophantineConsistency/research/ordinary67-relaxed-same-f-obstruction/check.py` from the repository root.

| Artifact | SHA-256 |
| --- | --- |
| `check.py` | `d115178263bb7dcdd458b2d48f083ab67c39029bbf77eb6d4427d52134489657` |
| `result.json` | `1eddfbdc50e47fe9c23e427a18a5445a66c5012824e5cf72750033e3212a8c1c` |
