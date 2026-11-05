# Generic `IΣ₁`-model divisibility for the 72 carrier

The corrected [`FreeMainDivisibility.lean`](FreeMainDivisibility.lean) passed
[guarded Lean check attempt02](observations/attempt02/result.json). It proves,
in every model of `IΣ₁`, both:

- `dvd_of_cube_dvd_three`: if `q³ ∣ 3h`, then `q ∣ h`;
- `scale_dvd_carrier`: if `U>0` and `D²=U²N`, then `U ∣ D`.

The first proof splits `q mod 3`, uses literal cancellation in the divisible
case, and explicit Bézout unit certificates in the other two cases. It uses
no prime factorization or standardness assumption. The second invokes the
existing model square-divisibility theorem. Both reported axioms
`[propext, Classical.choice, Quot.sound]`; Lean exited 0 with no warnings or
`sorryAx`, stable direct-input guards, and no resource stop. Output object
SHA-256: `7bb7e9f6bee67dfe4d2a422bba3ca394b773d836484de8f21fb184dd78c6e342`.
The source comment saying “unchecked draft” predates the check; the file is
retained unchanged to match the receipt. The failed first attempt, source and
log are preserved separately.

This is **generic divisibility only**. It does not yet derive `q³ ∣ 3h` from
the actual 72 graph, prove its positive-zero `q | h` theorem, establish a
reverse witness map, or give an iPRA endpoint. The captured direct input
providers are pinned in the receipt; transitive, dynamic and between-sample
ancestry is inherited, not rebuilt from source.
