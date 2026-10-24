# Independent mathematical review: the consecutive modulus

Reviewed on 24 October 2026 against the derived-label factorial-carrier
source at commit `45b399ec51dfbecb891dd51d8a9e4b6b7c361ac6` and the
signed squared-radius source assembled during this research session.

## Selected source

```
t=16+h^2,
rho=F^2*t^2,
R=2+t+x+y+F^2,
y=V(V-1).
```

The corresponding full proof is
`CONSECUTIVE_MODULUS_PROOF.md`. The `V` power request and all other
source modules retain the same meaning and inherited interfaces.
No proof or check in this directory depends on the earlier modulus
`V^2+3F^2-1` or on the later rejected need to impose an even horizon.

## Conclusions

1. The product `V(V-1)` is nonnegative for every integer `V`; hence
   the seed `y+1` is positive before any indexed-Pell interpretation.
   Proposed values `V=0,1` do not cause a seed failure. A parity or
   zero-output obstruction is unnecessary.
2. The retained `q>=2` anchor orients the `t` pair. Then the ceiling
   rows force `F>=1`, and `V>=F+2` restores `y>=F+1` and the old
   endpoint slack before decoding.
3. The reciprocal-index row, signed-output orientation, exact digit
   bounds, and squared-radius factorial lemma retain their established
   noncircular order.
4. For `a=Ft>=3`, `t>=2`, the inequalities
   `a^2+1>(a-1)(a+1)` and `(a-1)^t>=a+1` give
   `S<=(1+Ft)^(t+1)<V`. These hypotheses hold at every actual horizon
   `t>=16`.
5. Canonical witnesses satisfy `F|(V-1)`, so `F|y`, and `y>=V>S`.
   The first CRT requires only `S,Sp<=y`, `y>=F+1`, and `F|y`.
   It never required `y>V^2` independently.
6. All later majorants remain valid because `F^2>=F` after sign
   recovery. Their growth floor is used only after `F=t!` is proved.
7. A square horizon is cofinal in the parent's eventually unrestricted
   completeness parameter. Other witnesses must be reconstructed
   after choosing it; no pointwise old-to-new witness claim is made.

## Literal source interfaces examined

The first-CRT requirements are explicit in inherited
`FACTORIAL_CARRIER_PROOF.md`, Sections 1, 3, and 4. The actual endpoint
slack coordinate occurs only in its defining row. All other appearances
of `y` serve the beta moduli, natural local ranges, the exponent `y+1`,
or the majorant. The source retains the guards on `x`, the shared frame
base and bootstrap witness, the independent encoded representatives,
and all original natural digit/ceiling slacks.

The strict accumulator estimate and new unconditional sign argument
replace the relevant old sufficient bounds; they do not remove any
inherited CRT or Pell hypothesis.

## Finite regression scope

`check_cofinal_semantics.py` checks selected exact arithmetic cases,
including negative and zero proposed outputs, the stronger pending
bound, canonical moduli and beta coprimality, the factorial fixed-point
lemma, the older 512-variable modulus, and negative controls. It binds
the old checkpoint proof and the new principal proof by SHA-256.
Its checks use explicit exceptions and remain active under `python -O`.

These are finite regressions and transcription controls. The all-integer
sign statement, unrestricted factorial equivalence, and unbounded
consistency equivalence are justified by the ordinary proofs, not by
the finite fixture set. No coefficient or compiler equivalence test is
duplicated here; those belong to the direct construction's separate
audit.
