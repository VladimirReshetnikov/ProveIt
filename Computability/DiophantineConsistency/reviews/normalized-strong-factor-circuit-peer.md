# Independent review of strong-factor normalization

Reviewer: `/root/circuit_reduction`. ROOT authored the lead. I read its
complete text, SHA256
`50c2adcb78198e111abba88344fccabfd2a493399cf02772316418eae3ea9f57`,
at `research/thirteen-variable-independent/NORMALIZED_LEAD.md`.
This review also uses the corrected complete thirteen-variable proof,
SHA256 `d2e40a04fdc670a5f5a05d2c8e7e762e07ef559eb051e5ff6f5c82e7e3e8f6a8`,
already reviewed in `thirteen-variable2471-circuit-peer.md`.

PASS for the ordinary identity, positive-domain transfer, degree and
proposed schedule. Since `S=b*i*Delta*c^2`, the normalized strong factor
is exactly

    Zbar=f^2-Delta*(b*i*c^2)^2,
    Z=Delta*Zbar, p=Delta*(P*Q*U*Zbar-1).

These are full polynomial identities. `Delta=(a+2)^2-1` is strictly
positive for every positive assignment before applying either equation.
Consequently the normalized and unnormalized thirteen-variable equations
have the same entire positive zero set by the identity map. All proved
soundness and fresh-seed completeness maps transport unchanged at the
same complete2471 tuple.

I checked the full inert source graph's uses of `Dc2`, `hi`, `S` and
`S^2`. After the scaled auxiliary replacement, the last two are live
only through the old strong factor. `Dc2` must remain because the main
norm also uses it. Replacing the two products for `S,S^2` by the three
products `hi^2`, `hi^2*Dc2`, and `(hi^2*Dc2)*c^2` is therefore valid,
with one extra multiplication. The strong and final subtractions change
their operands but not their counts; `scaled_f2` remains live through
`Theta`. This gives the stated prospective71 operations:
40 multiplications,16 additions,15 subtractions. No liveness deletion
of `Dc2` is available in that schedule.

The integral-domain degree identity subtracts the exact degree12 of
`Delta` from the independently checked degree140, giving exact degree128.
Independently multiplying the normalized strong leader
`-i^2*w^2*s^6*k0^4*q0^22` by the other three factor leaders gives

    -128*q0^69*gamma*i^2*k0^11*w^10*s^19*f^10*T^4*C0^2.

The selected coefficient is exactly `-128*beta^71`, hence nonzero at
the fixed positive beta. The analogous fourteen-variable normalization
removes degree12 from the degree118 equation and uses the same replacement
of two products by three, giving the stated prospective67/106 tradeoff.

No correction is requested. This is a review of the complete algebra and
proposed circuit construction, not of a new materialized graph, page or
unrestricted-domain lift. No incoming executable was run, and no new
formal-kernel replay or minimality claim is made.
