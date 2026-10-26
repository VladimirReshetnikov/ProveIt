# A Boolean-only controller dummy

[PROOF.md](PROOF.md) gives the complete ordinary proof for a simpler
length4027 recipe. The controller dummy at978 now permits only0 and1.
Every canonical safe subset already uses those values, so the construction
needs only `MC=beta+rho-rho^978-G_943(rho)-Psi(rho,1)`. The coefficient3
from the preceding mask is removed. The complete kernel, label layout,
marker and length remain the same; both changed whole masks are specified
afresh. The front retains fifteen positive variables,66 operations and
degree157.

Physical support still contains979 positions, but MC now clears exactly
978 bits: every physical position except forbidden selector1. There is
no extra dummy-bit clearing. The complementary native population is978,
made of105 core tests and873 padding tests. Padding uses18 full fields
4008..4025 and27 low bits at4026. The actual rank proof explicitly uses
populations `(d-978)N+1` and `978N+1`, again giving `pc(R)=3t+2`.

This also simplifies decoding. Every physical C digit is Boolean, so all
fractional phases1..46 produce only even temporal digits and never spill.
The Start parity tests force fractional phase zero directly. The whole
raw bound is `Uraw<=Csum+3`, the temporal digit bound is `rho/2`, and the
same global carry bound29 suffices. The low reset is `3+rho/2+29<rho`.
At a clause predecessor, the Boolean dummy contributes its next label
coefficient only once, so `Aadj<=2M-1024` without an extra2048 allowance.
The exact tile942 offset20 obstruction, all seventeen copies, marker
relation, origin resets and every padding test are restated.

Completeness constructs fresh one-Start rectangles with the same shifted
marker `a_j=x_(0,j+width)` and initializes the sole dummy to zero. Each
chosen safe subset changes distinct dummy bits to one and remains inside
the new mask. Exact ordinary F and rank increments therefore retain the
whole controller orbit and positive P66 witness maps. No inherited step
requires a dummy value2 or3. The final [verifier](certify.py) and
[certificate](certificate.json) check this changed interface and the
complete new ports. The proof author read the whole verifier and
reproduced normal and optimized read-only runs with exact JSON equality.
All guards remain active under `python3 -O`. The verifier additionally
checks whole-mask acceptance `[true,true,false,false]` for dummy digits0..3,
actual shifted-origin populations, and exact whole-rank identities on
finite mask-compatible samples; those samples are not claimed as tilings.

The proof SHA256 is
`d5a364a28ba03433cb97ae57bc9c8f62806694752beae40aa805bff92b8de96f`.
The final verifier SHA256 is
`c84ace45cdc45693640aa7dea3a93f2234e7a4fba3d8db6afe0a56951b515d71`,
and the certificate SHA256 is
`ed634aba0bb722f15ee673e7fbe3bcd2523a987aa8b40f01365211f51fc5cfcf`.
Soundness has no new controller premise; completeness uses exactly Pcbd18
in section11, now discharged by the bound certificate. The checked
controller facts are orders23/1342, spacing30866, lambda246929 and H
residues18/2634/79912. The full tuple remains94689 raw bytes; its K and
beta are unchanged, and its two changed masks have the following hashes.
Independent full mathematical review is pending. Printed size is measured
separately.

| Port | Bits | Minimal unsigned bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta | 189269 | 23659 | `236f2a7313a08032b1d2b34726174a0dc2d4b4bf99be5ea989f815d32cb2cd70` |
| K | 189693 | 23712 | `506ba903a9ca9db6d51be2bce05bd9b906d0ceb7cf94cfaf094a28b99f0d5790` |
| MC | 189269 | 23659 | `9113894179bcb055af8eed0131f6263d064354fc1ade02a5c920ae2a0c2d16d3` |
| MF_source | 189270 | 23659 | `2537c625f8fa2c61a3335556e5d6f42550891932a0dc559f77b9a6f345cb71b6` |

The proof author is `/root/complemented47_review`; separate authors handle
finite implementation and independent review. The theorem remains relative
to the named inherited ordinary arithmetic, complete syntactic-refutation
and foundational calibration contracts. No fresh end-to-end formal-kernel
or internal-ZFC replay, consistency decision, actual unsolvability or
global minimum is claimed. Accepted predecessors remain frozen.
