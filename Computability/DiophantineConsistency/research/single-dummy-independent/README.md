# Removing the high dummy

[PROOF.md](PROOF.md) gives the complete ordinary native argument and both
positive P66 maps for a length4027 tuple with one dummy. The shared
color-copy monomial `rho^18` remains. Removing the high dummy simplifies
the first mask to `MC=beta+rho-3*rho^978-G_943(rho)-Psi(rho,1)` and allows
the west/east labels and Start marker to move lower. The front still has
fifteen positive variables,66 integer-leaf operations and degree157.

South/north positions remain943..951 and961..969; west/east move to
970..977 and979..986. The sole dummy is978, and the zero-weight marker
is1006. The special fractional phase46 can spill from dummy978 into979,
which is already the physical east-bit0 label. Its own contribution is
even at that phase, so the same unique-odd-spill argument applies. The
physical temporal support remains closed without a second dummy.

This change has an explicit carry cost. The dummy may have actual value
0..3, and its adjacent coefficient is now `c_979=1024`. Its extra0/2
part contributes at most2048 to the clause predecessor. Thus
`Aadj<=2M+1024`, and the upper predecessor still resets because
`Aadj+c_0+29<3M+1024+29<rho`. The global carry bound29, all17 label
copies, the marker's offset20/tile942 contradiction and every reset are
proved for the new full geometry.

There are979 physical positions:977 weighted positions, the one dummy,
and the zero-weight marker. MC clears978 ordinary physical bits plus the
extra dummy bit. The native mask population is979, split into105 core
tests and874 padding tests. The clauses are at1994/3001, the last product
at4007, and padding occupies18 full zero fields4008..4025 plus28 low bits
at4026. The full actual rank derivation now uses mask populations
`(d-979)N+1` and `979N+1`; its conclusion `pc(R)=3t+2` remains unchanged.
Safe increments have local/spatial/temporal exponents3979/987/978.

The separately bound [verifier](certify.py) and [certificate](certificate.json)
discharge all finite geometry and controller requirements for `L=4027`,
`d=189269`. The proof author read the entire verifier, then reproduced
both normal and optimized read-only checks, including exact byte equality
of both JSON artifacts. All explicit exception guards remain active under
`python3 -O`. The earlier [finite probe](../merged-copy-one-dummy-probe/NOTE.md)
remains preserved. Exact orders are23 and1342=2*11*61, spacing30866, auxiliary prime
`lambda=246929=8*30866+1>d`, H residues18,2634,79912, and valuation-one
lift `45579142537=1+lambda*184584`. All935 support-compatible offsets
are classified: zero,933 multiple-selector exclusions and offset20
excluded by tile942. The whole four-port tuple costs94689 raw bytes,
516 fewer than merged-copy4049's95205. The
[independent whole-proof and finite review](../../reviews/single-dummy4027-independent-peer.md)
reports no unresolved new gap, including an independent reconstruction
of the changed physical layout and whole ports. Printed-page measurements
remain a separate check.

| Port | Bits | Minimal unsigned bytes | SHA256 |
| --- | ---: | ---: | --- |
| beta | 189269 | 23659 | `236f2a7313a08032b1d2b34726174a0dc2d4b4bf99be5ea989f815d32cb2cd70` |
| K | 189693 | 23712 | `506ba903a9ca9db6d51be2bce05bd9b906d0ceb7cf94cfaf094a28b99f0d5790` |
| MC | 189269 | 23659 | `33bc65bace7f8d7c281a9a5c27ff0c741af4e4c5179e29e501618d430cf25908` |
| MF_source | 189270 | 23659 | `8dcd4049c011cabd366a91458eca7463bee5ab06b9aecbedfc152ad4e14de7ad` |

The frozen complete proof SHA256 is
`a8b695c016263a3ac98851c1b54e2adb66b8254e49af2ec1447d91a3e01da638`.
The final verifier SHA256 is
`0c1e55958f20b3e0cbcd3e27488f0dadfafc23456d2c20ab8ef5eec60df09530`,
and the certificate SHA256 is
`bff400f62a90830a82dfcad43605560224efe08555b17be012d036462cd55500`.
The proof author is `/root/complemented47_review`; separate authors handle
finite implementation and independent review. Soundness has no new
controller premise; completeness uses precisely Pcsd18 in section11
whose finite conditions are now discharged. The theorem remains relative
to the named inherited ordinary arithmetic, complete syntactic-refutation
and foundational calibration contracts. No consistency decision, actual
unsolvability, global minimum or fresh end-to-end formal-kernel/internal-ZFC
replay is claimed. Every accepted predecessor remains frozen.
