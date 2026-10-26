# Independent review of the Boolean-dummy4027 proof and certificate

Reviewer `/root/controller_certificate`; proof author
`/root/complemented47_review`; finite author `/root/circuit_reduction`;
ROOT coordinates promotion. The reviewer did not edit these artifacts.

**PASS.** I read the entire564-line proof, README and492-line verifier,
checked the full difference from the separately reviewed single-dummy4027
tuple, and ran the verifier in normal and optimized read-only modes.
Both runs reproduced the exact certificate and coefficient artifact.
An independent stdlib-only reconstruction importing no project module
also reproduced every whole port and its hash, the changed mask domains,
padding and rank populations. No mathematical or finite-check gap was found.

## Exact bindings

Paths are relative to `Computability/DiophantineConsistency`.

| Artifact | SHA256 |
|---|---|
| `research/boolean-dummy-independent/PROOF.md` | `d5a364a28ba03433cb97ae57bc9c8f62806694752beae40aa805bff92b8de96f` |
| `research/boolean-dummy-independent/README.md` | `06c74d2f6d1cecdcdd996a9b6a42307bdb2c4b23b87cf593011025ac2c6d7c66` |
| `research/boolean-dummy-independent/certify.py` | `c84ace45cdc45693640aa7dea3a93f2234e7a4fba3d8db6afe0a56951b515d71` |
| `research/boolean-dummy-independent/certificate.json` | `ed634aba0bb722f15ee673e7fbe3bcd2523a987aa8b40f01365211f51fc5cfcf` |
| `research/boolean-dummy-independent/coefficients.json` | `485f3e3bfa617cb5a1b7aa98447d3629b8e53057d0f2aed5eecb56fd6b52ac98` |

The verifier authenticates the full new proof and previously reviewed
decoder/helper chain before import; the preserved complete radix55 language
has page hash `440cf0853ec2f992db7aa6146aec42c189368375d8db725d3df085ca27dc4dff`.
The source uses explicit exception gates, and optimization is harmless.
Neither run used `--write`.

## Whole ordinary argument

The support still has979 positions:943 selectors,34 weighted labels,
one Boolean marker and one Boolean controller dummy. Coefficients, kernel,
L4027 and d189269 are unchanged from single-dummy4027. The changed MC
clears exactly978 physical bits, excluding selector1; it now clears only
the low bit of dummy978. Thus dummy values0/1 pass and2/3 fail. Native
population becomes978, comprising105 core bits and873 padding bits.
The latter use18 full fields4008..4025 and27 low bits at4026. All scalar
boxes, origin residues and the single beta source-mask shift are retained.

This is a genuine restriction of the soundness mask domain. The proof
uses it before phase recovery: every digit is Boolean, so multiplication
by `2^s`,1<=s<=46, gives an even value below rho with no spill. Temporal
digits are at most rho/2. The full raw bound `Uraw<=Csum+3` and low reset
`3+rho/2+29<rho` are valid. A clean count clause still recovers at most
one selector before the phase or marker relation is known.

The full field-offset argument is unchanged and correctly reapplied.
All935 support candidates split into zero,933 multiple-selector cases
and offset20, where the complete decoded tile942 south74 contradicts
the required south bit0. All17 label copies and the marker test follow;
the marker is the shifted Start indicator, not an assumed all-one flag.
Occupation follows from positive complemented colors.

Every copy, clause, predecessor and padding identity is restated. The
Boolean dummy contributes `c979=1024` once within the label sum; there
is no extra2048 term. Consequently `Aadj<=2M-1024`, and the upper
predecessor's exact extra `c0*x1006` plus carry29 remains below rho.
The last product4007 resets, and all fields4008..4026 are actual zero.
The top bound, strict canonical representative and ordinary safe-increment
margin therefore apply to all fresh subsets.

Completeness does not need a dummy value2 or3. It starts from zero and
toggles distinct safe bits once; all simultaneous subsets stay in the new
Boolean mask. The index construction ensures the local, spatial and
temporal increments do not wrap. Their exponents3979/987/978 and the
degree-plus-one margins give the stated three-term bound below `q/rho^2`.
The actual representative changes by the ordinary deltaRaw, giving the
same algebraic deltaR with the newly formed actual rank.

The rank proof explicitly changes both populations to
`(d-978)N+1` and `978N+1`, whose sum is still `t+2`. Its disjoint binary
identity gives `pc(R)=3t+2`, with `R=3 mod4` from origin residues. The
controller is applied to this actual new rank; it does not reuse an old
rank value or old packed witness. The complete orbit/subset construction,
positive transport multiplier and both full positive P66 witness maps
remain valid. The66-operation uniform graph,15 positive inputs and exact
degree157 remain the retained symbolic facts at the four new ports.

## Finite evidence and independent reconstruction

The full3297 coefficient array is byte-identical to the independently
reconstructed single-dummy4027 array. I also compared the entire fixed
controller records and auxiliary-prime trials, which are unchanged because
beta and K are identical. The new verifier nevertheless reconstructs
the complete finite language and all new whole masks, checks every
geometry comparison, and binds the new proof and both changed ports.

My independent reconstruction formed MC both from the physical support
and from the closed Psi recipe. It checked the actual dummy field equals
`rho-2`, with acceptance pattern `[true,true,false,false]` for0..3.
It verified the positive padding sum against its telescoping formula,
populations105/873/978 and MC population188291, scalar boxes and origin
residues. It checked all46 nonzero fractional phases for parity and
absence of spill, and independently recomputed the carry and adjacency
inequalities. All four full integers match the certificate hashes below.

The verifier's whole-word rank controls use1,2,3 cells, with all dummy
bits off and on. I additionally checked a four-cell mask-compatible word
with only dummy cells0 and2 on: both rank formulas agree exactly, the
mask population is t+2, rank population is2271230=3t+2, and residue is3
mod4. These finite words check mask/rank algebra; they are not claimed
to be canonical tilings. The universal rank identity was reviewed in the
ordinary proof. The physical-marker omission control still rejects the
whole mask population and phase support despite its zero coefficient.

Exact orders of2 andB are23 modulo47 and1342=`2*11*61` modulo4027,
both coprime to d. The spacing is30866 and the prime is
`lambda=246929=8*30866+1>d`. All primality, factor/order and lift tests
were independently reproduced in the preceding single-dummy4027 review;
the full unchanged controller records were compared here. H values are
18,2634,79912; B-squared values16,519,234415 are not1. The valuation-one
lift is45579142537=`1+246929*184584`. The new finite Pcbd18 premise is
therefore discharged for the exact Boolean tuple.

| Port | Bytes | SHA256 |
|---|---:|---|
| beta |23659|`236f2a7313a08032b1d2b34726174a0dc2d4b4bf99be5ea989f815d32cb2cd70`|
| K |23712|`506ba903a9ca9db6d51be2bce05bd9b906d0ceb7cf94cfaf094a28b99f0d5790`|
| MC |23659|`9113894179bcb055af8eed0131f6263d064354fc1ade02a5c920ae2a0c2d16d3`|
| MF_source |23659|`2537c625f8fa2c61a3335556e5d6f42550891932a0dc559f77b9a6f345cb71b6`|

The total remains94689 raw bytes. The simplification over the immediately
preceding single-dummy tuple is the mask formula and ordinary proof, not
a further raw-byte reduction. Printed-page measurements belong to the
separate page review. This establishes no global minimum, consistency
decision, actual unsolvability or fresh formal-kernel/internal-ZFC replay.
The full ordinary equivalence retains its named arithmetic, syntactic-
refutation and foundational contracts.
