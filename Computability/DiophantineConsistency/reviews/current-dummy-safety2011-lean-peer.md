# Current dummy safety: independent Lean review

PASS. Reviewer: `complemented47_review`; author: `controller_certificate`.
I read all213 main lines, all81 check lines, the complete author receipt,
both complete direct imports, and the relevant literal kernel, carry-Facts,
and rank definitions before replay. No source correction is requested.

I did not author this packet, its direct mutation/top-bound imports, or its
kernel/word-construction definitions. I authored older generic cyclic-carry
and carry-word modules, portions of the literal tile calibration/permutation,
and the separate new controller-position packet. This review is independent
of the new safety proof, not independent of every transitive prerequisite.

| Frozen source | SHA-256 |
|---|---|
| `CurrentDummySafety2011.lean` | `31f92f372076071c75ece964cb418c118fa051694057556c004d74a7353e7c00` |
| `CurrentDummySafety2011Checks.lean` | `0ff01ecb9c436f6f7043449c666d2473687725067e9aa5bd7729af39a6f7efe7` |
| `CurrentDummyMutation2011.lean` | `7bddcd9b7380e296a524ef229b467d4875e81a609dd4a4c5a7b126804a424f96` |
| `CurrentWordTopBounds2011.lean` | `7f8cf6688ef8f0152cbafd388957635a0f8a10e7e72de73fc52af87871217a1f` |
| `CurrentKernel2011.lean` | `6f8642d8d3715335dcf61fb0060818226f227db24e126d4c14d58831e76d3a55` |
| Author receipt | `512d04ac550dcafe130f768cb6f58ae7758aec90dbd857e4fda582601c2f6661` |

All Lean source paths are under `Lean/DiophantineConsistency/`, relative to
`Computability/DiophantineConsistency/`.

The complete stencil includes all three bare exponents18,1004,2020 and all
reflected exponents1005−position. Its positive coefficients have previously
proved total7659829036801887, below rho². Bounding every exponent by2020
therefore gives the actual natural K<rho^2022. Folding collisions need not
be enumerated: this estimate bounds the complete positive sum before any
folding. In particular the spatial term2020 is retained.

For `delta=rho^977*(rho^2011)^j.val` and `m=2011*N`, the explicit hypotheses
`j.val+1<N` and `j.val+s<N` give N≥2 and the respective exponent margins
1023 and1034. The kernel contribution is strictly below rho^(m−3), and
the temporal contribution is at most rho^(m−3). Their sum is strictly
below rho^(m−2), using rho≥2. All subtractions are justified by m≥4022;
none depends on a silently truncated negative exponent. The ordinary
identity `2^(displacement s)=rho^(2011*s)` keeps the unreduced stride.

The inherited top-field proof gives `F<rho^(m−1)` for the same original
assembled word and supplied carry Facts. The short-word arithmetic then
proves `F+deltaRaw<rho^m−1` with an integer margin. The mutation theorem
uses this bound and both actual transport congruences to obtain the
ordinary equality. It does not replace F with a newly chosen residue.
The new normalization is constructed by the accepted carry-existence
theorem, and Boolean controls are preserved by the actual point update.
The explicit `dummy j=0` premise is necessary and is retained.

The final rank statement is the exact signed identity for fixed generic
MC, source MF, and J, with the established changes in both C and F.
It supplies no rank positivity, target residue, or Gamma-unit premise.
No tile matching, marked origin, high-mask acceptance, or desired ordinary
increment is assumed by the numerical safety theorems. The checks exercise
stride0, coincident destinations, repeated integer casts, the last permitted
cell, N=1 exclusion, omitted-position-condition boundary failures, and a
freshly constructed two-cell old/new normalization with arbitrary tiles
and Boolean marker controls.

I freshly compiled both reviewed sources sequentially with Lean4.32.0,
`-M6000 -j1`; both set `Elab.async false`. Outputs were isolated under
`/tmp/current-dummy-safety2011-complement-peer-800cl2qq/lib/DiophantineConsistency`.
Unchanged prerequisite objects were symlinked into that namespace; the two
reviewed object bundles were excluded and rebuilt. The checks imported
the fresh main through LEAN_PATH prepended after `lake env`. This is a
fresh two-module replay, not a replay of the entire dependency closure.

Both first replay attempts exited zero. Main:6.41seconds, peak RSS
3,288,048KiB, empty log. Checks:4.21seconds, peak RSS3,255,420KiB, no
warnings or errors. All13 axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. Both objects are byte-identical to
the author's shared objects. No reviewed source contains a new axiom,
`sorry`, or `native_decide`.

| Replay artifact | SHA-256 |
|---|---|
| Main object | `987d72a91d4496ebe5273b9be53576455f04ba7340fb18c12991520ab5f3fcd6` |
| Checks object | `031d186efa0644193edcb75ceb561d5104a04476926c168b681491b2d8f0e0c3` |
| Main log | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Checks log | `a2d37437411d2f00b424922f2558d7ae1fb18ea3084d520a83e86fabbf91b4be` |
| Before and after input manifests | `0401f12124ecb07fb144352e6b95d23e450ae313a8035b561f4637ee80043924` |
| `REPLAY.json` | `cf00626983eef45f8774387c6a500462ca4973c435fb83256bf7d212ea286797` |

All14 pinned source/object inputs remained unchanged. Only this new peer
receipt and temporary replay artifacts were written. No frozen source,
shared object, central document, or Git state was modified. A finite-support
iteration and final controller/rank composition are still separate work;
this receipt does not claim the complete equation converse.
