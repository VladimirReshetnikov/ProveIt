# Adaptive positive source restoration: author checkpoint

2026-10-26. Author `/root/complemented47_review`. The complete final main,
focused checks and replay driver were read before execution and the final
sources were read again after the clean run. This is author validation;
root's independent replay and acceptance are separate.

The new main `Lean/DiophantineConsistency/NativeAdaptiveSourceRestoration.lean`
has 373 lines and SHA256
`d3dbdffe6ad47d9da540cccbc7017a8bb52bfc56901b38923d28ba74c84fbc08`.
Its 43-line Checks file has SHA256
`9d0ad78824372fb0a2548eaedbdb2835ad0afab3911b563e9d205e08b46b1483`.
The sole main import is frozen `NativeAdaptiveMersenne`. Existing proof
sources, shared objects, coefficient tuples, displays and Git were untouched.

## Exact theorem and proof boundary

`adaptive_positive_source` assumes the original thirteen positive integer
inputs, the literal definitions of k, q, target R and Bt, `PortBox ports`,
`ports 0=2^d−1` with d≥4, and precisely the four cuts
`firstA0=0`, `mainA1=0`, `strongFactor=1`, `auxiliaryFactor=1`.
It constructs one `x : Fin 31 → ℕ` with every coordinate positive and every
literal `SplitCertificate59.sourceRows ports (↑x)` equal to zero. The output
retains J, F, alpha, f, i, eta, zeta, X, the literal V, y=V+u, and
`NativePellBootstrap.nativeRank x=R`.

The statement receives no restored source, index equality, power identity,
q-divisibility, positive ordinary gamma, or ordinary coordinate quotient as
a premise. It uses the accepted all-positive adaptive chain to derive them.
All four ports stay unchanged, including the already shifted MF at port 3.
The width is generic and admits the current d=47*2011; this leaf does not
independently reprove the concrete current port bounds.

The construction has the following explicit stages.

- The signed first-carrier theorem supplies positive s,b, with Y=q³s and
  Bt=(q−1)b. The Mersenne endpoint supplies q|X and hence positive w with
  X=qw. The literal Bt identity becomes qB=(q−1)b for
  B=(K+w)(q−F−alpha)−F. `transport_quotient` sets z=b−B and proves
  b=qz, B=(q−1)z and z>0. The original source coordinate at index 3 is
  **z+1**, not the shifted quotient z.
- Projection supplies 2n=R+1, n≥25 and k=2ψ(n). The actual Pell bound
  ψ(n)>n proves k−R−1>0. Divisibility by 4XY² yields positive h with
  k−R−1=XYh. Divisibility by U=q²Y yields the integer quotient t, also
  positive. None of these quotients is an extra variable premise.
- The strong endpoint supplies positive D,j,o and the exact congruences
  V=jc−R=of−c with c<V. A1 gives D²=1+δc². With
  gammaOld=gamma+w−t, cancellation of positive U proves
  D=X+ac+(4a+3)gammaOld. The existing large-c bound gives X<c. The exact
  identity D²−((a+1)c)²=1+2(a+1)c² then forces gammaOld>0; positivity is
  not inferred from the signed difference gamma+w−t alone.
- The source Pell root is the absolute value of the first signed quotient.
  Its square is unchanged. The source auxiliary gap is y²−V²>0 because
  V>0 and y=V+u>V. The actual strong and auxiliary cuts provide the last
  two original rows.
- `source` records the complete 31-coordinate order. `source_positive`
  checks every coordinate explicitly. `source_rows` checks all 22 literal
  original-order rows with definitional `change` statements and ring
  identities, including rank, original transport, and both norm equations.
  Only after positivity is proved is the tuple converted with `Int.toNat`;
  each cast back to ℤ is identified with that same coordinate.

The focused checks retain the old/shifted transport distinction, the exact
i*c² coordinate, the gamma positivity interface, a negative-quotient
counterexample when positivity is omitted, and the literal rank coordinate
binding. Five principal theorems have axiom audits.

This is the approved first restoration pair only. It does not bind the full
historical 13-variable graph/product to these cuts, prove a canonical
converse, compose a current polynomial/ConZFC endpoint, or establish an
internal HA/PA theorem. Those remain separate work. In particular, no new
equation-size or global frontier claim is made.

## Authentication and bounded replay

The approved proposal remains byte-identical at SHA256
`ec436d67ca7b45ca654086572416ecd1de3c591d66a122caafd71fa0e4be89ff`;
the frozen cache audit is
`c2dfe2c604c5b5cfdbf2a67abc65a9798e90378f613200980db6d188b18647d8`.
The selected Mersenne object is root's independently accepted provider
`/tmp/native-adaptive-mersenne-root-gah0zove/lib`, recorded by ROOT SHA256
`1d94b06188bd72dbee9cf0cd495e3aeb2a8d6d671411d6e087729eea211bac21`.

The driver authenticates 33 cached custom source/object pairs, 22 explicit
external names including implicit Init, and all 66 external companions.
Its 187 distinct execution pins include current source/import closure,
objects, compiler, predecessor evidence and source-only guides. They are
checked before and after the run. The external package boundary is reused;
there is no Foundation, prerequisite, package, or whole-chain rebuild.

Final private overlay: `/tmp/native-adaptive-source-restoration-j5s7732x/lib`.
The two new outputs are regular non-symlink files; only cached inputs are
linked. Commands use the pinned Lean 4.32 executable with
`-M6000 -j1 -DElab.async=false`, one Lean thread, no `LEAN_SRC_PATH`, and the
512 MiB reserve check before each command and at completion.

Final main/checks pass in **12.613 / 3.011 seconds**, with peak RSS
3,351,400 / 3,208,216 KiB. The main log is empty, with no warnings or errors.
All five reports contain only `propext`, `Classical.choice`, `Quot.sound`.
Final free space was 1,955,418,112 bytes.

Final object hashes:

- Main: `19c6aa468fb51283a32c2efc0899df06012bfa36909226816f8242c8a250043e`.
- Checks: `5fd86424d9efc9222caca3cff3c7c62cc5bdd9f79f381642445ca233da41b199`.

Driver `/tmp/native-adaptive-source-restoration-driver.py`: SHA256
`ca468e6d2018c557f74a8eac7415cb791b86d8ea66fbce0bd35c64cdd852ffbe`.
Final inputs: `1fc4bd79f45c3b2a2ce70aa5265f620fb40d8bc5bc1856fb384df416c395bc74`.
The durable replay JSON is `native-adaptive-source-restoration-replay.json`,
SHA256 `3228854d5e430585198928063a65b647acf5f8b8b73749d49af3bcb8108dd4d0`.
Its 32-file manifest, `native-adaptive-source-restoration-replay-files.json`,
has SHA256 `0ec0f74d180772014bdeeffba498934442b3269579d663bae5697f58176e5f44`.
The bundle preserves all five inputs/state records, source snapshots,
logs/timings, complete driver, freeze script, proposal and cache audit.

Four failed main attempts preceded the final pass. The first caught `<i`
token spacing, a linear-combination sign, and the default heartbeat cost of
a single vector-row simplification. The second exposed unreduced match
positivity goals, nested tactic sequencing in the Pell base proof, an
implicitly inferred wrong rank parameter and repeated-cast rewriting. The
third retained diagnostic match goals after those other fixes. The fourth
had two reintroduced `<i` tokens in explicit coordinate branches. Final
source uses literal index matches, explicit row/positivity cases, the
specified rank parameter and complete cast rewriting. The mathematical
endpoint and resource caps were not weakened. All failed evidence remains
historical, not an accepted proof. The fifth main and first executed Checks
are the final clean pair.
