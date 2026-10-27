# Native adaptive first-carrier author receipt

The new 130-line `NativeAdaptiveCarrierBootstrap.lean` and 43-line Checks
passed their first private Lean 4.32.0 compilation. I authored and fully
read both files and the driver before execution, and reread both final
sources afterward. This is an author receipt, not independent review.

The frozen main SHA256 is
`0975b336fd452dff7c68a8ccb795c8af516c2c08dac6940542b0f148f2dc1761`;
Checks is
`bf4289cc5c9c15ca48cc42f158aaf99e3490478378e42108011e1ed2cc626cff`.
The durable complete replay bundle is
[native-adaptive-carrier-bootstrap-replay.json](native-adaptive-carrier-bootstrap-replay.json),
SHA256 `308a402e442fabb3a99929b095849d658e321f60cabca026564515a602f49a5c`.

## Exact mathematical scope

`firstZ` and `firstA0` are the actual signed first-carrier cuts of the
historical unrestricted-J 13-input graph. The first theorem assumes only
q>1, ell,k,r,Y>0 and this A0=0. It derives positive integers s,b and a
signed integer tau satisfying Y=q^3*s, Bt=(q-1)*b, Z=M*tau,
tau^2=ell*(ell+k)+1, the exact transport expression for tau, and
0<|tau|<ell+k. It derives square divisibility and uses explicit polynomial
Bézout identities; no coprimality-with-three premise is present.

`transport_positive` derives C=q-F-alpha>0 from the actual Bt formula,
Bt>0, q,X,F>0 and K>=0. `classify_signed_first_norm` casts positive Q,k
and tau.natAbs into the existing generic first Pell classification. It
retains |tau| and never asserts tau>0. Focused checks include a negative
root (Z/M=-3), a q divisible by three, the first Pell index for a negative
root, and the generic signed transport client. The numerical carrier checks
test this generic carrier domain; they are not asserted to be full
thirteen-input polynomial zeros.

There is no A1 proof, four-factor unit extraction, actual current-port
corollary, graph/metric audit, restored source, main-index recovery,
equation-equivalence or internal consistency result in this packet. Those
remain downstream. No existing/frozen Lean source, display or shared object
was changed.

## Cache and execution

The sole main import is `DiophantineConsistency.NativePellBootstrap`;
Checks imports only the new main. The exact proposed closure was authenticated
against the accepted shifted-source inventory and rechecked before/after:
25 reused custom source/object pairs, 22 external boundary names including
implicit Init, 66 external object companions, 145 total input pins. Every
selected source's current parsed imports matched the frozen import records.
All selected external source/artifact hashes matched; no new boundary,
Foundation build or prerequisite rebuild occurred.

The private directory is `/tmp/native-adaptive-carrier-t5lulzt2`; its
`lib` contains links only for the authenticated prerequisites. The two new
target objects were absent before execution and are new regular files.
The driver is `/tmp/native-adaptive-carrier-driver.py`, SHA256
`fc92121b346a600ce5980ac55e6547027f7661c75be33f90301f62c3f5f120e9`.
Complete driver, source snapshots, logs, timings, input records and final
state are embedded in the durable replay bundle. No failed compiler attempt
preceded this successful pair.

Both commands used the pinned 4.32.0 binary with
`-M6000 -j1 -DElab.async=false -o <private regular object> <source>`;
LEAN_PATH contained the new private overlay and the authenticated external
package roots, not the project shared cache. The 512 MiB reserve was checked
before each command and at completion; final available disk was 720773120
bytes.

| Target | Seconds | Peak RSS, KiB | Exit | Object SHA256 |
|---|---:|---:|---:|---|
| Main | 11.952 | 3235868 | 0 | `2ef643d6db2ac5d0b0b7911416e260e9469aa6cd7076899a2b93309dfa722f6a` |
| Checks | 2.887 | 3204480 | 0 | `a6c0c7c23ada14955bb7938a00b49df337b681706600bc81c7caf01e16660a51` |

Main produced no diagnostics. The five actual axiom reports contain only
the standard axioms: the two definitions report propext; the three theorems
report propext, Classical.choice and Quot.sound. There is no sorry,
native_decide or new axiom.

The private input record SHA256 is
`a3683214e5b213f0555479c925e784d4cca451c65cdacb038bf0dc7353e7ebce`;
the final state SHA256 is
`ddeb972834d99bb5e43aa2e98197db2a93213678ec344616b14d4fc420f21094`.
The read-only proposal and closure inventory remain unchanged at
`cdddfed4a9436479554f6f34808498fb090e11d141f1060e3869c6e2243b5af4`
and `21917ee6855045afd5c9494868c431f2bd8e2ed67b3ef621e8772f42cdc6b915`.
