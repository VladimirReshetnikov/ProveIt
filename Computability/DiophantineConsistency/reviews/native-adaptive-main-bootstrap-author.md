# Native adaptive main-carrier author receipt

The new 192-line `NativeAdaptiveMainBootstrap.lean` and 59-line Checks
are frozen and passed the final private Lean 4.32.0 replay. I authored and
fully read both sources and the entire 160-line driver before execution,
then reread the complete final sources. This is an author receipt, not
independent review. No accepted source, shared object, display, or Git
state was changed.

Main SHA256:
`a735876afcc033877741f414e233f1dea1bc9209899979fd83fc8308733eae7a`.
Checks SHA256:
`45c7469d705ea9c99b20f6e37768aa2bc6216a84a0011fb34d6c670c8c22020f`.
The complete durable replay is
[native-adaptive-main-bootstrap-replay.json](native-adaptive-main-bootstrap-replay.json),
SHA256 `4a541172db640db109e39737f78b9c27dec6807f1f04a0bc4486d8c00bd6fb61`.
It embeds the driver, both attempts' exact source snapshots, commands,
logs, timings, input inventories, states, object pins, and axiom reports.

## Proven scope

The literal signed `target`, `mainDstar`, and `mainA1` match the displayed
cuts of the unrestricted-J adaptive graph. `target_positive` assumes only
q>1, alpha,J>0, MC,MF>=0, and C=q-F-alpha>0. It proves R>0; the actual
target wrapper therefore derives v=k-R-1<k. `target_positive_of_transport`
derives C>0 using the accepted first-carrier transport lemma rather than
a source or rank assumption. MF is already shifted; it is not shifted again.

`mainDstar_positive` assumes q>1, X,Y,k,eta,gamma>0, q^3 dividing Y,
and v<k. It derives Y>=8 and a positive U*a*Y-H, then proves positivity
of the actual Dstar through the exact ring identity in the approved
proposal. It allows negative v and q divisible by three.

`main_carrier_bootstrap` adds only the literal A1=0. Integer square
divisibility supplies D with Dstar=U*D; the preceding positivity argument
forces D>0. It retains that signed equality, cancels U^2, and proves the
main norm. The exact transport H(qXY-v)=U(D-X-ac-H*gamma), together with
q^5 dividing U, feeds the accepted factor-three theorem and gives q^4|v.
`classify_positive_main_norm` casts the positive signed coordinates into
the generic main Pell classification. The returned D is not replaced by
its absolute value. The final target wrapper retains all these conclusions
while deriving v<k from the explicit target.

There is no restored source, rank window, index comparison, large-c bound,
power recovery, concrete coefficient specialization, canonical converse,
complete adaptive polynomial binding, metric, or HA/ZFC endpoint here.
Upstream unit extraction and the later source reconstruction remain separate.
The current code imports no `source_*` classification theorem as a premise.

Focused checks cover q=3 with negative v and the exact positive Dstar,
an unrestricted target example, the positive first main Pell root, and
both generic and literal-target q^4 divisibility clients. The numerical
controls are generic arithmetic examples, not claimed thirteen-input zeros.

## Authenticated inputs and replay

The only main imports are the accepted `NativeAdaptiveCarrierBootstrap`
and `NativeAdaptiveFactorThree`; Checks imports only the new main. The
private overlay reuses exactly 27 custom source/object pairs: the accepted
25-module NativePellBootstrap closure plus these two frozen leaves. It
retains all 22 actual external names including implicit Init and all 66
external object companions. All 149 pin observations, current custom
import headers, and external source/artifact hashes were verified before
the final replay and again afterward. No Foundation or prerequisite build
occurred and no new boundary was introduced.

The first-carrier object is the root independently replayed
`/tmp/native-adaptive-bootstrap-root-qdo6f38v/lib/DiophantineConsistency/NativeAdaptiveCarrierBootstrap.olean`,
SHA256 `2ef643d6db2ac5d0b0b7911416e260e9469aa6cd7076899a2b93309dfa722f6a`.
The factor-three object is the independently replayed
`/tmp/native-adaptive-factor-three-peer-0z7ha_1s/lib/DiophantineConsistency/NativeAdaptiveFactorThree.olean`,
SHA256 `bcb54d6683b952870f88545ea5a85bfcb67ef335f89f30f45044385c6b18c4a8`.
The complete remaining pairs and actual external names are preserved in
the embedded input inventory; no representative-pin shortcut was used.

The final private overlay is `/tmp/native-adaptive-main-1v3mu3_y/lib`.
Target outputs were absent initially, created as regular nonsymlink files,
and never copied over accepted shared objects. LEAN_PATH contains only
the private custom overlay and the authenticated package roots. Commands
use the pinned 4.32.0 compiler with `-M6000 -j1 -DElab.async=false` and
private `-o` outputs. The 512 MiB reserve was checked before each command
and at completion; final available disk was 2358870016 bytes.

| Final target | Seconds | Peak RSS, KiB | Exit | Object SHA256 |
|---|---:|---:|---:|---|
| Main | 7.941 | 3246104 | 0 | `77c60c8d47ca50d9fefdfdbd0ee3981dd4ae512e1e7280e83efe897ee3079e2d` |
| Checks | 2.805 | 3206376 | 0 | `d4fe7c7cb86ac62b773a3b97f5fb06192678ac5c2bf2948dc21f3a6f6c1a6df9` |

Main produced no diagnostics. All nine actual axiom reports use only the
standard axioms: three definitions report propext; the six theorems report
propext, Classical.choice, and Quot.sound. No sorry, native_decide, or new
axiom is present.

The first main attempt in `/tmp/native-adaptive-main-g4equ07g` exited 1
after 7.754 seconds. It found two proof-elaboration issues: an inferred
factor in `mul_le_mul` needed an explicit 4*12 bound, and the factor-three
call needed its explicit X argument plus multiplication reassociation.
Only those proof steps changed; all public statements and mathematical
premises are identical. The failed main snapshot and complete log/state
are preserved, and Checks was not launched on that failed attempt. No
timeout, cap increase, or discarded failure preceded the final pair.

Driver `/tmp/native-adaptive-main-driver.py` SHA256:
`b5faa8b7180b2016a6aa0e82667f0d126dc5ffb1a5f1fd7b27903bd1c05f0e16`.
Final input inventory SHA256:
`9e9e60b181bd2555c971ca17d3cfa9b88c67e1027a00dbb5e63c498d1f72d6bd`.
Final state SHA256:
`adb20c4e5812fd0046d1c3a731321f1ec924bc97a218f8fc289f1f1ff6647625`.
The approved proposal remains frozen at
`3188d4a5fa028e0c149035d48bf3757de981a56d6f9f5c00a05d6ec952961d15`.
