# Exact controller data: independent root review

Date: 2026-10-26. Author: `complemented47_review`; reviewer: ROOT.
Result: PASS for the stated finite-data scope. ROOT read all184 main
lines,76 check lines and the complete author receipt before replay.
ROOT authored none of the new finite-data statements or their proofs.

| Source | SHA-256 |
| --- | --- |
| `CurrentControllerData2011.lean` | `a86aa5cc6b523bd659df8681012a1a39307ea340c27a7785629d30699ca151ae` |
| `CurrentControllerData2011Checks.lean` | `94c31dd43489bb37d8aae28af221f7e7e9e95c7c6f32b3b98a5ec00c28cdb43a` |
| Author receipt | `41e3d4873350db2dc51bdf184405cce9770576fd852d055096e71da51d4da018` |

The definitions are bound to the actual current radix and width, not an
unrelated coefficient tuple. Primality, squarefree factorization, the
spacing lcm, exact orders23/402, base/square residues and the nontrivial
auxiliary-square lift are unconditional. The order402 proof tests every
prime divisor of402. Exponent11360754366 is reduced in the finite ring
by proof-producing modular squaring, without constructing the natural
power. The cast-to-remainder lemma retains the strict residue bound.

The last three wrappers visibly require the actual kernel residues26,
1995 and114787 as hypotheses. Those hypotheses have not been proved by
this module or by this review. Keeping K locally irreducible only limits
elaborator reduction; it adds no axiom or premise to earlier finite facts.
The module does not discharge the full Pcst interface, the power-orbit
classification, CRT, safe mutations or any polynomial converse.

ROOT replayed both complete sources sequentially under the pinned
Lean4.32.0 toolchain with `lake env lean -M6000 -j1` and the sources'
`Elab.async false`. The main and then checks wrote their named shared
objects; this was a fresh two-target replay reusing prerequisite objects,
not an isolated overlay or a fresh full dependency build. Both terminal
results were exit0. The main log is empty and all21 requested reports
are axiom-free or use only `propext`, `Classical.choice`, `Quot.sound`.
No `sorry`, `admit`, `native_decide` or added axiom occurs.
Both objects are byte-identical to the author's final objects.

| Root replay evidence | SHA-256 |
| --- | --- |
| `/tmp/current-controller-data2011-root-main.log` | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| `/tmp/current-controller-data2011-root-checks.log` | `9c8cca3bb9c6b55998a4e4a85108ce6991646f8db3f4a5c858c1b21bb36bbc55` |
| Main `.olean` | `d3e59650f41406c44c43bd0d702a16b9256f21c1242c6faeb4bbf0439951a7b8` |
| Checks `.olean` | `2ff1ef64160c12b118478622b09ed17e6c5b33875dc987a5e8c8dd855f5302cc` |

The author receipt accurately distinguishes the terminated development
job and later excessive-memory conversion errors from the final passing
proofs. ROOT's successful replay needed no cap increase or source edit.
The equation artifacts and literal native coefficient definitions remain
unchanged. The goal, full equation converse and internal-ZFC work remain
active/open.
