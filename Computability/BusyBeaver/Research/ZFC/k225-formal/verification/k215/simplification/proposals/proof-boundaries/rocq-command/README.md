# Rocq command/codec factorization pilot

Baseline: `VladimirReshetnikov/ProveIt` at
`6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95`.

This component brings the maintained Lean enumerator's separation of command
effects and numerical decoding to the current Rocq enumerator. It proves an
exact adapter against the existing `EnumPerm.enum_step` and
`L1_CompPerm.xstep`. It changes no production file or machine table. The
underlying design is credited to the repository's existing Lean `EnumPerm`
(`Cmd`, `cstep`, `decode`, `fetch`, `execAt`); the contribution here is the
checked Rocq adapter and its current-source soundness clients.

## Interface

For any current state `s`, let `(z,next)=fetch s` and `(c,rest)=decode z`.
The checked theorem is

```coq
enum_step s = option_map (restore rest next) (xstep c (tupof s)).
```

`decode_fields` states that encoding a command followed by a remainder and
decoding it recovers that exact command and remainder. `decode_le` says that
the remainder never exceeds the input code. Both statements are about the
literal Cantor decoder used by the retained Rocq code. There is no finite
test bound and no well-formed-formula premise: every natural-valued state and
code, including junk codes, is covered.

The two generic lifting theorems establish preservation and halting soundness
for any working-register predicate preserved by `xstep`. The concrete
`WorkingInv` uses the existing theorem-stack invariant. Its command proof is
proved directly from the current command effects, theorem constructors, and
stack lemmas; it does not invoke the original `Inv_step` or `halt_step`.

## What becomes simpler

The four proof clients become short codec-independent consequences:

| Existing theorem | Existing lines | Pilot client lines |
| --- | ---: | ---: |
| `L1_CompPerm.step_read` | 20 | 10 |
| `L1_CompPerm.step_pl` | 22 | 9 |
| `L1_SoundPerm.Inv_step` | 24 | 2 |
| `L1_SoundPerm.halt_step` | 12 | 2 |

Counts include each declaration and `Proof`/`Qed`, exclude preceding comments,
and are reproduced in `comparison.json`. The total pilot is 145 lines and
6,312 bytes. **This is an additive adapter, not a net reduction of 55 lines.**
The 23 client lines depend on the additional shared infrastructure. Current
production source is not shortened by shipping the adapter alone.

The proposed integration is to move `cmd`, `tup`, the codec, and `xstep` into
one dependency shared by the enumerator's soundness, completeness, and L2
simulation. Define the enumerator through that interface, retain compatibility
aliases where qualified old names are public, and remove the repeated field
decoding from the clients. Next port the `L2RootPerm` decoder/command boundary
from Lean so the physical root correctness proof consumes the same `xstep`.
Measure the whole changed source-and-generator boundary after these removals.
If it grows for K215 alone, justify adoption by shared use across the retained
enumerator variants rather than reporting only shorter wrapper bodies.

## Reproduction and acceptance scope

The driver needs a checkout containing the pinned sources, a complete Coq/Rocq
installation, and Python 3.10 or later. It checks every source hash against
`source_provenance.json`, compiles into a fresh directory, and performs a
recursive `coqchk CommandFactor` check. It does not use prior project objects.
The retained reference code is read from the current repository's existing
proposal source copies; it is not bundled again with this pilot.

The two arithmetic support files were separately compared with the external
production reference `elliotglazer/k230-rocq` at commit
`3142e4dd980f0be12f4abb636c4ae2528afc17eb`. **Their only difference is CRLF
versus LF line endings.** No definition, proof, namespace, comment or other
token differs. The retrieved external bytes match both that commit's
`manifest.json` SHA-256 pins and its Git-tree blob identifiers. The exact
comparison is in `evidence/reference-support-provenance.json`. It can be
repeated without compiling:

```sh
python3 check_reference_support.py --repo /path/to/ProveIt \
  --reference /path/to/pinned-k230-rocq
```

```sh
python3 check.py --repo /path/to/ProveIt \
  --coqc /path/to/coqc --coqchk /path/to/coqchk \
  --out /tmp/k215-command-factor-check
```

The executed compatibility build uses Coq 8.18.0 with OCaml 4.14.1. Only the
`Stdlib` import prefix is replaced by `Coq` in temporary copies. The seven
reported adapter theorems are closed under the global context. The copied
current sources, compiled-source hashes, scope and invocation results appear
in the build receipt. The repository-designated Rocq 9.1.0 lane and complete
physical-machine-to-ZFC endpoint were not rebuilt for this pilot.

The additive pilot is not offered as an automatically applicable production
patch: relocating definitions changes module dependencies and may require
qualified compatibility aliases. Compile every affected descendant, check
producer replay, and rerun the designated endpoint audit before replacing
the existing proofs.

## Deliverable files

Include `src/CommandFactor.v`, `check.py`, `check_reference_support.py`, `source_provenance.json`,
`comparison.json`, this README, and the final receipt/logs. No `.vo` objects,
toolchain binaries or redundant copied reference sources are required.
