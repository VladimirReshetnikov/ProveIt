# Exact prefix250 instruction composition

`InstructionPrefix250.lean` composes an accepted binary site with the complete dispatch frame for the exact shared-carry 250-state table. Every successful logical step has a strictly positive binary duration. The result retains the logical successor, zero logical-register tail, complete infinite tape and a nonempty spare suffix.

Increment appends one value-one spare. Both decrement branches preserve the suffix; positive decrement adds one cell to the target header distance, in addition to any PC-overflow contribution. Break and continue preserve the register file. The separate halt theorem turns an accepted halt site into a positive-time binary halt. These results quantify arbitrary register values and gap parameters and use the checked whole-tape frame adapters.

The theorem is conditional on the particular site's Boolean check succeeding. It neither asserts all 8,391 checks succeed nor connects the whole program's reachable runs or blank startup to the frame. Runtime transport, complete site coverage, the exact 250 consistency endpoint and the user's PA-internal equivalence remain separate obligations.

The root's sole attempt passed the 119-line source and 43-line audit, with seven named axiom probes, seven typed callers and no warnings. The two elementary increment-path length lemmas use only `propext`; the other five probes use `propext` and `Quot.sound`. Source compilation took 0.725 seconds and the audit 0.431 seconds in that run. The fresh object was recorded before the audit and remained unchanged afterward.

Successful record SHA256: `109098d924c927d9894a4e22a3ce816e8eacf87be85ddde670e0716181d1239d`.
Source SHA256: `29bb8760369dbada6df56c5d0597392d17e36407aaffc63eab2d14e9904f1936`.
Audit SHA256: `68653f063b0b2890c5865759f53b8072dd7da17a3634156019c49d2bf9a82942`.
Fresh object SHA256: `ea60221fed4b77ee97f4ff84767a332976d028547c031caa99882dde4edacf0e`.

The guard pins the successful Frame record, verifies 22 exact project providers and all 63 current inputs, and checks the project import closure and first-provider resolution. Init and Omega are the only toolchain boundaries; there is no external project-library boundary. Inherited 252/253 modules supply generic layout, list and tape infrastructure, without assuming those tables execute like this machine.

Only this source and audit compile, serially with one thread, 4096 MiB and a shared 120-second budget under default elaboration limits. Maintained publication changes only the two source/audit default paths. The following preparation checks the pinned sources and existing provider objects without compiling or querying a compiler version:

```sh
python3 Computability/BusyBeaver/Research/ZFC/check_prefix250_instruction.py \
  --repo "$PWD" \
  --frame-evidence Computability/BusyBeaver/Research/ZFC/results/prefix250-frame-verification.json \
  --output /tmp/prefix250-instruction-fresh-preparation --prepare-only
```

Provider objects must already be available; the command performs no dependency build. The complete sole-attempt source, audit, guard, result and raw output are retained in history. The author reviewed the final evidence, and root independently reviewed and executed the proof. A separate independent child source/interface review is embedded with its original pre-build scope; it is not presented as a second execution or final evidence audit.

The machine, instruction semantics, verification framework and compiler retain Mira-Cult, Jeff Ketchersid and Andrew James Wade's attribution. The shared-carry construction is preserved from incoming source 58 (`126d12e470`), with the generic permutation-frame work attributed to the ProveIt development.
