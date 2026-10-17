# Actual dispatch and the cached-falsity NIP branch

`ArithmeticControlDispatch254.lean` connects the actual dispatch after the two reads to its four branches on arbitrary internal inputs. AC=0 reaches the actual MP entry in one logical instruction. AC=1 reaches DROP in two, clearing AC. AC=2 reaches NIP in three, clearing AC. AC=c+3 reaches AX in three, retaining c in AC. Every other file field is preserved. `opcode_cases` proves that these alternatives exhaust every element of an IΣ1 model; no standard-tag premise is used.

The high branch controls are defined by actual resolved continuations. Their exact source paths and edges follow from the existing generic `resolve_source` theorem and literal balanced-program walk/consume equations. Thus no large DFS ordinal reduction or resource-option increase is needed. The separate Python discovery and finite trace are untrusted development evidence, not premises of the Lean proof.

`nip_falsity` proves the actual NIP halt when old scratch1=0 and old cache=1. Only those two fields are constrained; the other seven, including scratch2 and AC, are arbitrary. Its seven logical instructions are increment scratch1, decrement scratch1, decrement cache, continue, test scratch1 zero, test cache zero, halt. The clock includes the literal halt instruction. `dispatch_nip_falsity` prepends the three AC=2 classifier instructions, giving the exact ten-instruction register-interpreter result.

`dispatch_nip_falsity_binary_entry` uses the existing positive-clock `halts_iff_entry` simulation. For arbitrary internal file, spare count and gap satisfying the three tested-field hypotheses, it derives existential halting of the actual represented binary machine from the corresponding prepared entry. Its binary clock is not claimed to be ten. This is a conditional prepared-entry result, with no blank-start claim.

Run2 is the first complete source/audit PASS: 14 ordered probes, 18 generic and specialized callers, standard axioms only, zero warnings. Source compilation took 3.480 s and the audit 2.386 s. The guard checks 92 exact project prerequisites, 6 external boundaries, 207 inputs and the fresh object. It builds or downloads no dependency and replays neither site certificates nor bootstrap. Run1 remains a source FAIL with three elaboration errors and zero warnings; its audit did not run. The repair replaces disequality symmetry notation by `Ne.symm` and qualifies two ambiguous `one_ne_zero` references. No statement, clock, hypothesis or resource limit changed.

The portable checker is byte-identical to its successful executed driver:

```bash
python3 Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_dispatch254.py \
  --repo /path/to/Proofs --dependency-root /path/to/built/Proofs \
  --template-evidence /path/to/Proofs/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-read-template254-verification.json \
  --output /outside/Proofs/dispatch-check
```

Add `--prepare-only` for metadata validation against existing pinned Foundation/Mathlib objects. The separate maintained-default preparation is UNBUILT and involves no proof replay or additional controls.

MP, DROP and AX are classified here; their complete branch effects are not proved by this module. NIP for cache≠1 still needs its clear/pop phase. The complete internal L2/Enum connection and whole PA consistency equivalence remain open. No machine mutation or state reduction is claimed.
