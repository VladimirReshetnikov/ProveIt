# K215: the normalized source certificate now checked in Rocq

This package ports the 1,426-entry source certificate from the incoming Lean
normalization proposal to Rocq/Coq. It combines that certificate with the exact
K215 source definitions and the proved path codec and mirror helpers from the
incoming compact-source proposal. The new contribution is the **compiled Rocq
checker and its concrete all-register source theorem**, with a tested facade
that preserves the existing public source interface.

The exact incoming archives and hashes are recorded in `PROVENANCE.json`.
The normalized certificate, the idea of quotienting trailing zeros, the compact
path codec, and the plain mirror helper are prior work, not newly claimed here.

## Checked mathematical statement

`NormalizedSource215.p215_dagPerm_normalized` states:

```coq
forall R, rm_halts Prog215.p215 ([],R) <-> rm_halts DagPerm.dagPerm ([],R).
```

Both program definitions are byte-for-byte copies of the current repository at
`53269bcab1efc0f82d3022645bd7cf0c22d84959`. The statement is for every
natural-valued register file. It has no consistency premise. Its dependency
report and the generic checker report are closed under the global context.

This is the precise **source-correspondence layer** of the established K215
machine proof. The binary machine, boot frame, tape interpreter, numerical
calculus, and ZFC refutation predicate are unchanged. The complete 237-module
machine-to-ZFC endpoint is not rebuilt by this package.

## Actual verification result

The fresh twelve-module build completed successfully in 80.632 seconds of summed
compiler wall time, with a peak of 824,648 KiB (805.32 MiB). The separate recursive
`coqchk` of `NormalizedSource215` also completed successfully, in 521.235 seconds;
its exit code is zero. The primary driver therefore completed in 601.867 seconds
of summed proof-process wall time. The source module itself took 13.718 seconds,
including a forward VM reduction reporting 6.874 seconds.

The public facade and typed client compiled in a further 2.608 and 1.870 seconds,
respectively; both dependency reports are closed. A supplementary recursive check
of the generic checker also passed (44.191 seconds). The independent binding audit
passed for every serialized entry. There was no interrupted final recursive check.
These timings were not benchmarked against an old source proof.

`verification/compilation-summary.json` separates the twelve source compilations,
two interface compilations, and recursive checker results. The full raw receipts
and logs are retained. No complete machine-to-ZFC endpoint replay is claimed.

## What is smaller

| Representation | Entries | Uncompressed source bytes |
| --- | ---: | ---: |
| Production Rocq offset certificate | 2,240 | 1,499,170 |
| Incoming compact ordinary certificate plus path codec | 2,240 | 173,003 |
| This normalized ordinary certificate plus the same codec | 1,426 | 109,958 |

The reduction is 814 entries (36.3393%). The normalized certificate by itself
has 108,633 bytes; the retained codec has 1,325 bytes. The new generic checker
has 193 lines and 8,315 bytes; the concrete source theorem has 21 lines and
757 bytes. `metrics.json` gives the exact measurements and their scope. Source
byte counts do not measure proof-object size or checking speed. We did not run
a controlled timing comparison with either baseline.

The source proof requires one finite checker evaluation. It uses ordinary
register equality and no signed-offset layer. The converse follows from the
generic `ncheck_mirror` theorem. The shared JSON has one halt checkpoint and
1,425 decrement checkpoints, giving 2,851 branch obligations including the
initial branch.

## Why normalization is sound

For finite bit lists define `ipeq P Q` to mean that every bit agrees when the
lists are extended by false bits forever. The existing `RMEquiv.hn_ipeq` theorem
transfers a halting run of exactly N steps between equivalent pointers. Its
proof uses the interpreter's full consumed leaf path, including the zero bits
read beyond a shorter stored pointer.

The new Boolean `ibeq` checks this equivalence. `ibeq_ok` proves its soundness.
The normalized branch checker executes the original `seg` function on both
programs, checks equality of the register increment counts, and compares each
resulting pointer with its certificate representative using `ibeq`.

At each branch the inherited `seg_hn` and `seg_run` lemmas produce the actual
source and target segment endpoints. `hn_ipeq` transfers the source endpoint
to its stored representative. The corresponding target halting run transfers
back from its stored representative. The induction decreases at the next
register test, which consumes a genuine source step; zero-length segments do
not compromise this descent. The two possible test outcomes then use the
certificate's successor rows. Mirroring swaps the two pointers and the two
segment checks, so a second checker evaluation is unnecessary.

**The normalization caveat:** only trailing false bits in the mathematical
instruction-pointer representation are identified. The proof does not delete
an arbitrary suffix, operate break/continue on a shortened consumed path, or
remove physical cells from the binary Turing machine's tape frame. Those
would require separate theorems. All path arithmetic still uses the consumed
leaf path returned by the unchanged interpreter.

## Reproduce

Use Coq 8.18.0 (the checked local toolchain) or Rocq 9.1.0 (the supplied upstream
compatibility route; not tested in this session):

```sh
python3 verify_binding.py
python3 build.py
python3 complete_interface_audit.py
```

The first command independently checks that all 1,426 Rocq rows decode to the
same paths and successors as the exact shared incoming JSON. The source proof
then checks those rows directly against the program semantics; the Python
producer and its audit are not logical premises.

`build.py` compiles twelve modules from source, including every project
prerequisite of the source theorem. It separately runs recursive `coqchk` on
`NormalizedSource215`. `--skip-recursive` omits that separate checker pass;
ordinary compilation still checks proof terms in the kernel. The driver records
source hashes, compiler hashes, commands, raw output hashes, wall times and
peak resident memory in `verification/result.json`.

The second proof command compiles the adapter and a typed caller using those
freshly compiled objects. It records the imported object hashes and the two
closed reports in `verification/interface-result.json`. This is a check of the
source interface; it is not a complete endpoint rebuild.

On Coq 8.18, the private build copy of `RMEquiv.v` receives one import of the
incoming, fully proved `Compat818.v`. The original Rocq 9.1 file remains unchanged
at `deps/K230/RMEquiv.rocq91.v`. The compatibility module supplies renamed standard
library lemmas and adds no axiom. All other inherited source bytes are preserved.
Compiled `.vo` objects are disposable build products and are not part of the
deliverable.

## Integrating with the primary proof

`integration/Source215.v`, compiled as `K215F.Source215`, exports exactly:

```coq
K215F.Source215.p215_dagPerm :
  forall R, rm_halts p215 ([],R) <-> rm_halts dagPerm ([],R).
```

`integration/EndpointClient.v` independently elaborates this exact public name
and type. The production `Correct215.v` consumes this theorem. A search of the
current `coq/215` tree found no external use of the old private
`certificate_forward` or `certificate_backward` lemmas.

For integration, retain the helper modules on the Coq load path used by this
package, or consistently put them under a dedicated project namespace and
adjust their `Require` declarations. Replace the source facade with the adapter;
update the source generator and dependency manifests; then rebuild
`Correct215` and `CorrectDense215` and inspect the four endpoint assumption
reports. That final full-endpoint integration is outstanding.

The existing Lean normalized certificate can use the very same JSON. There is
no need to maintain two separately generated normalization certificates.

## Provenance

The source semantics and ordinary segment proof descend from the pinned K230
reference `3142e4dd980f0be12f4abb636c4ae2528afc17eb`. The incoming compact-source
packet extracted the exact dependencies from the retained ProveIt proof-evidence
archive. Its codec, plain mirror helper, compatibility module and licenses are
retained here. `NormalizedBisim.v` adapts the original certificate soundness proof
at the two segment endpoints by invoking `hn_ipeq`; it does not claim a new
simulation semantics. Existing notices and available license texts are retained
under `licenses/`.
