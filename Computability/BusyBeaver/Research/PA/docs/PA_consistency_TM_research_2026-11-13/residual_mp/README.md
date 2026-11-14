# Parameter-free MP via an AX comparison residual

This standalone source experiment adapts the ZFC residual-parameter idea to
PA196's three-command Shift/MP/AX interpreter. It gives a complete ordinary
command compiler, including the changed raw-word encoding and fair candidate
enumeration, and an exact 3,799-site register source. It does **not** give a
physical TM below 196 states, a runtime certificate for a new TM, or a newly
kernel-checked PA biconditional.

The new AX residual is `d = max(c - (old_d + x) - 1, 0)`. MP has no numeric
operand field. The gate and its eight theorem outputs are unchanged. The
source modification retains the opposite scratch residual from AX's second
comparison and removes the 14-site MP operand reader.

The ordinary proof is `residual_command_proof.tex` (a section suitable for
inclusion in the complete report). It includes all-number command identities,
zero-stack alias cases, explicit proof compilation, exact fresh/continuation
coding, and the full three-case comparison invariant with step counts.

## Reproduction

Use Python 3.10 or later, with assertions enabled. No third-party Python
packages are needed for these two checks.

```sh
python3 residual_source.py --output reproduced
python3 check_residual_commands.py
```

The first command reconstructs the source, checks its complete unchanged
instruction/edge projection with two CFG resolvers, and checks the local
comparison and its exact duration for 4,096 finite inputs. The output source
matches `evidence/sites.json`, SHA-256
`9aa46652ee8f11d7919700f860578d3c4c6b0ad8ec43524af79ec7d4703dff4a`.

The second command is a finite regression of the command algebra under three
safe **abstract** AX-row models. It explicitly does not evaluate the full
native AX emitter. `HOLE` means a premise-compiler interface assumed by the
structural induction. These tests supplement the written proof and do not
establish a PA theorem.

The reconstructed source has 164 distinct internal subtrees (187 including
23 distinct leaves), versus 159 internal subtrees in PA196. An inherited
conservative allocator with exact startup protection and no new labels gives
an empty assignment domain; the receipt is retained in `evidence/`. A source
instruction saving is not a physical-state saving.

## Provenance

The pinned ProveIt revision is
`38b84bce90b7d1c24c3319c0ff58d8ef92d96b21`.

`inputs/Program.lean` and `inputs/Fetch.lean` are unmodified files from James
Chang's imported PA196 package. `inputs/original.json` is the corresponding
flat source from `PA/pa196-vs-u208/source-search/allocator-screen/`.
The two unmodified source utilities in `vendor/` come from
`ZFC/k215-residual-parameter/vendor/`; inherited notices and licenses are in
`provenance/`. That ZFC experiment supplies the opposite-comparison-residual
idea. The adaptation to the distinct Shift-only PA command interface, the
new PA source splice, compiler proof and regression checker were developed
for this report. Upstream authors did not review this experiment.

`manifest.json` records all supplied file hashes as generated before this
README. Reproduction outputs are intentionally not included in its frozen
input list.
