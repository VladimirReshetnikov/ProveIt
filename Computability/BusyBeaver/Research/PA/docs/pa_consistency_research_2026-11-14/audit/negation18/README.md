# Independent certificate for the 18-instruction negation macro

Run from any directory with standard Python 3:

```sh
python3 /path/to/negation18/verify.py
```

All inputs are bundled in `reference/`. The default receipt is `receipt.json`;
`--out PATH` chooses another output. No repository checkout, optimizer, source
compiler, or third-party Python package is imported.

## Proved source effect

For natural register values, the exact 16-instruction `node64` core maps

`(R1,R6,R7)=(t,s,y)` to `(4*(y+p(s,t)),0,0)`,

where `p(a,b)=(a+b)*(a+b+1)/2+b`. All other registers, including the encoded
stack in register 2, are preserved. Hence, with registers 6 and 7 initially zero,

`INC7; INC7; node64`

computes `N(t)=4*p(t,1)`. It contains exactly 18 primitive source instructions.
The arbitrary initial register-7 value is retained throughout the proof; the
clean-scratch restriction is used only when specializing the core to negation.

`proof.tex` is an includable TeX proof fragment with the exact primitive graph,
loop invariants, termination variants, instruction counts, and scope limits.

## What the checker does

- Parses the copied raw source independently.
- Resolves source control flow twice, using distinct algorithms: subtree
  intervals and recursive break/continue context stacks.
- Checks the exact core graph and terminating loop summaries as rational
  polynomial identities, including the arbitrary-Y contract and step counts.
- Checks all five negation spellings' primitive instruction counts.
- Follows complete source prefixes in the original machine to bind all 64
  `node64` occurrences to native state 106 and all 346 `INC7` occurrences to 82.
- Reconstructs the changed 3441-site seed source from its grammar and checks
  both CFG resolvers against that exact source.
- Locates its eight exact NEG18 blocks and independently exhausts the joint
  zero/positive abstraction. The 245112 reachable abstract pairs force both
  scratch registers to zero at every NEG18 entry.
- Runs 819 arbitrary-Y core examples and 455 full-frame comparisons of the five
  spellings as supplementary finite regression controls.

The algebraic source proof and inductive abstract invariant are universal for
their stated initial conditions. The finite concrete examples are not used to
infer those universal statements. This is an executable mathematical certificate,
not a Lean kernel theorem. It does not reprove the full TM runtime or concrete
blank startup; those are supplied separately for the 197-state seed. No machine
below 196 states is claimed here.

## Related artifacts

`seed18_emitter_audit.json` comes from the independent
`audit_negation_emitter.py` checker in the overall research archive. It restores all eight new NEG18 spellings to
the baseline separated 190-token emitter and checks the exact free expression
and stack identities. That checker supports the joint five-spelling C++ search
with `--mask-encoding five` (three bits per negation occurrence).

The associated 197-state physical compilation is distributed separately with
the overall report. Its native and dense table SHA-256 digests are respectively
`06f0d712e0933e80c2a0e82c765dbf82b4a9645a4fb6556eb50f8fc79550519d` and
`15f8b3e96d6adae76236ab0960d288b9537e39294ef1ab65f8fdd2e16dc2a9b6`.

The raw reference machine and source are upstream work by James Y.-C. Chang,
copied from ProveIt commit `906367250a7f96c923147b10df392294bced7be5`.
`PROVENANCE.json` records the archive path. The copies retain their upstream
licenses; see `LICENSE.JamesChang` and `LICENSE.ProveIt`. This independent
checker, proof, and changed-source audit are new research artifacts, not an
upstream formalization claim.
