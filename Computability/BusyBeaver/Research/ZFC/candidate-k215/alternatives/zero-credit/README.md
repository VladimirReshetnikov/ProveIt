# ZC215: zero-credit enumeration

This packet constructs a **215-working-state, two-symbol, blank-input Turing machine** whose nonhalting is equivalent to `Con(ZFC)` by ordinary reasoning formalizable in ZFC. It provides a materially different 215-state candidate, **not a 214-state result**.

Read **ZC215.pdf** for the theorem, construction, mathematical proofs, verification boundary, additional research, and complete transition table. The editable source is **ZC215.tex**. `machine/zc215.tm` is the dense, start-0 presentation; `machine/zc215.native.tm` retains the parent's labels and starts at 74. The halt state is not included in the 215 working states.

## Main new idea

DROP has tag 0, NIP tag 1, and both consume one Cantor field. The new refill enumerates raw candidates 0,1,2,... . Replacing any NIP occurrence by DROP gives a unique, strictly smaller candidate containing the corresponding DROP. This is an injection from all NIPs in any command prefix into DROPs in earlier completed candidates. Therefore `#DROP >= #NIP` at every prefix—even if AX is assigned zero stack credit. The entire initialized stack can remain an arbitrary opaque tail. This proof is in `proofs/tag_lowering_credit.md`; the older diagonal proof is retained independently.

## Exact construction

Parent: `candidate-k215/alternatives/commands120`, ProveIt commit `29e2cc4c557c04d3358e41e566bd7c582844ff4e`.

| Item | Parent | ZC215 |
|---|---|---|
| Native start | 0 | 74 |
| Native row 8/1 | 1 R 13 | 1 R 103 |
| Native row 198/0 | 1 L 40 | 0 L 40 |

In the source, replace subtree `H0=(CD6,CC2)` at path `0111` with `(H0,CB1)`. All command bodies are unchanged. Frozen parent data and a byte-exact deterministic reconstructor are included.

## Reproduction

Use Python 3 with assertions enabled. All main verification dependencies are included and use the standard library. Choose fresh output directories:

```sh
python3 -B verify.py --out /tmp/zc215-check
python3 -B verify.py --runtime --out /tmp/zc215-full-check
```

The first checks the manifest (when present), exact table/source reconstruction, every transported source edge, literal blank startup, saved-runtime coverage/positivity, and comparison with the 67 frozen prior tables. It also runs the finite credit corroboration. The second freshly rederives all 6,177 arbitrary-value guarded runtime obligations using literal steps, unary induction, and structural finite-list induction, and compares every case to the released census. It can take several minutes. These are executable mathematical certificates, not a new proof-assistant kernel endpoint.

Build the report with a TeX distribution containing the standard packages used by `ZC215.tex`:

```sh
bash build_report.sh
```

## Evidence

- 215 working states; all 215 are reachable in the transition graph.
- 430 rows, all covered by the runtime proof.
- 202 source DAG nodes; 4,752 primitive occurrences; 6,177 guarded cases.
- Fresh runtime: 1,698,860 symbolic rule applications; minimum affine duration constant 9, all coefficients nonnegative.
- Exact blank prefix: 117,004 transitions to native dispatcher 84, head -4, header 80, gap 20.
- Logical registers `(N,T,W,A,D,H,X,Y,L)=(1,0,5,0,0,0,0,0,0)`; 67 spare blocks; exactly 86 one-cells; complete zero exterior.
- No rooted state-renaming or global-reflection equality to any of 67 parseable 215-state `.tm` tables in the pinned checkout, representing 16 rooted graph classes. Historical archive members were not part of that finite corpus.

`evidence/` contains machine-readable receipts, the complete case census, startup frame, and frozen comparison tables. `MANIFEST.json` pins every delivered file except itself.

## Additional research and its status

- `research/seven_shift_synchronizer.md`: a new cofinal forced-hit theorem for an **abstract** scratch-biased, skipped-candidate scheduler. A separate credit proof and finite-base checker are included. This does not validate its archived physical implementation.
- `research/rejected_scratch_transfer/`: the historical table and source whose inserted CC3 return reaches dispatch rather than the scheduler root. `research/replay_rejected_scratch.py` reproduces a 23,142-step binary false halt from a valid all-truth MP frame. See `scratch_transfer_audit.json`. This is a rejected research table, not the main candidate.
- `research/transfer_gq.sites.json`: a 201-subtree source using the equiconsistent fresh binder `4P(a,b)+2`. Logical calibration transfers; physical allocation is unresolved. No additional binary machine is claimed.
- `research/binder_variants/`: representative sources for four fresh-binder families. The sum binder `a+b+1` reduces the word to 4,729 primitive occurrences but has 203 distinct subtrees, illustrating the difference between short code and shared binary allocation. `binder_batch_summary.json` records all 16 bounded initial allocation attempts and their limited scope.

## Scope and provenance

The ordinary proof inherits the accepted numerical-calculus/ZFC consistency calibration and strong command compiler. The parent primary K215 has compiled Lean/Rocq endpoints; **this new table does not yet have its own compiled Lean/Rocq endpoint**. No unconditional nonhalting, internal-PA endpoint, state lower bound, or global discovery-priority claim is made.

References preserve their original status, machine-specific startup figures, and relative links. They are historical dependencies, not newly written claims about ZC215. Consult `NOTICE.md` and `licenses/` for inherited attribution and terms. No full upstream checkout is needed for the released computational checks.
