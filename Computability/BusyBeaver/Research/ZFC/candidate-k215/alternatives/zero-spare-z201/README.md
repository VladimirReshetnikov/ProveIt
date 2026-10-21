# Two new zero-spare command compositions at 215 states

This packet gives two materially different **215-working-state, two-symbol, blank-tape** consistency machines. It does not give a certified 214-state machine. Read report.pdf or its editable report.tex and sections/ first.

Both retain the accepted numerical-calculus calibration to ZFC. Their new contribution is the combination of an existing command encoding with the zero-spare backend and a new, rigorously calibrated blank initialization. No priority is claimed for the inherited command languages, zero-spare idea, compiler, credit theorem, or symbolic checker. These are ordinary mathematical proofs formalizable in ZFC, not new Lean/Rocq kernel endpoints.

## Primary: NIP/MP/DROP with finite cleanup of unsafe data

- Machine: primary/z201.tm (canonical start0, states0–214, halt215), or primary/z201.native.tm (native start74, halt254).
- Source: primary/sites.json; 202 DAG nodes, 4,751 occurrences.
- Full runtime: all6,176 guarded cases pass, 1,697,188 symbolic rules, all430 rows covered.
- Safe blank endpoint:570,263 transitions, genuine source root with (N,T,W,A,D,H,X,Y,L)=(5,0,0,0,1,0,0,0,0).

The earlier118,411-step frame is explicitly unsafe. Its next four commands NIP,NIP,DROP,MP(1) remove the unsafe data without halting. The proof begins its theoremhood invariant only at the later safe root. It uses arbitrary-counter calibration, not a borrowed protected-tail bound.

## Secondary: transfer-pop with an unsafe suffix kept out of reach

- Machine: secondary/candidate.tm (canonical start0, states0–214, halt215), or secondary/candidate.native.tm (native start74, halt254).
- Source: secondary/sites.json;201 DAG nodes,4,775 occurrences.
- Full runtime: all6,209 guarded cases pass,1,611,489 symbolic rules, all430 rows covered.
- Blank endpoint:73,172 transitions, an exact interior AX frame at source ordinal119.

A separately checked177-primitive source prefix identifies that frame. The remaining AX produces eight theorem heads above the unsafe suffix J=171, which contains Q_1(1)=18. The infinite schedule has conservative debt3, so at least five theorem heads remain above that suffix. Neither the dirty incoming cache nor its generalization is assumed to be a theorem. The actual composite transfer tests both top and cache for falsity; both guards and its internal pops are covered.

## Reproduction

Python3.10 or later, standard library only, no network or solver. From any directory:

    python3 -B /path/to/packet/verify.py

This checks the exact aggregate manifest and both standalone subpackets, including literal reconstructions, complete blank traces, source checks, certificate inventories, graph distinctions, and read-only behavior. It does not rederive every symbolic proof.

For fresh unbounded derivations:

    python3 -B /path/to/packet/verify.py --runtime --work /tmp/new-zero-spare-replay

Use a nonexistent output directory outside this packet. --primary-runtime and --secondary-runtime select one full derivation instead. Each complete symbolic replay can take several minutes. The verifier explicitly rejects Python optimization rather than skipping assertions.

The standalone primary/README.md and secondary/README.md describe their individual entry points. Their pinned parent files are preserved as inherited dependencies. A rerun of the same mathematical checker is not represented as an independently designed proof algorithm; separately implemented finite parsers, source traces, and tape replays have their exact scopes recorded.

## Files and proof boundaries

- report.pdf, report.tex, sections/: detailed mathematical report and complete canonical transition tables for both machines.
- primary/: exact first construction, recipes, finite cleanup proof, source, native/dense tables, complete runtime evidence, and independent review.
- secondary/: exact second construction, dirty-AX/protected-tail proof, source, native/dense tables, full runtime evidence, and independent review.
- verify.py, rebuild_manifest.py, manifest.json: aggregate reproducibility and exact integrity checking.
- evidence/: final portable replay and PDF/table quality checks.

The numerical-calculus/ZFC bridge is explicitly inherited, and the exact source compilers and scheduler theorems are supplied with attribution in the subpackets. State count excludes halt. No nonblank external setup, unconditional nonhalting claim, or state-minimality result is asserted. The initialized214 research failures are not presented as candidates.
