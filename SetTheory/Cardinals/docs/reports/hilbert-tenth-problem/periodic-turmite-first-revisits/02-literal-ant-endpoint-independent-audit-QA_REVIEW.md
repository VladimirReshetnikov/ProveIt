# External endpoint packet QA

Verdict: PASS for the frozen endpoint component, conditional on its stated parent-history contract. No blocking defect found. No release file was modified or uploaded.

## Authentication and isolation

- ZIP: 46,289 bytes; SHA-256 `f14b03ad1486f637bbb763b1ab6b061ae6f06068ef9ae972cb559dcc1d55b1ad`
- Manifest SHA-256: `31fb4d8feedae85446fdf6cf480ec1e5ed6a2ffd3ccb16cb15887503093e5112`
- All 23 manifest entries match sizes and hashes. The archive contains exactly those 23 files plus the manifest. Archive members are unique, unencrypted regular files with safe relative paths; all archive and frozen-tree bytes agree.
- All five Python source files were read before execution. Their imports are standard-library modules plus the authenticated local `audit_endpoint.py`. No upstream file, program, or arithmetic schedule was run.
- Execution was restricted to an independently extracted authenticated tree. The replay driver made its own additional generation copy. The frozen root was never an execution target.
- Recorded pre/post snapshots show original ZIP and release contents, modes, and nanosecond mtimes unchanged. Read-induced access-time changes are outside this preservation assertion.

## Replays and independent checks

- Ordinary Python 3.12.14 replay passed all four commands and reproduced all six source DAGs and four receipts byte-for-byte.
- The newly produced replay receipt and driver stdout also match the frozen versions byte-for-byte.
- Eight optimized-mode probes rejected as required: `-O`, `-OO`, `PYTHONOPTIMIZE=1`, and `PYTHONOPTIMIZE=2` for each of `replay_all.py` and `verify_literal_sources.py`.
- The three preserved generators lack explicit optimization guards. They are unsupported under optimization and were never run optimized. No optimized generator pass is claimed.
- A separate external checker imported no packet modules. It parsed all six JSON DAGs, verified exact literal/fixed/variable interfaces, every reference and opcode, acyclicity, all-gate liveness, all four target powers, section boundaries and ledgers, and exact complete residual polynomials in the formal integer ring with base Z.
- The external checker independently proves each degree survives specialization Z=3 by giving a nonzero modular leading-coefficient certificate. It does not materialize giant powers or coefficients.
- The packet's supporting finite regressions passed: 17,280 candidate endpoints, 80 folded positivity cases, and 192 five-witness correspondence cases. These support, rather than replace, the integer proof.

## Algebra and counts

The three-witness folded source has prescribed fixed K,C,D, with D=C-1. It has 42 operations = 37M+5A, three positive witnesses and three equations. Its strict literal-1/3 source has 101 operations = 94M+7A. The exact endpoint degree vector is (1,605950,1).

The five-witness source has 42 operations = 37M+5A with prescribed K,C,D, or 101 operations = 94M+7A from literal 1 and 3. It has five positive witnesses and five equations, with degree vector (1,576001,1,29950,1). Its first two equations force U=1+C(Uq-1) and V=1+(W^v-1)(Vq-1). Consequently Uq=HxPlus and Vq=HyPlus give a bijection with the three-witness solutions, including both zero underlying quotients. The five-witness form is therefore a valid lower-maximum-degree alternative at the same displayed source cost.

The earlier conventional fixed-numeral source remains 43 = 37M+6A. These are exact costs of the displayed sources, not optimality claims. Gate outputs are computed expressions; they are not new quantified witnesses. Equalities are free in the component ledger. Multiplication by fixed constants remains charged.

Under W=3^w and FinalHead=3^j, positivity forces U and V to be powers of 3. The divisor criterion (3^d-1)|(3^k-1) iff d|k, including k=0, recovers the required horizontal and vertical exponent periods. BoundCol>0 prevents row carry; FinalHead<Q supplies the row bound. The even periods and odd/even residues select a white square, where FinalSignPlus=1 gives incoming east under the parent convention. The normalization X=y-75, Y=288650-x gives the stated canonical residues and maps initial E to N and accepting S to E.

## Scope and remaining obligations

The endpoint theorem remains conditional on the parent history's odd w>=3, even h>=2, W=3^w, Q=W^h, FinalHead=3^j<Q, 0<=j<wh, canonical bounded board, and heading/sign semantics. This review neither executes nor re-proves the inherited 174-operation theorem or the separately frozen literal-interface exclusivity theorem. Those are explicit premises.

There is no standalone arbitrary-integer endpoint interpretation, combined 174 total, universal arithmetic certificate, raw-input loader, or final single-polynomial claim. Initial-board encoding, translation/padding, input dilation, periodic-background arithmetic, and polynomial combination remain separate. K,C,D must retain their prescribed values; treating them as unconstrained witnesses invalidates the intended endpoint relation.

## Evidence

- `authentication.json`: archive, manifest, file sizes, hashes, and safe extraction checks
- `executable_boundary.json`: source hashes and imported modules
- `fresh_replay.json`, `normal_replay.stdout.log`, `normal_replay.stderr.log`: normal replay
- `optimization_guards.json`: all eight guarded rejection probes
- `independent_dag_check.py`, `independent_dag_check.json`: external data-only interpreter and exact certificates
- `frozen_before.json`, `frozen_after.json`: preservation snapshots
- `external_qa_summary.json`: compact replay summary
- `run_external_qa.py`: external authentication and replay orchestration source
