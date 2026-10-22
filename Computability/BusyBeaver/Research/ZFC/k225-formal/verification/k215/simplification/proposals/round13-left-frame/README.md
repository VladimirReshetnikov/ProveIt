# Further simplifying Rocq and Lean proofs

Pinned main: 6d9800d1ca67c52db0eb6e1c65df7b5cab9cdb95.
Baseline: 57541fe0cfe3af62b4cb58747d8d1d7c16b338d5.

Read report.pdf or edit report.tex. The new recommendation is to keep the existing runtime executor and prove one guarded left-frame lifting lemma, then use the existing terminal Home theorem. The finite diagnostic yields 35 templates for 1,422 control guards and a candidate 4,789 expensive obligations; all 6,176 source-coverage instances remain. These new proof contracts are NOT kernel checked, and no existing endpoint family has been replaced.

## Offline replay

Use Python 3.8 or newer, with assertions enabled, and a work directory that does not exist:

    python -I -B verify.py --work /tmp/round13-check

The verifier checks exact package membership and hashes, copies components outside the packet, and executes only eight explicitly listed owned scripts. It does not fetch anything, execute received scripts, run proof assistants or mutate the package. Its results and logs are written to the work directory. Reproduction was performed again after safe extraction of the release ZIP.

## Contents

- review/: Current accepted-source maps, 198 current source snapshots, the full 199-source prior map and its ten changed/removed snapshots (the other 189 prior sources are reconstructed from identical current bytes after exact prior-hash checks), phase-13/14 archived evidence, exact current-byte and scoped-delta replay, recent-commit/proposal status review. Receipt evidence is not local compilation. Archived scripts are inert evidence and are not used by verify.py.
- runtime/: 35-template discovery, explicit native/formal label binding, source routing, finite checks, full traces, negative tests and an uncompiled Lean frame-contract sketch. Use FORMAL_TEMPLATES.json, not unrenamed native traces, when integrating into Lean.
- structural/: Proposed shared EnumStack module, exact Lean extraction patch, synchronized Rocq producer/generated patch, source audits and uncompiled compatibility client. The Rocq change is nine unique proof lines, not eighteen independent proof lines.
- calculus/: Optional formula-local equality-capability patch, three proposed sources and uncompiled typed audit clients. Net production saving is five lines; it preserves existing public fragment/freshness guards.
- licenses/: Retained source notices and license texts from the preceding source packet.
- MANIFEST.json: SHA256 and size for every other packaged file.

## Verification boundary

No Lean or Rocq compiler was available. Proposed proof bodies, typed clients, wrapper compatibility, universal framing and endpoint integration remain to be compiled. Finite tests do not establish quantified semantics. Semantic reachability does not imply the existing fixed-fuel Boolean checkEdge succeeds; integration needs the separately checked semantic interface and endpoint adapter. No machine change, smaller state count, reduced endpoint axiom profile, fresh cross-language endpoint receipt or build-speed gain is claimed.
