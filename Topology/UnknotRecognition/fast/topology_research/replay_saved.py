"""Replay all retained benchmark certificates after reading their JSON files.

This is a verification pass, not a second performance benchmark. It checks
the saved proof hash against every associated measured/warmup sample before
calling the independent source-bound verifier. Large integers remain encoded
as hexadecimal JSON strings until the ordinary verifier decodes them.
"""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys
import time

FAST = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(FAST))

from fastunknot.normal_topology_verify import verify_normal_topology_spectrum
from topology_research.benchmark import _snapshot, verify_coordinates_reference


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--benchmark', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    benchmark = args.benchmark.resolve()
    data = json.loads(benchmark.read_text())
    proof_root = benchmark.parent / (benchmark.stem + '-proofs')
    before = _snapshot()
    if before != data['source_hashes_after'] or not data['sources_unchanged']:
        raise RuntimeError('source identity differs from the completed benchmark')
    report = dict(schema='normal-topology-saved-proof-replay-v1',
        started_utc=datetime.now(timezone.utc).isoformat(),
        baseline_commit=data['baseline_commit'],
        benchmark_sha256=hashlib.sha256(benchmark.read_bytes()).hexdigest(),
        driver_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        source_hashes_before=before, proofs=[])
    started = time.perf_counter()
    for case in data['cases']:
        source = case['source']
        for arm in data['arms']:
            path = proof_root / source['name'] / f'{arm}.json'
            raw = path.read_bytes()
            canonical = raw[:-1] if raw.endswith(b'\n') else raw
            digest = hashlib.sha256(canonical).hexdigest()
            expected = {sample['samples'][arm]['certificate_sha256']
                        for sample in [case['warmup'], *case['rounds']]}
            matches = expected == {digest}
            if not matches:
                raise RuntimeError(f'{path}: saved proof differs from recorded samples')
            proof = json.loads(raw)
            if arm == 'coordinates_reference':
                valid = verify_coordinates_reference(source['triangulation'],
                    source['coordinates'], proof, lambda: None)
            else:
                valid = verify_normal_topology_spectrum(source['triangulation'],
                    source['coordinates'], proof)
            report['proofs'].append(dict(case=source['name'], arm=arm,
                certificate_sha256=digest, recorded_hashes_match=matches,
                certificate_bytes=len(canonical), valid=valid))
            if not valid:
                raise RuntimeError(f'{path}: saved certificate failed replay')
    after = _snapshot()
    report.update(finished_utc=datetime.now(timezone.utc).isoformat(),
        elapsed_seconds=time.perf_counter() - started,
        source_hashes_after=after, sources_unchanged=(before == after),
        attempted=len(report['proofs']), passed=sum(row['valid'] for row in report['proofs']))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(report, sort_keys=True, separators=(',', ':')) + '\n')
    if before != after:
        raise RuntimeError('sources changed during saved-proof replay')
    print(json.dumps({key: report[key] for key in
                      ('attempted', 'passed', 'elapsed_seconds', 'sources_unchanged')}))


if __name__ == '__main__':
    main()
