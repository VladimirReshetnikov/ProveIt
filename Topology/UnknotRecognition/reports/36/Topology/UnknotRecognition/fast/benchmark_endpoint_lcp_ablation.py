"""Reproduce the archived full-LCP endpoint variant in the paired harness.

Run from fast/:
python benchmark_endpoint_lcp_ablation.py --output results/endpoint_ap_lcp_ablation_20261008.json
All benchmark_compressed_endpoint.py CLI arguments are accepted.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
from unittest.mock import patch

import benchmark_compressed_endpoint as harness
from fastunknot import compressed_lcs


def main():
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--output', type=Path)
    args, _ = parser.parse_known_args()
    path = harness.ROOT/'endpoint_research/lcp_endpoint_variant.py'
    spec = importlib.util.spec_from_file_location('fastunknot._endpoint_lcp_ablation', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    with patch.object(compressed_lcs, 'endpoint_overlaps', module.endpoint_overlaps):
        harness.main()
    result = json.loads(args.output.read_text())
    result['variant'] = 'LCP clipping ablation before candidate-rank refinement'
    result['ablation_scope'] = 'Current integration hook calls the archived exact LCP clipping implementation'
    for source in (path, Path(__file__)):
        result['source_sha256'][str(source.relative_to(harness.ROOT))] = hashlib.sha256(source.read_bytes()).hexdigest()
    args.output.write_text(json.dumps(result, indent=2)+'\n')


if __name__ == '__main__':
    main()
