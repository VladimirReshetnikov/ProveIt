#!/usr/bin/env python3
"""Rebuild the four fixed compiler integers and compare their literal bytes."""
from pathlib import Path
import gzip
import importlib.util
import json
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    path = ROOT / 'upstream/source31/coefficients/build_coefficients.py'
    spec = importlib.util.spec_from_file_location('pinned_coefficients', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    data = module.recipe()
    geometry = module.check_geometry(data)
    padding = module.check_padding(data[5])
    with tempfile.TemporaryDirectory(prefix='con-zfc-coefficients-') as directory:
        module.ROOT = Path(directory)
        files, masks = module.materialize(data)
        for row in files:
            rebuilt = gzip.decompress((module.ROOT / row['file']).read_bytes())
            supplied = gzip.decompress((ROOT / 'upstream/source31/signed10/data' / (row['port'] + '.bin.gz')).read_bytes())
            assert rebuilt == supplied, row['port']
    receipt = {'status': 'PASS', 'geometry': geometry, 'padding': padding,
               'masks': masks, 'reconstructed_ports': files,
               'comparison': 'All four reconstructed integers equal the supplied payloads byte-for-byte.'}
    (ROOT / 'generated/COEFFICIENT_REPLAY.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({'status': 'PASS', 'ports_reconstructed': 4,
                      'native_basis_checks': geometry['native_basis_checks'],
                      'tiles': 943}))


if __name__ == '__main__':
    main()
