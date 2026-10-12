"""Copy only the pinned transitive incoming dependencies for native reproduction.

The source modules remain byte-identical. Generated package shims avoid the
unrelated recognizer imports performed by the public fastunknot facade.
"""

import argparse
import hashlib
import json
from pathlib import Path
import shutil


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--runtime', required=True)
    parser.add_argument('--output', required=True)
    parser.add_argument('--manifest', default=str(
        Path(__file__).resolve().parents[1] / 'evidence' / 'upstream_dependencies.json'))
    args = parser.parse_args()
    runtime, output = Path(args.runtime), Path(args.output)
    manifest = json.loads(Path(args.manifest).read_text())
    for item in manifest['files'] + manifest.get('extra_files', []):
        source = runtime / item['path']
        if hashlib.sha256(source.read_bytes()).hexdigest() != item['sha256']:
            raise RuntimeError('upstream file does not match pinned hash: ' + item['path'])
        target = output / item['path']
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    for package in ('fastunknot', 'normal_orbit_research', 'marked_parallelity_research'):
        (output / package / '__init__.py').write_text(
            '"""Generated reproduction namespace; pinned source modules are unchanged."""\n')
    print('Copied', len(manifest['files']), 'pinned source modules to', output)


if __name__ == '__main__':
    main()
