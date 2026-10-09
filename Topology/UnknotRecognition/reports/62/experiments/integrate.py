#!/usr/bin/env python3
"""Conservative, opt-in installation of new files; no Git or network writes."""
from __future__ import annotations
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[1]


def git_blob(data: bytes) -> str:
    return hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', required=True, type=Path, help='Local ProveIt root')
    parser.add_argument('--apply', action='store_true', help='Actually copy; default is dry run')
    args = parser.parse_args()
    manifest = json.loads((ROOT / 'SOURCE_MANIFEST.json').read_text(encoding='utf-8'))
    repo = args.repo.expanduser().resolve()
    for entry in manifest['upstream_dependencies']:
        target = repo / entry['repository_path']
        if not target.is_file() or git_blob(target.read_bytes()) != entry['git_blob']:
            raise ValueError(f'Target dependency is absent or differs from the pinned source: {target}')
    destination = repo / 'Topology' / 'UnknotRecognition'
    todo: list[tuple[Path, Path]] = []
    for source in sorted((ROOT / 'overlay').rglob('*.py')):
        target = destination / source.relative_to(ROOT / 'overlay')
        if target.exists():
            if not target.is_file() or target.read_bytes() != source.read_bytes():
                raise ValueError(f'Refusing to overwrite different target: {target}')
            print(f'UNCHANGED {target}')
        else:
            todo.append((source, target))
            print(f'{"COPY" if args.apply else "WOULD COPY"} {target}')
    if args.apply:
        for source, target in todo:
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(source, target)
        print(f'Added {len(todo)} files; no existing file or Git metadata changed.')
    else:
        print(f'Dry run: {len(todo)} additions validated. Use --apply to copy.')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (OSError, ValueError) as error:
        print(f'Integration refused: {error}', file=sys.stderr)
        raise SystemExit(2)
