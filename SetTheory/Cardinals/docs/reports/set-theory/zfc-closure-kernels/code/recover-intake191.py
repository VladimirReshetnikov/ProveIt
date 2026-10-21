"""Recover batch 191 in original layouts outside the repository; no execution."""
from pathlib import Path, PurePosixPath
import argparse
import io
import json
import stat
import subprocess
import zipfile

ARCHIVES = [('7071e5041e', name) for name in (
    'K217_Search_Round_2026-10-20.zip',
    'K218_Dominated_Rho8_2026-10-20.zip',
    'ZFC_217_Investigation_2026-10-20.zip',
    'zfc-217-state-search.zip',
)]


def extract(data, output):
    with zipfile.ZipFile(io.BytesIO(data)) as archive:
        entries = archive.infolist()
        names = [entry.filename for entry in entries]
        if len(names) != len(set(names)):
            raise ValueError('Duplicate ZIP member')
        for entry in entries:
            path = PurePosixPath(entry.filename)
            if path.is_absolute() or '..' in path.parts or stat.S_ISLNK(entry.external_attr >> 16):
                raise ValueError('Unsafe ZIP member: ' + entry.filename)
            if entry.is_dir():
                continue
            target = output.joinpath(*path.parts)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(archive.read(entry))
        return sum(not entry.is_dir() for entry in entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='New directory outside the repository')
    args = parser.parse_args()
    repo = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    output = args.output.resolve()
    if output == repo or repo in output.parents:
        parser.error('Use an output directory outside the repository')
    output.mkdir(parents=True, exist_ok=False)
    receipt = []
    for commit, filename in ARCHIVES:
        data = subprocess.check_output(['git', 'show', commit + ':docs/incoming/' + filename], cwd=repo)
        archive_output = output / Path(filename).stem
        archive_output.mkdir()
        receipt.append(dict(commit=commit, archive=filename, directory=str(archive_output),
                            members=extract(data, archive_output)))
    (output / 'recovery.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))


if __name__ == '__main__':
    main()
