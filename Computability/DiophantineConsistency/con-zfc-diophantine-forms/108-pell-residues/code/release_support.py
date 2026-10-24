"""Shared file handling for deterministic offline reproduction.

Only the bundled, hash-pinned dependency archive is extracted. No network,
credentials, external repository, or mathematical search is used.
"""
from contextlib import contextmanager
from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile
import hashlib
import json
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(Path(path).read_text())


def canonical(value):
    return (json.dumps(value, sort_keys=True, separators=(',', ':'))+'\n').encode()


def command(script, *arguments):
    opts = ['-O'] if not __debug__ else []
    proc = subprocess.run([sys.executable, *opts, str(script), *map(str, arguments)],
                          capture_output=True, text=True, check=False)
    if proc.returncode:
        raise RuntimeError(f'{Path(script).name} failed:\n{proc.stdout}\n{proc.stderr}')
    return json.loads(proc.stdout)


@contextmanager
def parent_workspace():
    pin = read(ROOT/'provenance/SNAPSHOT.json')
    archive = ROOT/'inputs'/pin['input_archive']
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == pin['input_archive_sha256'],
            'Pinned parent archive has changed')
    with TemporaryDirectory(prefix='conzfc-pell-residues-') as tmp:
        destination = Path(tmp)
        with ZipFile(archive) as zip_file:
            for item in zip_file.infolist():
                member = Path(item.filename)
                require(not member.is_absolute() and '..' not in member.parts,
                        'Unsafe archive member')
            zip_file.extractall(destination)
        parent = destination/'ConZFC_407_888_Quartics'
        require((parent/'code/build_projected.py').is_file(), 'Wrong parent layout')
        for name in ('modular_binomial.py', 'build_modular.py', 'check_modular_structure.py'):
            shutil.copy2(ROOT/'code'/name, parent/'code'/name)
        yield parent


def compare_json(actual, expected):
    require(read(actual) == read(expected), f'Rebuilt JSON differs: {expected}')


def manifest_check():
    manifest = ROOT/'SHA256SUMS'
    if not manifest.exists():
        return {'status':'not_present_during_authoring'}
    count = 0
    for line in manifest.read_text().splitlines():
        expected, name = line.split('  ', 1)
        require(hashlib.sha256((ROOT/name).read_bytes()).hexdigest() == expected,
                'Digest mismatch: '+name)
        count += 1
    return {'status':'pass', 'files':count}
