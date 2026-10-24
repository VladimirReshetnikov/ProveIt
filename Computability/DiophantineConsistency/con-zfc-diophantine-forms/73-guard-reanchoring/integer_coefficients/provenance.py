"""Byte identity and complete-tuple binding helpers; Python standard library."""
from pathlib import Path
import hashlib
import importlib.util
import json

ROOT = Path(__file__).resolve().parent
BACKEND = 'mixed-parity-unrounded-1064921'
PORT_FILES = {'beta':'beta', 'K0':'K', 'MC':'MC', 'MF':'MF_source'}


def require(value, label):
    if not value:
        raise ValueError(label)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def verify_sources():
    records = json.loads((ROOT/'SOURCE_PINS.json').read_text())['files']
    for record in records:
        raw = (ROOT/record['file']).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(blob == record['git_blob_sha1'], 'source Git blob: '+record['file'])
        require(sha256(raw) == record['sha256'], 'source SHA256: '+record['file'])
        require(len(raw) == record['bytes'], 'source length: '+record['file'])
    return len(records)


def load_source34(module_name, filename):
    path = ROOT/'upstream'/'source34'/filename
    spec = importlib.util.spec_from_file_location(module_name, path)
    require(spec is not None and spec.loader is not None, 'module loader')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def tuple_digest(raw_values):
    """Canonical names and length-delimited raw integers prevent port mixing."""
    h = hashlib.sha256(b'ProveIt fixed Diophantine coefficient tuple v1\0')
    for port in ('beta', 'K0', 'MC', 'MF'):
        raw = raw_values[PORT_FILES[port]]
        h.update(port.encode('ascii')+b'\0')
        h.update(len(raw).to_bytes(8, 'big'))
        h.update(raw)
    return h.hexdigest()


def make_binding(raw_values, inherited):
    return {
        'backend': BACKEND,
        'source_commit': '9cca523d9f27ad39d52993f4065cbd7e58f8bdd4',
        'fixed_numerals': ['beta', 'K0', 'MC', 'MF'],
        'ports': {port: 'payloads/'+name+'.bin.gz' for port,name in PORT_FILES.items()},
        'raw_ports': {port: 'payloads/'+name+'.bin' for port,name in PORT_FILES.items()},
        'format': 'gzip of minimal unsigned little-endian integer bytes',
        'beta': '2^1064921-1',
        'mask_convention': 'MF=MF_native+beta; the supplied MF is already shifted.',
        'policy': 'Use this complete four-port tuple together; no cross-backend port substitutions.',
        'tuple_sha256_scheme': 'SHA256(prefix || each port name || NUL || 8-byte big-endian raw length || minimal unsigned little-endian bytes), in beta,K0,MC,MF order; prefix is ProveIt fixed Diophantine coefficient tuple v1 followed by NUL.',
        'tuple_sha256': tuple_digest(raw_values),
        'payloads': inherited['payloads'],
        'inherited_manifest': 'upstream/source34/PAYLOAD_BINDING.json',
        'coefficient_proof': 'proofs/COEFFICIENT_PROOF.md',
        'scope': 'Exact finite coefficient materialization and full inherited compiler adapter; no new end-to-end formal certificate.'
    }


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')
