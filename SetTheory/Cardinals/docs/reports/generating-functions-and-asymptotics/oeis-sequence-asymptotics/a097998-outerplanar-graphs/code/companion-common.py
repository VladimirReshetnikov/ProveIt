"""Small deterministic, dependency-light helpers. All checks survive python -O."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent

class VerificationError(RuntimeError):
    """A mathematical identity or reproducibility check failed."""

def require(condition, message):
    if not condition:
        raise VerificationError(message)

def canonical_json(value):
    return (json.dumps(value, indent=2, sort_keys=True, ensure_ascii=True) + '\n').encode('utf-8')

def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def validate_fixtures():
    provenance = json.loads((ROOT / 'fixtures' / 'provenance.json').read_text())
    for name, record in provenance['fixtures'].items():
        require(sha256(ROOT / 'fixtures' / name) == record['sha256'], 'Fixture hash mismatch: ' + name)
    return provenance
