"""Shared experiment configuration and complete source/dependency pins."""
from boundary_transversal_research.common import source_hashes as boundary_hashes
from hashlib import sha256
import json
from pathlib import Path

from euler_transversal_research.common import (
    ROOT, DIAGRAM_CONFIG, STRATEGIES, lower_fixtures,
    source_hashes as inherited_hashes)

PACKAGE = Path(__file__).resolve().parent
POLICIES = ('subsets', 'conflicts')
SEED = 2026101219


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def configs():
    return {policy: dict(DIAGRAM_CONFIG, transversal_candidate_policy=policy)
            for policy in POLICIES}


def source_hashes():
    result = inherited_hashes()
    for name, expected in boundary_hashes().items():
        assert name not in result or result[name] == expected
        result[name] = expected
    for path in sorted(PACKAGE.rglob('*')):
        if path.is_file() and path.suffix in ('.py', '.md', '.json'):
            result[str(path.relative_to(ROOT))] = sha256(path.read_bytes()).hexdigest()
    return dict(sorted(result.items()))
