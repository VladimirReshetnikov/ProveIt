"""Small independent literal-table utilities for the scoped search replay."""
from pathlib import Path
import hashlib
import json

BASE = Path(__file__).resolve().parent


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read_json(path):
    return json.loads(Path(path).read_text())


def read_table(path):
    rows = {}
    for line in Path(path).read_text().splitlines():
        line = line.strip()
        if not line or line.startswith(('#', '//', ';')):
            continue
        q, b, w, d, n = line.split()
        q, b, w, n = map(int, (q, b, w, n))
        assert q >= 0 and n >= 0
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in rows
        rows[q, b] = (w, 1 if d == 'R' else -1, n)
    states = {q for q, _ in rows}
    assert states and set(rows) == {(q, b) for q in states for b in (0, 1)}
    halts = {n for _, _, n in rows.values()} - states
    assert len(halts) == 1
    return rows, states, next(iter(halts))


def read_contexts(path, radius):
    pairs = []
    for line in Path(path).read_text().splitlines():
        if not line.strip():
            continue
        q, p = map(int, line.split())
        assert q >= 0 and 0 <= p < (1 << (2 * radius + 1))
        pairs.append((q, p))
    assert len(pairs) == len(set(pairs))
    return set(pairs)


def write_contexts(path, pairs):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(''.join(f'{q} {p}\n' for q, p in sorted(pairs)))


def write_json(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')
