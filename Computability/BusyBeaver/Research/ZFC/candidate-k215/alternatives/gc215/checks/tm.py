"""Small literal table reader/writer. All labels are integers; moves are L/R."""
import hashlib


def read_table(raw):
    rows, starts = {}, []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:])); continue
        if not line or line.startswith('#'):
            continue
        q, b, w, d, z = line.split()
        q, b, w, z = map(int, (q, b, w, z))
        assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
        assert (q, b) not in rows
        rows[q, b] = (w, 1 if d == 'R' else -1, z)
    states = {q for q, b in rows}
    assert starts == [0] and 0 in states
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert len({z for w, d, z in rows.values()} - states) == 1
    return rows


def table_bytes(rows, start=0):
    return (f'#! start {start}\n' + ''.join(
        f'{q} {b} {w} {"R" if d == 1 else "L"} {z}\n'
        for (q, b), (w, d, z) in sorted(rows.items()))).encode('ascii')


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
