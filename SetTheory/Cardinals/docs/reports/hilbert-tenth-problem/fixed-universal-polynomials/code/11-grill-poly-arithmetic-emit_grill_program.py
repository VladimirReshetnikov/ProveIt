# Portable locally authored code; upstream Python is never imported or executed.
# See PROVENANCE.json and PORTABILITY.md for all transformations.
"""Literal corrected Grill table from the pinned numerical Genera table."""
from array import array
from pathlib import Path
from collections import Counter
import hashlib, json, sys, time, resource
ROOT = Path(__file__).resolve().parent
SOURCE = ROOT.parent / 'input-research/literal/literal_tables.json'
SOURCE_SHA = '3c8924dbb1b5d6e6b8897e59550b0e38a703654b87442c73487f411e94ae355b'

def emit():
    started = time.monotonic()
    raw = SOURCE.read_bytes()
    if hashlib.sha256(raw).hexdigest() != SOURCE_SHA:
        raise ValueError('Literal Genera source pin')
    g = json.loads(raw)['genera']
    rows = g['alphabet']
    N = len(rows)
    halt = g['halt_symbol']
    a = 28 * (N + 1)
    m = 14 * a
    program = array('I', [0]) * m
    written = set()
    if program.itemsize != 4:
        raise RuntimeError('This writer requires a32-bit array I')

    def place(i, n):
        if type(i) is not int or type(n) is not int or (not (0 <= i < m and 0 <= n < 1 << 32)) or (i in written):
            raise ValueError('Conflicting/noncanonical run-table entry')
        program[i] = n
        written.add(i)

    def extension(y):
        return 3 * a // 2 if y == halt else 7 * a * (1 - rows[y]['width'])
    for phase in (0, 1):
        base = 7 * a * phase
        for y in range(N):
            for i, n in zip((28 * y + 17, 28 * y + 19, 28 * y + 21), (a - 3, 7, a - 4)):
                place(base + i, n)
            for i, n in zip((28 * y + a + 13, 28 * y + a + 15, 28 * y + a + 17), (a - 3, 7, a - 4)):
                place(base + i, n)
            if y == halt:
                continue
            u, v = rows[y]['productions'][phase]
            out = (14 * u + 7, 3, 3 * a - 14 * u - 10 + extension(u), 0, 14 * v + 7, 3, 3 * a - 14 * v - 10 + extension(v))
            for j, n in enumerate(out):
                place(base + 14 * y + 2 * a + 3 + 2 * j, n)
    hist = Counter(program)
    if sum((c for n, c in hist.items() if n)) != 24 * N - 12:
        raise ValueError('Positive support count')
    if sys.byteorder != 'little':
        program.byteswap()
    data = program.tobytes()
    (ROOT / 'grill_program.u32').write_bytes(data)
    meta = dict(schema='corrected_grill_run_table_u32le_v1', source=str(SOURCE), source_sha256=SOURCE_SHA, generator_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), program_sha256=hashlib.sha256(data).hexdigest(), program_bytes=len(data), alphabet_size=N, halt_symbol=halt, a=a, phase_count=m, initial_phase=0, positive_runs=m - hist[0], zero_runs=hist[0], distinct_exponents=len(hist), max_exponent=max(hist), histogram=dict(sorted(hist.items())), first_empty_time_contract='Inherited corrected E/L/R bridge and unique-H cleanup; no padding freedom.', resources=dict(elapsed_seconds=time.monotonic() - started, max_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024))
    (ROOT / 'grill_program.json').write_text(json.dumps(meta, indent=2, sort_keys=True) + '\n')
    return meta
if __name__ == '__main__':
    p = emit()
    print(json.dumps({k: v for k, v in p.items() if k != 'histogram'}, sort_keys=True))
