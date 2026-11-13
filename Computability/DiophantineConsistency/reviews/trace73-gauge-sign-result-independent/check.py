import hashlib, json, os, pathlib

root = pathlib.Path(__file__).resolve().parents[2]
packet = root / 'research/trace73-gauge-sign'
obs = packet / 'observations/attempt04'
h = lambda p: hashlib.sha256(pathlib.Path(p).read_bytes()).hexdigest()
t = json.loads((obs / 'terminal.json').read_text())
assert t['status'] == 'PASS' and t['exit'] == 0 and t['reason'] is None
assert h(packet / 'Trace73GaugeSign.lean') == t['source_sha256'] == h(obs / 'source.txt')
assert h(packet / 'run.py') == t['runner_sha256']
assert h(t['output']) == t['output_sha256']
assert h(obs / 'stdout') == t['stdout_sha256'] and h(obs / 'stderr') == t['stderr_sha256']
assert (obs / 'stderr').read_bytes() == b''
assert (obs / 'stdout').read_text() == ("'Trace73GaugeSign.B_negative_after_one' depends on axioms: [propext, Classical.choice, Quot.sound]\n" "'Trace73GaugeSign.positive_zero_to_negative_B' depends on axioms: [propext, Classical.choice, Quot.sound]\n")
for name, pin in t['pins'].items():
    assert str(pathlib.Path(name).resolve()) == pin['resolved'] and h(name) == pin['sha256'], name
paths = t['lean_path'].split(':')
for mod in ('Trace73Gauge', 'Mathlib.Tactic.Linarith', 'Mathlib.Algebra.Order.Ring.Basic'):
    candidates = [pathlib.Path(p) / (mod.replace('.', '/') + '.olean') for p in paths]
    first = next(p for p in candidates if os.path.lexists(p))
    assert first.is_file() and str(first) in t['pins'], (mod, first)
    print(mod, 'first', first)
assert t['preflight']['mem_available_kib'] >= 8*1024*1024
assert all(s['mem_available_kib'] >= 8*1024*1024 and len(s['lean']) <= 2 for s in t['samples'])
print('PASS source/runner/object, both reports, ten pins, direct first resolutions and resource samples')
