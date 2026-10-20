"""Own finite Source146 audit; imports no submitted executable module."""
from pathlib import Path
import argparse
import hashlib
import json
import subprocess


def sha(data):
    return hashlib.sha256(data).hexdigest()


def table(raw, count, halt):
    rows = {}
    starts = []
    for line in raw.decode('ascii').splitlines():
        if line.startswith('#! start '):
            starts.append(int(line[9:]))
        if not line or line.startswith('#'):
            continue
        q, bit, write, direction, target = line.split()
        q, bit, write, target = map(int, (q, bit, write, target))
        assert bit in (0, 1) and write in (0, 1) and direction in ('L', 'R')
        assert (q, bit) not in rows
        rows[q, bit] = write, 1 if direction == 'R' else -1, target
    states = {q for q, _ in rows}
    assert starts == [0] and len(states) == count
    assert set(rows) == {(q, bit) for q in states for bit in (0, 1)}
    assert {v[2] for v in rows.values()} - states == {halt}
    return rows


def run(rows, steps, record=False):
    state = head = 0
    ones = set()
    history = []
    for tick in range(steps + 1):
        if record:
            history.append(dict(steps=tick, state=state, head=head, ones=sorted(ones)))
        if tick == steps:
            return dict(steps=tick, state=state, head=head, ones=sorted(ones)), history
        write, move, state = rows[state, int(head in ones)]
        if write:
            ones.add(head)
        else:
            ones.discard(head)
        head += move


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists()
    root = Path(subprocess.check_output(['git', 'rev-parse', '--show-toplevel'], text=True).strip())
    base = root / 'Computability/BusyBeaver/Research/ZFC/candidate-k219'
    pins = {
        'core': (args.packet/'machine/core218/core218.native.tm', 'cd2e25ad8bd58112b74d671ff78334eacc0eb237201b32c871a73424e134073f'),
        'alternative': (args.packet/'machine/alternative219/k219.native.tm', '142cb09f13f336cf23330f959d5e78e4249c47a3d8f728efed7c61cc38825a11'),
        'baseline': (base/'k219.native.tm', 'b255f8ee341d394c303d67a7fca7f8288ed9d4c40f075899fa64b13085aaca26'),
    }
    raw = {name: path.read_bytes() for name, (path, _) in pins.items()}
    for name, (_, pin) in pins.items():
        assert sha(raw[name]) == pin
    old = table(raw['baseline'], 219, 254)
    core = table(raw['core'], 218, 254)
    alt = table(raw['alternative'], 219, 254)
    expected = {k: v for k, v in old.items() if k[0] != 301}
    expected.update({(87, 0): (0, 1, 88), (88, 0): (0, -1, 51), (51, 0): (0, 1, 122)})
    assert core == expected
    end, history = run(core, 85, True)
    assert history[79] == dict(steps=79, state=51, head=5, ones=[-3, -2])
    assert end == dict(steps=85, state=35, head=7, ones=[-3, -2])
    assert core[35, 0] == (1, 1, 35) and max(end['ones']) < end['head']
    alt_end, _ = run(alt, 312617)
    reference = json.loads((root/'Computability/BusyBeaver/Research/ZFC/candidate-k218/evidence/blank-startup.json').read_text())
    assert alt_end == dict(steps=312617, state=84, head=-5, ones=reference['final_one_cells'])
    source = json.loads((base/'sites219.json').read_bytes())
    alt_source = json.loads((args.packet/'machine/alternative219/sites219.json').read_bytes())
    assert [r[1:] for r in source] == [r[1:] for r in alt_source]
    assert (args.packet/'machine/core218/sites219.json').read_bytes() == (base/'sites219.json').read_bytes()
    changed = [list(k) for k in sorted(old) if alt[k] != old[k]]
    assert len(changed) == 35
    result = dict(status='FINITE_LITERAL_CHECK_PASS', input_pins={name: pin for name, (_, pin) in pins.items()},
        core_patch_exact=True, core_blank_prefix=history, core_ray_induction_premises=True,
        alternative_changed_rows=changed, alternative_complete_startup=alt_end,
        alternative_primitive_word_equal=True,
        scope='Exact table patch, concrete blank traces and ray premises, and source instruction word only. No alternate source CFG or primitive-runtime replay, no new kernel theorem.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: v for k, v in result.items() if k not in ('core_blank_prefix', 'alternative_complete_startup', 'alternative_changed_rows')}))


if __name__ == '__main__':
    main()
