#!/usr/bin/env python3
"""Independently replay every row of the supplied exact rejection witnesses."""
from pathlib import Path
import hashlib
import json

ROOT = Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def rows(path):
    table = {}
    for line in path.read_text().splitlines():
        q, bit, write, move, target = line.split()
        table[int(q), int(bit)] = int(write), move, int(target)
    return table

def unpack(c):
    assert len(c['ones']) == len(set(c['ones']))
    return c['state'], c['head'], set(c['ones'])

def replay(table, start, certificate):
    q, head, ones = unpack(start)
    for q0, bit0, write0, move0, next0 in certificate:
        assert q == q0 and int(head in ones) == bit0
        assert table[q, bit0] == (write0, move0, next0)
        assert q != 254
        if write0 == 1:
            ones.add(head)
        else:
            assert write0 == 0
            ones.discard(head)
        assert move0 in ('L', 'R')
        head += 1 if move0 == 'R' else -1
        q = next0
    return q, head, ones

def main():
    table_path = ROOT / 'rejected193/REJECTED_16_to_38.native.tm'
    assert digest(table_path) == 'cb53ad33e8812dc2ebfb6a1a1b452962eeba0cf6b851d398d403a192ea0e6b80'
    table = rows(table_path)
    base_path = ROOT / 'inputs/pa194.native.tm'
    assert digest(base_path) == 'e0a7397cf2134e8e7f58a8b1de2f7ff90b74ededd54c912f6ba5b7db48dabe54'
    base = rows(base_path)
    # Reconstruct the stipulated mutation without importing the witness generator.
    reconstructed = {}
    for (q, bit), row in base.items():
        if q != 16:
            write, move, target = base[16, bit] if q == 38 else row
            reconstructed[q, bit] = write, move, 38 if target == 16 else target
    assert table == reconstructed
    assert len(table) == 386 and len({q for q, _ in table}) == 193
    result = []
    for name in ('blank', 'site3661_positive'):
        path = ROOT / f'rejected193/{name}_cycle.json'
        witness = json.loads(path.read_text())
        assert witness['machine_sha256'] == digest(table_path)
        assert witness['preperiod'] == len(witness['prefix_rows'])
        assert witness['period'] == len(witness['cycle_rows']) > 0
        if name == 'blank':
            assert witness['initial_configuration'] == {'state': 74, 'head': 0, 'ones': []}
        else:
            # Independently construct physical unary frame for logical T=1.
            ones = {-1, 48} | {i for i, b in enumerate('101100') if b == '1'}
            p = 49
            for value in [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1]:
                p += 1
                for j in range(value + 1):
                    ones.add(p + j)
                p += value + 1
            assert unpack(witness['initial_configuration']) == (84, 0, ones)
        entry = unpack(witness['cycle_configuration'])
        assert replay(table, witness['initial_configuration'], witness['prefix_rows']) == entry
        assert replay(table, witness['cycle_configuration'], witness['cycle_rows']) == entry
        result.append({'case': name, 'preperiod': witness['preperiod'], 'period': witness['period'],
                       'entry_state': entry[0], 'entry_head': entry[1], 'entry_ones': len(entry[2]),
                       'full_tape_equality': True, 'replay': 'PASS'})
    receipt = {'evidence_status': 'Fresh independent literal replay after tmpfs loss', 'cases': result}
    (ROOT / 'rejected193/literal_replay_receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps(receipt, indent=2))

if __name__ == '__main__':
    main()
