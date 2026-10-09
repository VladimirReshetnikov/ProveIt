"""Exact huge-program demonstrations; no knot-source certification is implied."""
import json
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from compiled_ports import Profiles, ConeProgram
from compiled_ports.profiles import json_safe
from compiled_ports.verify import verify_threshold, verify_change_points


def main():
    q, delay = 1 << 256, 1 << 4096
    table = Profiles.from_histogram((q,)*8, {(1,)*8: q})
    records = [dict(op='cone', atoms=[]), dict(op='power', child=0, exponent=delay),
               dict(op='cone', atoms=[3]), dict(op='concat', left=1, right=2),
               dict(op='power', child=3, exponent=delay)]
    p = ConeProgram(8, records)
    answer = p.first_at_most(table, 1)
    assert answer['index'] == delay + 1
    assert verify_threshold(table, records, p.root, 1, answer['index'])
    events = p.change_points(table)
    assert verify_change_points(table, records, p.root, events['events'])
    out = dict(scope='Abstract source census, not a knot or native source certificate',
               profiles=table.to_dict(), program=records, root=p.root,
               target=1, first_threshold=answer, history=events)
    (ROOT/'examples'/'delayed_program.json').write_text(json.dumps(json_safe(out), indent=2)+'\n')
    print('expanded length bits:', p.length.bit_length())
    print('first threshold bits:', answer['index'].bit_length())
    print('first threshold state trials:', answer['trials'])
    print('all history events:', len(events['events']))
    print('independent threshold and complete-history replay: PASS')

if __name__ == '__main__':
    main()
