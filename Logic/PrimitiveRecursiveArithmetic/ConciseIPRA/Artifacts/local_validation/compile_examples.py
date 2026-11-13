"""Untrusted canonical proof compiler; never imported by a checker.

The pinned compiler recodes a typed four-field native proof tree into the
actual-binder, three-field entry-reservation protocol. Its old neutral major
is scalar 0. The eager opener uses [] as that neutral major instead. Only an
introduction's source field changes; the canonical proof and every assigned
eigenparameter stay the same.
"""
from pathlib import Path
import copy
import json
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / 'compiler'))
from compile_three import translate


def compile_all():
    source = json.loads((ROOT / 'compiler/source_cases.json').read_text())['cases']
    result = []
    for case in source:
        if not case['expected']:
            continue
        document, stats = translate(case['certificate'], 'entry')
        document = copy.deepcopy(document)
        adapted = 0
        for record in document[:-1]:
            if (type(record) is list and len(record) == 3 and record[0] == 0
                    and (record[1] == 2 or record[1] == [])):
                record[0] = []
                adapted += 1
        result.append({'name': case['name'], 'certificate': document,
                       'expected': True, 'compiler_stats': stats,
                       'neutral_introductions_adapted': adapted})
    return result


if __name__ == '__main__':
    rows = compile_all()
    print(json.dumps({'cases': rows}, indent=1))
