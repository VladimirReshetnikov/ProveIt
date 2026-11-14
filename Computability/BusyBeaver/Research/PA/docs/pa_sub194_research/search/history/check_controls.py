#!/usr/bin/env python3
"""Positive and adverse controls for repaint_fold.py; standard library only."""
import json
from repaint_fold import search

def fixture():
    rows = {}
    for bit in (0, 1):
        rows[0, bit] = (0, 1, 2)
        rows[1, bit] = (0, 1, 3)
        rows[2, bit] = (0, 1, 7)
        rows[3, bit] = (1, 1, 7)
        rows[5, bit] = rows[2, bit]
        rows[6, bit] = rows[3, bit]
        rows[7, bit] = (bit, 1, 99)
    rows[4, 0] = (0, 1, 5)
    rows[4, 1] = (0, 1, 6)
    return rows

def witness(result):
    return next((r for r in result['candidates']
                 if r['delete'] == 2 and r['keep'] == 3
                 and r['tags'] == [0, 1]), None)

if __name__ == '__main__':
    assert __debug__, 'Run without -O.'
    rows = fixture()
    found = witness(search(rows, start=0, fuel=9))
    assert found is not None
    rows[4, 1] = (1, 1, 6)  # Deliberately fail to restore the old history bit.
    assert witness(search(rows, start=0, fuel=9)) is None
    print(json.dumps({'status': 'PASS', 'positive_same_old_history_fold_found': True,
                      'corrupted_restore_rejected': True,
                      'positive_witness': found}, indent=2))
