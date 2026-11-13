#!/usr/bin/env python3
"""Independently enumerate the finite blocker-phase intersection; no Lean."""
import json
period = 8807
def bad(x):
    return x <= 1065 or x in (1095, 2195, 3296)
a = [d for d in range(period) if bad((2195-d) % period)]
b = [d for d in range(period) if bad((3296-d) % period)]
intersection = sorted(set(a).intersection(b))
assert len(a) == len(b) == 1069
assert intersection == [0]
print(json.dumps({'period': period, 'first_bad_count': len(a),
                  'second_bad_count': len(b), 'intersection': intersection,
                  'lean_launched': False}, indent=2, sort_keys=True))
