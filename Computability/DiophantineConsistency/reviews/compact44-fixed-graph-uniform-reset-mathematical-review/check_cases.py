#!/usr/bin/env python3
"""Concrete phase checks for the source review; does not run Lean."""
import json
period = 8807
phases = (2195, 3296, 4393, 5495)
def bad(x):
    return x <= 1065 or x in (1095, 2195, 3296)
predecessors = [(p-1) % period for p in phases]
assert all(not bad(p) for p in predecessors)
assert [bad(p) for p in phases] == [True, True, False, False]
count = 0
for N in (1, 2, 3, 5):
    for s in range(N):
        for k in range(period*N):
            assert ((k-period*s) % (period*N)) % period == k % period
            count += 1
print(json.dumps({'target_phases': phases, 'target_in_bad': [bad(p) for p in phases],
                  'predecessor_phases': predecessors, 'all_predecessors_outside_bad': True,
                  'small_standard_phase_shift_cases': count, 'lean_launched': False},
                 indent=2, sort_keys=True))
