#!/usr/bin/env python3
"""Independent concrete checks supporting the source review; does not run Lean."""
import json
bad = {1063, 1064}
first = [d for d in range(8807) if (2194-d) % 8807 in bad]
second = [d for d in range(8807) if (3295-d) % 8807 in bad]
assert first == [1130, 1131] and second == [2231, 2232]
assert not set(first).intersection(second)
count = 0
for r in range(1,67):
    for x in (0,1):
        for y in (0,1):
            value = (x * 2**r) % (2**67) + y // (2**(67-r))
            assert value % 2 == 0 and value <= 2**66
            count += 1
print(json.dumps({'first_bad_shifts':first, 'second_bad_shifts':second,
                  'intersection':[], 'positive_remainder_boolean_cases':count,
                  'lean_launched':False}, sort_keys=True, indent=2))
