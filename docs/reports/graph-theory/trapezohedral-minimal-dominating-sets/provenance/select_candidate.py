#!/usr/bin/env python3
"""Make a single unbiased OS-random draw after the candidate list is fixed."""
import json
import secrets
from pathlib import Path

# The recorded draw lives beside this script, in the archive's provenance/
# directory. It concerns how the incoming manuscript's author chose this
# problem; it is not part of the A381190 proof or its verification.
here = Path(__file__).resolve().parent
candidates = json.loads((here / 'candidates.json').read_text())
output = here / 'selection.json'
if output.exists():
    raise SystemExit('Refusing to replace the recorded selection.')
# randbelow uses rejection sampling; no outcome-dependent reroll is performed.
index = secrets.randbelow(len(candidates))
record = {'method':'Python secrets.randbelow(4), OS randomness, one call; zero-based result converted to one-based index',
          'candidate_count':len(candidates), 'zero_based_index':index,
          'one_based_index':index+1,'selected':candidates[index], 'rerolls':0}
output.write_text(json.dumps(record, indent=2) + '\n')
print(json.dumps(record, indent=2))
