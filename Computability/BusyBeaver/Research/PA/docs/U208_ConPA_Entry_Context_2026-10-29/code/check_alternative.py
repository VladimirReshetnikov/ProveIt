#!/usr/bin/env python3
"""Reuse the local theorem with explicit labels for the Compatibility variant."""
import argparse
import hashlib
import json
from pathlib import Path
from build import ROOT, read, need
from verify_fold import verify


def check(machine, output):
    old_path = ROOT / 'comparison/compatibility/u209.native.tm'
    new_path = Path(machine) / 'u208_compatibility.native.tm'
    old, new = read(old_path), read(new_path)
    # A bijection of labels used ONLY to instantiate the local theorem.
    # This is not an isomorphism claim for the two complete parent tables.
    joint_to_alternative = {163: 216, 216: 217, 217: 214, 214: 215, 215: 163}
    inverse = {v: k for k, v in joint_to_alternative.items()}
    rename = lambda q: inverse.get(q, q)
    def translated(table):
        return {(rename(q), b): (w, d, rename(z))
                for (q, b), (w, d, z) in table.items()}
    cases = verify(translated(old), translated(new))
    need(len(cases) == 4, 'Local case census')
    result = {'status': 'ALTERNATIVE_LOCAL_SIMULATION_PASS', 'working_states': 208,
              'transition_rows': 416, 'helper_native_label': 214,
              'label_instantiation': joint_to_alternative,
              'parent_sha256': hashlib.sha256(old_path.read_bytes()).hexdigest(),
              'candidate_sha256': hashlib.sha256(new_path.read_bytes()).hexdigest(),
              'cases_in_normalized_labels': cases,
              'scope': 'Same direct all-tape local theorem; no fresh full runtime replay for this variant.'}
    Path(output).write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--machine', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    a = p.parse_args()
    print(json.dumps(check(a.machine, a.output), indent=2))
