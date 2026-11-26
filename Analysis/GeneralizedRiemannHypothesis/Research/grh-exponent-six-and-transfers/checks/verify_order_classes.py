#!/usr/bin/env python3
"""Check every listed ring class group using the supplied reduced-form routines.

Call with Table-6.txt and the folder containing the two incoming reduced-form checkers.
This verifies the listed groups, while the proof and the cited conductor enumeration
supply exhaustiveness.
"""
import ast
import re
import sys
from math import prod
from pathlib import Path

sys.path.insert(0, sys.argv[2])
from check_exponent_five import power_is_principal
from check_exponent_six_fields import reduced_forms


def main():
    checked = set()
    total_classes = 0
    for line in Path(sys.argv[1]).read_text().splitlines():
        match = re.fullmatch(r"Group='([^']+)': (\[.*\])", line)
        if not match:
            continue
        factors = tuple(int(n) for n in re.findall(r'Z(\d+)', match[1]))
        assert set(factors) <= {2, 3, 6} and 6 in factors
        expected_order = prod(factors)
        for d in ast.literal_eval(match[2]):
            assert d not in checked
            checked.add(d)
            forms = tuple(reduced_forms(-d))
            assert len(forms) == expected_order
            assert all(power_is_principal(form, 6) for form in forms)
            # A group of this order annihilated by 6 has the prescribed
            # elementary-abelian 2- and 3-Sylow subgroups.
            total_classes += len(forms)
    assert len(checked) == 1236
    print('order discriminants verified:', len(checked))
    print('primitive reduced classes whose sixth powers were checked:', total_classes)
    print('computed group orders agree with all the printed group structures')


if __name__ == '__main__':
    main()
