#!/usr/bin/env python3
"""Emit the literal Prog254 decoder unfolding and a kernel definitional identity.

The program is Jeff's attributed verification of Mira-Cult's machine, using
Wade's framework. Reuse the untrusted row reader/unfolder of generate_bisim254;
Lean checks equality with the actual Prog254.program independently. No binary
simulation, refutation calibration, or state reduction is inferred by this data.
"""
from __future__ import annotations
import argparse
from pathlib import Path
import generate_bisim254 as generator

REPO = Path(__file__).resolve().parents[4]
TARGET = REPO / 'Computability/BusyBeaver/Lean/BusyBeaver/ZFC/ActualTree254.lean'
HEADER = '''import BusyBeaver.ZFC.RMBisim
import BusyBeaver.ZFC.Prog254
namespace SetTheory.BusyBeaver.ZFC.ActualTree254
open RMBisim
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
/-- Entire literal program unfolding; checked against the actual decoder. -/
def tree : Tree :=
'''
FOOTER = '''\n theorem tree_eq : ptree Prog254.program = tree := by rfl
#print axioms tree_eq
end SetTheory.BusyBeaver.ZFC.ActualTree254
'''


def generate() -> bytes:
    if not __debug__:
        raise RuntimeError('Assertions must remain enabled')
    rows = generator.bisim254.load_prog254()
    assert len(rows) == 6459
    return (HEADER + generator.literal_tree(rows) + FOOTER).encode('utf-8')


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument('--out', type=Path, default=TARGET)
    parser.add_argument('--check', action='store_true', help='require byte-exact existing output')
    args = parser.parse_args()
    data = generate()
    if args.check:
        if args.out.read_bytes() != data:
            parser.error('Generated literal decoder source differs')
        print(f'PASS: exact literal decoder source ({len(data)} bytes)')
    else:
        args.out.write_bytes(data)
        print(f'Wrote {args.out} ({len(data)} bytes)')


if __name__ == '__main__':
    main()
