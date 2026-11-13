"""Untrusted paired simulator for selected canonical 239-token fixtures.

Adapted from the attributed structural_parameters/structural/translate.py
at ProveIt commit 65c32fbe4730bfe5a064502b0b95ebc798c732fa. The source is
its three-field return-reservation stream; the target is checker.py here.
This finite-fixture translator is not a proof of equivalence on every raw
input. Missing source eigenparameters are injected into odd negative names;
allocated target eigenparameters are even powers of ten.
"""
from copy import deepcopy
import json
from pathlib import Path
import sys
sys.set_int_max_str_digits(0)

MISSING = object()


class Unsupported(ValueError):
    pass


class Translation:
    def __init__(self, rows):
        self.source = rows
        self.cursor = 1
        self.floor = 0
        self.names = {}
        self.output = [deepcopy(rows[0])]
        self.events = []
        self.allocations = []
        self.mismatches = []

    def old_open(self, a, t=MISSING, d=0):
        if type(a) is list:
            return [self.old_open(b, t, d + 5 - len(a)) for b in a]
        if type(a) not in (int, bool):
            raise Unsupported('source data is not exact integer/list')
        if self.floor <= a < d:
            return a
        return d % 2 and self.old_open(t, d=3)

    def new_open(self, a, t=MISSING, d=0):
        if type(a) is list:
            return [self.new_open(b, t, d + 5 - len(a)) for b in a]
        # The compact condition may supply False as the zero image.
        if type(a) not in (int, bool):
            raise Unsupported('target missing image was demanded')
        if a < d:
            return a
        return d % 2 and self.new_open(t, d=3)

    def rename(self, a):
        if type(a) is list:
            return [self.rename(b) for b in a]
        if type(a) is not int:
            raise Unsupported('non-integer/list source data')
        if a >= 0:
            return a
        if a < self.floor:
            raise Unsupported('future negative scalar used as a hole')
        if a not in self.names:
            # Fixed free labels are odd; the fresh powers of ten are even.
            self.names[a] = 2 * a - 1
        return self.names[a]

    def run(self):
        self.visit([0], self.source[0], [0], self.output[0])
        return self.output

    def visit(self, old_g, old_a, new_g, new_a):
        if self.cursor >= len(self.source):
            raise Unsupported('source ran out of packets')
        position = self.cursor
        row = self.source[self.cursor]
        self.cursor += 1
        if type(row) is not list or len(row) != 3:
            raise Unsupported('source packet is not a triple')
        os, ou, ot = row
        new_row = self.rename(row)
        ns, nu, nt = new_row
        # Save the actual input packet before extending its runtime value.
        self.output.append(deepcopy(new_row))
        old_ax = [[os and [os], ou, ot],
                  self.old_open(ot, row, 3) if os else ou]
        new_ax = [[ns and [ns], nu, nt],
                  self.new_open(nt, new_row, 3) if ns else nu]
        old_checked = self.old_open(old_a)
        new_checked = self.new_open(new_a)
        old_terminal = old_checked in [*old_g, old_ax]
        new_terminal = new_checked in [*new_g, new_ax]
        if old_terminal != new_terminal:
            raise Unsupported(f'terminal mismatch at packet {position}')
        if old_terminal:
            self.events.append({'packet': position, 'rule': 'hypothesis' if old_checked in old_g else 'computation'})
            self.floor -= 1
            return

        size = len(str([new_g, new_a, new_row]))
        if size > 2000000:
            raise Unsupported('diagnostic output cap exceeded; not a kernel rule')
        fresh = -10 ** size
        old_elim = self.old_open(ot, ou) == old_a
        new_elim = self.new_open(nt, nu) == new_a
        if old_elim != new_elim:
            raise Unsupported(f'elimination mismatch at packet {position}')
        if old_elim:
            old_a = self.old_open(ot, os)
            os = row[:2] if os else [ot] * 3
            new_a = self.new_open(nt, ns)
            ns = new_row[:2] if ns else [nt] * 3
        old_h = os * 3
        new_h = ns * 3
        if not old_h:
            if type(old_a) is not list or len(old_a) != 1:
                raise Unsupported('noncanonical introduction shape')
            old_a = self.old_open(old_a[0], ot, 2)
            new_a = self.new_open(new_a[0], nt, 2)
            old_h, new_h = old_a, new_a

        # The old floor changes in the major proof; the new scalar was
        # fixed from the full caller state before that proof ran.
        self.visit(old_g, os, new_g, ns)
        if self.floor in self.names:
            raise Unsupported('reserved name already allocated')
        self.names[self.floor] = fresh
        self.allocations.append({'packet': position, 'old_name': self.floor,
                                 'name_decimal_digits': size + 1})
        old_image = (os or len(old_a) == 2) and self.floor
        new_image = (ns or len(new_a) == 2) and fresh
        old_h = self.old_open(old_h, old_image)
        new_h = self.new_open(new_h, new_image)
        old_next = self.old_open(old_a, [self.floor])
        new_next = self.new_open(new_a, [fresh])
        kind = 'elimination' if old_elim else ('D-elimination' if os else ('progress' if len(old_a) == 2 else 'case'))
        self.events.append({'packet': position, 'rule': kind})
        self.visit([*old_g, old_h], old_next, [*new_g, new_h], new_next)
        self.floor -= 1


def tree_size(tree):
    return 1 + sum(map(tree_size, tree)) if type(tree) is list else 1


def read_stream(path):
    return [json.loads(line) for line in Path(path).read_text().splitlines() if line.strip()]


def integerize(a):
    return [integerize(x) for x in a] if type(a) is list else int(a) if type(a) is bool else a


def write_stream(path, rows):
    Path(path).write_text(''.join(json.dumps(integerize(row), separators=(',', ':')) + '\n' for row in rows))


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source')
    parser.add_argument('target')
    options = parser.parse_args()
    translation = Translation(read_stream(options.source))
    write_stream(options.target, translation.run())
    print(json.dumps({'packets': translation.cursor - 1,
                      'allocations': translation.allocations,
                      'events': translation.events}, indent=2))
