#!/usr/bin/env python3
"""Bounded synthesis of an exact, nondestructive zero-run detector.

Requires z3-solver.  The entry's read-1 row is free unless --fix-one is set.
The nine finite-window contracts imply universal exterior-independent macros
for a SAT model, after literal replay.  UNSAT is restricted to the recorded
time, space, symmetry, and optional row restrictions; UNKNOWN proves neither
existence nor nonexistence.
"""
import argparse
import json
import os
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parent
vendor = Path(os.environ.get('ZFC246_VENDOR', ROOT.parent / 'vendor'))
if vendor.is_dir():
    sys.path.insert(0, str(vendor))
import z3


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--states', type=int, default=7)
    ap.add_argument('--steps', type=int, default=20)
    ap.add_argument('--seconds', type=int, default=180)
    ap.add_argument('--first-write', type=int, choices=[0, 1])
    ap.add_argument('--fix-one', action='store_true')
    ap.add_argument('--forbid-write', action='store_true')
    ap.add_argument('--seed', type=int, default=0)
    ap.add_argument('--long-min-read', type=int, default=-7)
    ap.add_argument('--long-min-exit', type=int, default=-7)
    ap.add_argument('--long-exit-head', type=int)
    ap.add_argument('--output', type=Path)
    a = ap.parse_args()
    n = a.states
    assert 1 <= n <= 14 and a.steps > 0 and a.seconds > 0
    assert -16 <= a.long_min_read <= -7 and -16 <= a.long_min_exit <= 1
    solver = z3.Solver()
    solver.set(timeout=1000 * a.seconds, random_seed=a.seed)
    write = [z3.Bool(f'w{i}') for i in range(2 * n)]
    right = [z3.Bool(f'r{i}') for i in range(2 * n)]
    target = [z3.BitVec(f'q{i}', 4) for i in range(2 * n)]
    for q in target:
        solver.add(z3.ULE(q, n + 1))
    if a.fix_one:
        solver.add(write[1], z3.Not(right[1]), target[1] == n)
    if a.first_write is not None:
        solver.add(write[0] == bool(a.first_write))
    if a.forbid_write:
        for i in range(2 * n):
            solver.add(write[i] == bool(i % 2))
    # A deliberately recorded renaming restriction, not an impossibility claim.
    solver.add(z3.Or(z3.ULE(target[0], 1), z3.UGE(target[0], n)))
    for j in range(1, n):
        for bit in (0, 1):
            solver.add(z3.Or(z3.ULE(target[2 * j + bit], min(n - 1, 2 * j + 1)),
                             z3.UGE(target[2 * j + bit], n)))

    def lookup(xs, index):
        value = xs[-1]
        for i in range(len(xs) - 2, -1, -1):
            value = z3.If(index == i, xs[i], value)
        return value

    for case in range(9):
        short = case < 8
        k = case
        initial = (1 << 18) | ((1 << (16 - k)) if short else 0)
        states = [z3.BitVec(f's{case}_{i}', 4) for i in range(a.steps + 1)]
        heads = [z3.BitVec(f'h{case}_{i}', 5) for i in range(a.steps + 1)]
        tapes = [z3.BitVec(f't{case}_{i}', 32) for i in range(a.steps + 1)]
        solver.add(states[0] == 0, heads[0] == 16, tapes[0] == initial)
        for i in range(a.steps):
            active = z3.ULT(states[i], n)
            solver.add(z3.Implies(active, z3.And(
                z3.ULE(heads[i], 18), z3.UGE(heads[i], 16 - k if short else 16 + a.long_min_read))))
            bit = z3.Extract(0, 0, z3.LShR(tapes[i], z3.ZeroExt(27, heads[i])))
            index = z3.ZeroExt(1, states[i]) * 2 + z3.ZeroExt(4, bit)
            w = lookup(write, index)
            r = lookup(right, index)
            q = lookup(target, index)
            mask = z3.BitVecVal(1, 32) << z3.ZeroExt(27, heads[i])
            changed = z3.If(w, tapes[i] | mask, tapes[i] & ~mask)
            solver.add(states[i + 1] == z3.If(active, q, states[i]))
            solver.add(heads[i + 1] == z3.If(active, z3.If(r, heads[i] + 1, heads[i] - 1), heads[i]))
            solver.add(tapes[i + 1] == z3.If(active, changed, tapes[i]))
        solver.add(tapes[-1] == initial, states[-1] == (n if short else n + 1))
        if short:
            solver.add(heads[-1] == 15 - k)
        else:
            solver.add(z3.ULE(heads[-1], 17), z3.UGE(heads[-1], 16 + a.long_min_exit))
            if a.long_exit_head is not None:
                solver.add(heads[-1] == 16 + a.long_exit_head)

    began = time.monotonic()
    answer = solver.check()
    exit_description = (f'at exact head {a.long_exit_head}, before any further read of the exterior'
                        if a.long_exit_head is not None
                        else f'at a zero head in [{a.long_min_exit},1]')
    result = {
        'status': str(answer), 'states': n, 'step_bound': a.steps,
        'seconds': time.monotonic() - began, 'timeout_seconds': a.seconds,
        'z3_version': z3.get_version_string(), 'random_seed': a.seed,
        'first_write': a.first_write, 'fixed_entry_one_row': a.fix_one,
        'long_min_read': a.long_min_read, 'long_min_exit': a.long_min_exit,
        'long_exit_head': a.long_exit_head,
        'forbid_write': a.forbid_write,
        'renaming_restrictions': 'q(0,0)<=1 or exit; q(j,b)<=min(n-1,2*j+1) or exit for j>=1',
        'scope': f'Nine bounded exact traces. Entry head 0; cells +1=0,+2=1. Short case k=0..7 has first left 1 at -k and active reads only [-k,2]. Long case has known zeros [{a.long_min_read},1], active reads only [{a.long_min_read},2], and arbitrary exterior outside this window. Entire tape restored; short exit n at head -k-1, long exit n+1 {exit_description}. Unknown is not an impossibility result.'
    }
    if answer == z3.sat:
        model = solver.model()
        result['table'] = [
            [i // 2, i % 2,
             int(z3.is_true(model.eval(write[i], model_completion=True))),
             'R' if z3.is_true(model.eval(right[i], model_completion=True)) else 'L',
             model.eval(target[i], model_completion=True).as_long()]
            for i in range(2 * n)]
    elif answer == z3.unknown:
        result['reason'] = solver.reason_unknown()
    out = a.output or ROOT / f'detector_n{n}_t{a.steps}_w{a.first_write}_fix{int(a.fix_one)}_nowrite{int(a.forbid_write)}_seed{a.seed}_left{a.long_min_read}_exit{a.long_min_exit}_head{a.long_exit_head}.json'
    out.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
