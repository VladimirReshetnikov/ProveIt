#!/usr/bin/env python3
"""Check a local guarded-region certificate for PA194ZR zero returns.

This checker does not use the compiler, tape simulator, positivity abstraction,
or any whole-program register invariant. Its inputs are two complete instruction
lists, whose instructions are jump(target), inc(register,target),
dec(register,zero_target,positive_target), or halt.

Proof principle: every entry edge to a finite protected region is the zero
branch of a decrement of r; execution inside the region cannot turn zero r into
nonzero r. If the start lies outside the region, r is zero whenever control is in
the region. Replacing jumps in the region by decrements of r with the same zero
destination therefore preserves each executed source transition exactly.

The source configurations include the program counter and all nine unbounded
natural-number registers. No bound or sampling of register values is used.
"""
import argparse
import hashlib
import json
from pathlib import Path

RETURN_SITES = {3, 9, 3526, 3532, 3544, 3550, 3627, 3633}
CLOSING_SITE = 3553
SITES = RETURN_SITES | {CLOSING_SITE}
REGION3 = set(range(10)) | set(range(3523, 3634)) | set(range(3638, 3646))
START = 25


def require(condition, message):
    if not condition:
        raise ValueError(message)


def edges(instructions):
    result = []
    for pc, instruction in enumerate(instructions):
        kind = instruction[0]
        if kind == 'jump':
            require(len(instruction) == 2, f'bad jump at {pc}')
            result.append((pc, instruction[1], 'jump', None))
        elif kind == 'inc':
            require(len(instruction) == 3, f'bad increment at {pc}')
            result.append((pc, instruction[2], 'increment', instruction[1]))
        elif kind == 'dec':
            require(len(instruction) == 4, f'bad decrement at {pc}')
            result.append((pc, instruction[2], 'zero', instruction[1]))
            result.append((pc, instruction[3], 'positive', instruction[1]))
        else:
            require(kind == 'halt' and len(instruction) == 1,
                    f'unknown instruction at {pc}')
        if kind in ('inc', 'dec'):
            require(type(instruction[1]) is int and 0 <= instruction[1] < 9,
                    f'bad register at {pc}')
    for source, target, branch, register in result:
        require(type(target) is int and 0 <= target < len(instructions),
                f'bad target at {source}')
    return result


def region_certificate(instructions, protected_register, region):
    es = edges(instructions)
    require(START not in region, 'start must be outside protected region')
    require(all(0 <= pc < len(instructions) for pc in region), 'bad region')
    incoming = [e for e in es if e[0] not in region and e[1] in region]
    require(bool(incoming), 'unexpected empty entry-edge certificate')
    for source, target, branch, register in incoming:
        require(branch == 'zero' and register == protected_register,
                f'unguarded external edge {source} -> {target}')
    for pc in sorted(region):
        instruction = instructions[pc]
        require(not (instruction[0] == 'inc' and instruction[1] == protected_register),
                f'register can become positive within region at {pc}')
        # A decrement preserves zero in the protected register. When it
        # decrements that register, only the zero branch is executable.
    return {
        'protected_register': protected_register,
        'region': sorted(region),
        'region_size': len(region),
        'outside_entry_edges': [
            {'source': p, 'target': q, 'branch': b, 'register': r}
            for p, q, b, r in sorted(incoming)
        ],
        'region_instructions': {str(p): instructions[p] for p in sorted(region)},
        'invariant': f'pc in region implies R{protected_register} = 0',
        'entry_pc': START,
        'initial_registers': 'arbitrary natural numbers',
        'induction': 'entry edges establish zero; internal steps preserve zero',
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--original', type=Path, required=True)
    parser.add_argument('--modified', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    old = json.loads(args.original.read_text())
    new = json.loads(args.modified.read_text())
    require(len(old) == len(new) == 3646, 'unexpected source size')
    require(SITES <= REGION3, 'changed sites lie outside protected region')
    old_certificate = region_certificate(old, 3, REGION3)
    new_certificate = region_certificate(new, 3, REGION3)
    differences = {i for i, (x, y) in enumerate(zip(old, new)) if x != y}
    require(differences == SITES, 'unexpected source differences')
    replacements = []
    for pc in sorted(differences):
        require(old[pc][0] == 'jump', f'old instruction is not jump at {pc}')
        register = 3
        require(new[pc][0] == 'dec' and new[pc][1] == register,
                f'new instruction is not DEC{register} at {pc}')
        require(new[pc][2] == old[pc][1], f'zero destination differs at {pc}')
        replacements.append({'site': pc, 'before': old[pc], 'after': new[pc]})
    result = {
        'ok': True,
        'original_sha256': hashlib.sha256(args.original.read_bytes()).hexdigest(),
        'modified_sha256': hashlib.sha256(args.modified.read_bytes()).hexdigest(),
        'source_sites': len(old),
        'changed_sites': sorted(differences),
        'changed_sites_count': len(differences),
        'original_certificate': old_certificate,
        'modified_certificate': new_certificate,
        'replacements': replacements,
        'conclusion': 'For every initial register store at pc25, both programs '
                      'have identical complete configurations after every '
                      'source step, and hence identical halting behavior.',
        'proof': 'Induct on source steps. The protected-region invariant '
                 'gives R3=0 at all nine changed instructions. Both the old jump '
                 'and the new zero decrement leave the complete register '
                 'store unchanged and enter the same target. Every other '
                 'instruction is literally equal.',
        'scope': 'Source semantics only. Table-to-source contracts and the '
                 'inherited proof-search calibration are separate obligations.',
    }
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({k: result[k] for k in (
        'ok', 'source_sites', 'changed_sites_count', 'changed_sites', 'conclusion'
    )}, indent=2))


if __name__ == '__main__':
    main()
