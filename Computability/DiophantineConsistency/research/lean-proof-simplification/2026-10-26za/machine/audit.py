#!/usr/bin/env python3
"""Read-only source and finite-model validation; never invokes Lean or the network.

Default: read ../baseline and print JSON to stdout. --output explicitly saves it.
The --negative-control option deliberately corrupts a modeled receiver south
color; successful detection is a nonzero exit, under normal Python and python -O.
"""
from pathlib import Path
from itertools import product
import argparse
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent
PIN = '22e020937caa81d0cb72a4f63071d6c0bcc1eba9'
EXPECTED = {
 'WangTiles942StepConstruction': '935bfb4b2762bd099185350f3869114c81f11140a823951e6319a33ce292138f',
 'WangMachineAction': '1776d84d82ae32ec58287779e639ce163bf0e10dec24056effc3aa4c2f1d3bd5',
 'WangMachineEncoding': '0cb7f88e2cbc8fce77aed656a508d1154cb31c96d3ca2764c970591fc050806e',
 'DecimalMachineInitialization': '748587f903a4a1cc0d0c475ebc0ba9628887eaff0584e6d3a7944f4115b6b82f',
 'WangTiles942Core': '7471a9ff93f06d0eb39c2f3791d5db28dd2927e6346213173f38c2b3ea150d85',
 'WangTiles942Data': 'ac9047c705dddbab3bec84265beff2d72d498496bde12261cc76c46dc0c5a125',
 'DecimalMachine215': 'da9e49c1a5f47a10d1f385810e1e89d2e3f4f25fc438dc85cf2184efdc3c719a',
 'WangTiles942Language': 'a28056b4929cfea69255619b5d89b5f7a64dc47efe0e94ca2e43e00f7788228d',
 'WangMachineStep': '479ef25344a09804f3eeb6bd980e947941af55965ac48291349f90de14c3f100',
 'WangTiles942RowStep': 'f4b6f60e4dece143de6d45120c8aa8ae84691d50b1b888e6e0dcb0226f17f84b',
}

class ValidationError(Exception):
    pass


def require(condition, message):
    if not condition:
        raise ValidationError(message)


def source_dir(base):
    candidates = [base / 'Computability/DiophantineConsistency/Lean/DiophantineConsistency',
                  base / 'Lean/DiophantineConsistency', base / 'DiophantineConsistency', base]
    found = [p for p in candidates if (p / 'WangTiles942RowStep.lean').is_file()]
    require(bool(found), 'Cannot find frozen WangTiles942RowStep.lean below --baseline.')
    return found[0]


def replay_patch(source, patch):
    """Strict, zero-fuzz unified patch replay in memory; no files are written."""
    src = source.splitlines(keepends=True)
    lines = patch.splitlines(keepends=True)
    out, cursor, i = [], 0, 0
    while i < len(lines):
        if not lines[i].startswith('@@ '):
            i += 1
            continue
        match = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
        require(match is not None, 'Malformed unified patch hunk.')
        start = int(match.group(1)) - 1
        require(cursor <= start, 'Overlapping or out-of-order patch hunk.')
        out.extend(src[cursor:start])
        cursor = start
        before_count, after_count = 0, 0
        i += 1
        while i < len(lines) and not lines[i].startswith('@@ '):
            line = lines[i]
            require(bool(line) and line[0] in ' +-','Unexpected patch control line.')
            if line[0] in ' -':
                require(cursor < len(src) and src[cursor] == line[1:],
                        'Patch context mismatch: frozen source differs.')
                cursor += 1
                before_count += 1
            if line[0] in ' +':
                out.append(line[1:])
                after_count += 1
            i += 1
        require(before_count == int(match.group(2) or 1), 'Patch source hunk count differs.')
        require(after_count == int(match.group(4) or 1), 'Patch target hunk count differs.')
    out.extend(src[cursor:])
    return ''.join(out)


def signatures(text):
    return {m.group(1): re.sub(r'\s+', ' ', m.group(0).split(':=', 1)[0]).strip()
            for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?:=', text)}


def statistics(text):
    return {'nonblank_lines': sum(bool(line.strip()) for line in text.splitlines()),
            'bytes': len(text.encode())}


def proof_body(text, name):
    match = re.search(r'(?m)^theorem ' + re.escape(name) + r'\b', text)
    require(match is not None, 'Missing theorem: ' + name)
    end = re.search(r'(?m)^(?:theorem|/--|end )', text[match.end():])
    block = text[match.start():match.end() + end.start() if end else len(text)]
    require(':= by' in block, 'Missing tactic body: ' + name)
    return block.split(':= by', 1)[1].strip()


def validate(args):
    directory = source_dir(args.baseline)
    before_hashes = {name: hashlib.sha256((directory / (name + '.lean')).read_bytes()).hexdigest()
                     for name in EXPECTED}
    for name, digest in EXPECTED.items():
        require(before_hashes[name] == digest, 'Frozen source SHA256 mismatch: ' + name)
    source = (directory / 'WangTiles942RowStep.lean').read_text()
    candidate_path = ROOT / 'patched/WangTiles942RowStep.lean'
    patch_path = ROOT / 'canonical-row.patch'
    candidate_bytes = candidate_path.read_bytes()
    patch_bytes = patch_path.read_bytes()
    candidate, patch = candidate_bytes.decode(), patch_bytes.decode()
    require(replay_patch(source, patch) == candidate, 'Patch replay differs from shipped candidate.')
    old_sigs, new_sigs = signatures(source), signatures(candidate)
    require(all(new_sigs.get(name) == sig for name, sig in old_sigs.items()),
            'Original public theorem signature changed.')
    require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', candidate),
            'Candidate introduces a forbidden proof shortcut.')
    seen = set()

    def visit(module):
        name = module.removeprefix('DiophantineConsistency.')
        if name in seen:
            return
        require(name in EXPECTED, 'Unfrozen construction dependency: ' + name)
        require(name != 'WangTiles942RowStep', 'New construction import cycle.')
        seen.add(name)
        text = (directory / (name + '.lean')).read_text()
        for child in re.findall(r'(?m)^import (DiophantineConsistency\.\w+)', text):
            visit(child)

    visit('DiophantineConsistency.WangTiles942StepConstruction')
    data = (directory / 'WangTiles942Data.lean').read_text()
    block = data.split('def actionCache : Array Action := #[', 1)[1].split('\n ]', 1)[0]
    actions = [(w == 'true', d == 'true', int(q)) for w, d, q in
               re.findall(r'\((true|false), (true|false), (\d+)\)', block)]
    require(len(actions) == 430, 'Literal action count differs from 430.')
    require(actions[0] == (True, True, 1), 'Actual first action changed.')
    targets = {d: sorted({q for w, dd, q in actions if dd == d}) for d in [False, True]}

    def rail(d, q):
        return 205 - 199 * int(d) + sum(v < q for v in targets[d])

    def color(q, p, tape, x):
        return 2 * q + int(x in tape) + 2 if x == p else int(x in tape)

    def tile(j, p, tape, x):
        w, d, q = actions[j]
        n, r, bit = p + (1 if d else -1), rail(d, q), int(x in tape)
        if x == p:
            return ((1 - int(d)) * rail(False, q), j + 2, int(d) * rail(True, q), int(w))
        if x == n:
            wrong = 1 if args.negative_control else 0
            return (int(d) * r, bit, (1 - int(d)) * r, 2 * q + bit + 2 + wrong)
        return (0, bit, 0, bit)

    point_checks = cfg_checks = halt_configs = 0
    for j, (w, d, q1) in enumerate(actions):
        q0, oldbit = divmod(j, 2)
        for p in [-5, 0, 5]:
            offsets = [k for k in range(-3, 4) if k]
            for bits in product([False, True], repeat=6):
                tape = {p + k for k, bit in zip(offsets, bits) if bit}
                if oldbit:
                    tape.add(p)
                n = p + (1 if d else -1)
                ntape = (tape | {p}) if w else (tape - {p})
                for x in range(p - 3, p + 4):
                    tx = tile(j, p, tape, x)
                    require(tx[1] == color(q0, p, tape, x), 'Modeled north color mismatch.')
                    require(tx[3] == color(q1, n, ntape, x), 'Modeled south color mismatch.')
                    require(tile(j, p, tape, x + 1)[0] == tx[2], 'Modeled horizontal mismatch.')
                    expected = (2 * q1 + int(x in tape) + 2 if x == n else int(w)
                                if x == p else color(q0, p, tape, x))
                    require(tx[3] == expected, 'Modeled read/write/move formula mismatch.')
                    point_checks += 1
                cfg_checks += 1
                halt_configs += q1 == 215
    # Independent finite regression: no-finish, zero boundary edges.
    # These test conditions are NOT additional production theorem premises.
    allowed = {(0, 0, 0, 0), (0, 1, 0, 1), (0, 432, 0, 432), (0, 433, 0, 433)}
    for j, (w, d, q) in enumerate(actions):
        allowed.add(((1 - int(d)) * rail(False, q), j + 2, int(d) * rail(True, q), int(w)))
    for d in [False, True]:
        for q in targets[d]:
            for bit in [0, 1]:
                allowed.add((int(d) * rail(d, q), bit, (1 - int(d)) * rail(d, q), 2 * q + bit + 2))
    by_north_west = {}
    for t in allowed:
        by_north_west.setdefault((t[1], t[0]), []).append(t)
    unique_rows = 0
    for j in range(430):
        for bits in product([False, True], repeat=4):
            tape = {k for k, bit in zip([-2, -1, 1, 2], bits) if bit}
            if j % 2:
                tape.add(0)
            paths = [(0, [])]
            for x in range(-2, 3):
                north = color(j // 2, 0, tape, x)
                paths = [(t[2], path + [t]) for west, path in paths
                         for t in by_north_west.get((north, west), [])]
            rows = [path for east, path in paths if east == 0]
            require(rows == [[tile(j, 0, tape, x) for x in range(-2, 3)]],
                    'Finite five-cell row is not uniquely canonical.')
            unique_rows += 1
    require([color(1, 1, {0}, x) for x in [-2, -1, 0, 1, 2]] == [0, 0, 1, 4, 0],
            'Actual initializer profile changed.')
    require(all(color(1, 1, {0}, x) == color(1, 1, {0, 100}, x) for x in range(-1, 3)),
            'Exterior-tape counterexample failed.')
    after_hashes = {name: hashlib.sha256((directory / (name + '.lean')).read_bytes()).hexdigest()
                    for name in EXPECTED}
    require(after_hashes == before_hashes, 'Source bytes changed during validation.')
    require(candidate_path.read_bytes() == candidate_bytes, 'Candidate bytes changed during validation.')
    require(patch_path.read_bytes() == patch_bytes, 'Patch bytes changed during validation.')
    return {
      'pin': PIN, 'status': 'PASSED source/static and finite Python model checks; Lean NEVER RUN',
      'source_sha256_verified': before_hashes, 'patch_replay': 'passed in memory; no files applied',
      'input_immutability': 'verified before/after: frozen sources, patch and candidate',
      'public_theorem_signatures_preserved': sorted(old_sigs),
      'new_declarations': sorted(new_sigs.keys() - old_sigs.keys()),
      'construction_import_closure_modules': len(seen), 'construction_reaches_row_step': False,
      'literal_actions_read': len(actions), 'signed_heads_tested': [-5, 0, 5],
      'local_configurations': cfg_checks, 'color_and_matching_point_checks': point_checks,
      'halt_entry_configurations': halt_configs,
      'finite_five_cell_unique_rows_without_finish_zero_boundary': unique_rows,
      'initializer_colors_at_minus2_through2': [0, 0, 1, 4, 0],
      'scope_counterexample': 'Tapes [0] and [0,100] have identical colors on (-2,3) with head/state 1; list tapes [0] and [0,0] have identical reads everywhere but differ as lists.',
      'limits': 'No Lean elaboration, kernel acceptance, axiom-set or arbitrary-infinite-tiling verification. Finite no-finish and boundary restrictions are test conditions, not new production premises.',
      'candidate_sha256': hashlib.sha256(candidate_bytes).hexdigest(),
      'metrics': {
        'module_original': statistics(source), 'module_candidate': statistics(candidate),
        'modified_existing_proof_bodies': {
          name: {'before': statistics(proof_body(source, name)), 'after': statistics(proof_body(candidate, name))}
          for name in ['receiver_south', 'south_step']},
        'new_proof_bodies': {name: statistics(proof_body(candidate, name))
                             for name in ['receiver_tile', 'row_tile_eq_stepTile']}}
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, default=ROOT.parent / 'baseline',
                        help='Frozen full checkout, Lean root, or DiophantineConsistency module directory.')
    parser.add_argument('--output', type=Path, help='Explicitly save JSON here; default stdout only.')
    parser.add_argument('--negative-control', action='store_true',
                        help='Deliberately corrupt modeled receiver south color; expect exit status 1.')
    args = parser.parse_args()
    output_permitted = False
    try:
        if args.output:
            output = args.output.resolve()
            directory = source_dir(args.baseline).resolve()
            require(not output.is_relative_to(directory), 'Refusing output inside frozen source directory.')
            require(output not in {(ROOT / 'audit.py').resolve(), (ROOT / 'canonical-row.patch').resolve(),
                                    (ROOT / 'patched/WangTiles942RowStep.lean').resolve()},
                    'Refusing to overwrite validator, patch or candidate.')
        output_permitted = True
        result = validate(args)
        code = 0
    except (ValidationError, OSError, ValueError, IndexError) as exc:
        result = {'pin': PIN, 'status': 'FAILED', 'error': str(exc),
                  'negative_control_enabled': args.negative_control, 'Lean': 'NEVER RUN'}
        code = 1
    rendered = json.dumps(result, indent=2) + '\n'
    if args.output and output_permitted:
        args.output.write_text(rendered)
    sys.stdout.write(rendered)
    return code


if __name__ == '__main__':
    raise SystemExit(main())
