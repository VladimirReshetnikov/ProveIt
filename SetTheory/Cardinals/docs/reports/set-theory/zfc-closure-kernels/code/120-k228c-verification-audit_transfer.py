#!/usr/bin/env python3
"""Independent finite interface audit for the K228 mathematical transfer.

This checks data identities and a complete finite bootstrap.  The quantified
symbolic-runtime soundness and source context theorem are argued separately in
K228_TRANSFER_AUDIT.md.  No construction or runtime-checker module is imported.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
from collections import Counter

parser = argparse.ArgumentParser()
parser.add_argument('--package-root', type=Path, default=Path(__file__).resolve().parents[1])
parser.add_argument('--runtime-dir', type=Path,
                    help='Directory containing a complete portable verification.json/runtime_cases.json, '
                         'or discovery runtime228_composed.json/runtime228_composed_cases.json. '
                         'Defaults to the portable replay if present, otherwise discovery.')
parser.add_argument('--output-dir', type=Path,
                    help='Directory for transfer_audit.json (default: PACKAGE/receipts/audit).')
args = parser.parse_args()
if not __debug__:
    raise RuntimeError('Assertions must be enabled.')
root = args.package_root.resolve()
local = root / 'machine'
upstream = root / 'upstream/k230'
runtime_dir = args.runtime_dir
if runtime_dir is None:
    portable = root / 'receipts/replay/runtime'
    runtime_dir = portable if (portable / 'verification.json').exists() else root / 'receipts/discovery'
output_dir = args.output_dir or root / 'receipts/audit'
output_dir.mkdir(parents=True, exist_ok=True)


def read_json(path):
    return json.loads(path.read_text())


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def table(path):
    rows = {}
    start = None
    for line in path.read_text().splitlines():
        if line.startswith('#! start '):
            assert start is None
            start = int(line[len('#! start '):])
        elif line and not line.startswith('#'):
            q, b, w, d, z = line.split()
            q, b, w, z = map(int, (q, b, w, z))
            assert b in (0, 1) and w in (0, 1) and d in ('L', 'R')
            assert (q, b) not in rows
            rows[q, b] = (w, -1 if d == 'L' else 1, z)
    states = {q for q, _ in rows}
    assert set(rows) == {(q, b) for q in states for b in (0, 1)}
    assert start in states
    terminal = {z for w, d, z in rows.values()} - states
    assert len(terminal) == 1
    return rows, start, states, terminal.pop()


def validate_source(sites):
    leaves = {}
    prefixes = set()
    for pc, op, arg in sites:
        assert pc and len(pc) <= 40 and set(pc) <= {'0', '1'}
        assert pc not in leaves and op in ('CI', 'CD', 'CB', 'CC', 'CH')
        if op == 'CH':
            assert arg is None
        elif op in ('CI', 'CD'):
            assert type(arg) is int and 0 <= arg < 9
        else:
            assert type(arg) is int and arg >= 1
        leaves[pc] = (op, arg)
        prefixes.update(pc[:i] for i in range(len(pc)))
    assert not set(leaves) & prefixes
    assert all(p + b in leaves or p + b in prefixes for p in prefixes for b in '01')
    assert len(prefixes) == len(leaves) - 1
    return leaves, prefixes


# Independently parse the actual theorem-calibrated Coq source tree.
assert digest(upstream / 'coq/tm/Prog230.v') == 'b795e411095048db7849efe621d6b9fef4da3523167c7848ade26e3c715b83cc'
coq = (upstream / 'coq/tm/Prog230.v').read_text()
body = coq.split('Definition p230_tab : list (cedge * cedge) := [', 1)[1].split('].', 1)[0]
node_text = re.findall(r'\((CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH), '
                       r'(CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)\)', body)
assert len(node_text) == 5124
assert not re.sub(r'\((CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH), '
                  r'(CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)\)', '', body).strip(' ;\n\r\t')
assert re.search(r'root\s*:=\s*0\s*;\s*nnodes\s*:=\s*5124', coq)
assert 'Definition R0 : regs := upd (upd regs0 0 3) 4 3.' in coq
parsed = []
visits = set()


def expand(n, pc='', ancestors=frozenset()):
    assert 0 <= n < len(node_text) and n not in ancestors
    visits.add(n)
    for b, token in zip('01', node_text[n]):
        op, *rest = token.split()
        value = int(rest[0]) if rest else None
        if op == 'CN':
            expand(value, pc + b, ancestors | {n})
        else:
            parsed.append([pc + b, op, value])


expand(0)
assert len(visits) == 5124
original = parsed
machine_sites = read_json(upstream / 'machine/sites230.json')
names = {'EInc': 'CI', 'EDecnz': 'CD', 'EBreak': 'CB', 'EContinue': 'CC', 'EHalt': 'CH'}
converted = []
for pc, edge in machine_sites:
    op, *arg = edge.split()
    converted.append([pc, names[op], int(arg[0]) if arg else None])
assert converted == original
before, old_prefixes = validate_source(original)

old_pattern = [('00', 'CD', 6), ('010', 'CI', 5), ('011', 'CC', 2), ('1', 'CI', 5)]
new_pattern = [('0', 'CI', 5), ('10', 'CD', 6), ('11', 'CC', 2)]
replacement_paths = []
for p in sorted(old_prefixes):
    inside = sorted((q[len(p):], *op) for q, op in before.items() if q.startswith(p))
    if inside == old_pattern:
        replacement_paths.append(p)
assert len(replacement_paths) == 4
assert all(not a.startswith(b) for a in replacement_paths for b in replacement_paths if a != b)
expected = [s for s in original if not any(s[0].startswith(p) for p in replacement_paths)]
for p in replacement_paths:
    expected += [[p + q, op, arg] for q, op, arg in new_pattern]
expected.sort()
changed_path = root / 'source/sites_logical.json'
changed = read_json(changed_path)
assert expected == changed
after, new_prefixes = validate_source(changed)
assert len(original) == 5125 and len(changed) == 5121


def static_bounds(leaves):
    def rec(p):
        if p in leaves:
            op, arg = leaves[p]
            return (0, 1 if op == 'CD' else arg if op == 'CB' else 0,
                    arg if op == 'CC' else 0)
        ha, ba, ca = rec(p + '0')
        hb, bb, cb = rec(p + '1')
        return (1 + max(ha, hb), max(ba - 1, bb), max(ca, cb - 1))
    return rec('')


assert static_bounds(before) == static_bounds(after) == (40, 0, 0)


def increment(p):
    bits = list(p)
    for i in range(len(bits) - 1, -1, -1):
        if bits[i] == '0':
            bits[i] = '1'
            return ''.join(bits), False
        bits[i] = '0'
    return ''.join(bits), True


def drop_through(p, bit, count):
    for i in range(len(p) - 1, -1, -1):
        if p[i] == bit:
            count -= 1
            if count == 0:
                return p[:i]
    return ''


def successor(pc, op, arg, positive=False):
    if op == 'CH':
        return None
    if op == 'CI' or (op == 'CD' and positive):
        return increment(pc)[0]
    if op == 'CD' or op == 'CB':
        return increment(drop_through(pc, '0', 1 if op == 'CD' else arg))[0]
    assert op == 'CC'
    return drop_through(pc, '1', arg)


def dispatch(leaves, p):
    q = ''
    while q not in leaves:
        q += p[len(q)] if len(q) < len(p) else '0'
        assert len(q) <= 40
    assert set(p[len(q):]) <= {'0'}, ('stray nonzero path suffix', p, q)
    return q


def contextual(pc):
    for p in replacement_paths:
        if pc.startswith(p):
            return ('replacement', p)
    return ('outside', pc)


control_edges = 0
outside_edges = 0
incoming = {p: [0, 0] for p in replacement_paths}
for version, leaves in enumerate((before, after)):
    for pc, (op, arg) in leaves.items():
        for positive in ((False, True) if op == 'CD' else (False,)):
            p = successor(pc, op, arg, positive)
            if p is None:
                continue
            dest = dispatch(leaves, p)
            control_edges += 1
            if contextual(pc)[0] == 'outside':
                for block_root in replacement_paths:
                    if dest.startswith(block_root):
                        assert dest == dispatch(leaves, block_root)
                        incoming[block_root][version] += 1
                if version == 0:
                    assert after[pc] == (op, arg)
                    other_dest = dispatch(after, successor(pc, op, arg, positive))
                    assert contextual(dest) == contextual(other_dest)
                    outside_edges += 1

# Exact literal table renamings, including start and terminal states.
assert digest(upstream / 'machine/k230.tm') == 'e7ccbcec074534cfd955f0ab94d16f13594e81974074309dc2ce663b9dfd7ba8'
assert digest(upstream / 'machine/sites230.json') == '400fad2b1c5f99ed8490f6346ff63088ba94fc39ada376962cee2f68c092e487'
assert digest(local / 'k228.tm') == '06726bd731f3a42e3ccd1c4189d80af74ba2d486e333045097480fcaa3313001'
assert digest(changed_path) == '61450579877bc79cc4bc323ff0b8ae506064c79644107f4d818401dcfbce941b'
release, q0, states230, halt230 = table(upstream / 'machine/k230.tm')
old, qo, oldstates, oldhalt = table(local / 'k228_oldlabels.tm')
normalized, qn, normstates, normhalt = table(local / 'k228_normalized.tm')
canonical, qc, canstates, canhalt = table(local / 'k228.tm')
normalization = {q: {0: 95, 95: 0, 84: 96, 96: 84, 230: 254}.get(q, q) for q in range(231)}
if (local / 'normalization.json').exists():
    assert normalization == {int(k): v for k, v in read_json(local / 'normalization.json').items()}
renumbering = {int(k): v for k, v in read_json(local / 'renumbering.json')['old_to_new'].items()}
assert oldstates == states230 - {79, 140}
assert len(oldstates) == len(normstates) == len(canstates) == 228
assert len(set(normalization.values())) == len(normalization)
assert len(set(renumbering.values())) == len(renumbering)
assert normhalt == 254 and oldhalt == 230 and canhalt == 228
assert (q0, qo, qn, qc) == (0, 0, 95, 0)
assert canstates == set(range(228))
assert normalized == {(normalization[q], b): (w, d, normalization[z])
                      for (q, b), (w, d, z) in old.items()}
assert canonical == {(renumbering[q], b): (w, d, renumbering[z])
                     for (q, b), (w, d, z) in old.items()}
assert normalization[qo] == qn and renumbering[qo] == qc
assert normalization[84] == 96 and renumbering[84] == 83

# Direct fresh dense-array simulation of both pinned release and canonical K228.
# Array bounds are explicitly checked on every read; zeros outside are exact.
def boot(rows, start, duration):
    tape = bytearray(4096)
    origin = 1024
    h = origin
    q = start
    lo = hi = 0
    for _ in range(duration):
        assert 0 <= h < len(tape)
        w, d, q = rows[q, tape[h]]
        tape[h] = w
        h += d
        lo = min(lo, h - origin)
        hi = max(hi, h - origin)
    assert 0 <= h < len(tape)
    return q, h - origin, [i - origin for i, bit in enumerate(tape) if bit], (lo, hi)


oldboot = boot(release, q0, 408419)
newboot = boot(canonical, qc, 409835)
startup = read_json(root / 'receipts/discovery/startup228_composed.json')
assert oldboot[:2] == (84, -5) and newboot[:2] == (83, -5)
assert oldboot[2] == newboot[2] == startup['one_cells']
ones = set(newboot[2])
assert len(ones) == 351 and min(ones) == -6 and max(ones) == 701
assert {p for p in ones if p < 176} == {-6}
assert 176 in ones
registers = []
pos = 177
while pos <= max(ones):
    assert pos not in ones and pos + 1 in ones
    end = pos + 1
    while end in ones:
        end += 1
    registers.append(end - pos - 2)
    pos = end
assert registers == [0, 0, 0, 3, 0, 0, 3, 0, 0] + [1] * 167
physical = [6, 2, 0, 4, 3, 7, 8, 5, 1]
assert [registers[j] for j in physical] == [3, 0, 0, 0, 3, 0, 0, 0, 0]
interpreter_check = (upstream / 'coq/tm/Interpreter230Check.v').read_text()
assert digest(upstream / 'coq/tm/Interpreter230Check.v') == '031a654d6b6ffdbfc000dd60bf219549abf8fc90af1e52432aee32764f01d08a'
assert 'nth r [6; 2; 0; 4; 3; 7; 8; 5; 1] 0' in interpreter_check

# Receipt pinning and exhaustive site/guard coverage.  This does not rerun the
# quantified symbolic engine; its rule soundness is independently audited.
if (runtime_dir / 'verification.json').exists():
    runtime = read_json(runtime_dir / 'verification.json')
    cases_path = runtime_dir / 'runtime_cases.json'
    assert runtime['status'] == 'K228_UNIVERSAL_MATHEMATICAL_PASS'
    assert runtime['machine_sha256'] == digest(local / 'k228.tm')
    assert runtime['source_sha256'] == digest(changed_path)
    assert runtime['original_sha256'] == digest(upstream / 'machine/k230.tm')
    assert runtime['engine_sha256'] == digest(root / 'verification/kernels/runtime_engine.py')
    assert runtime['helper_sha256'] == digest(root / 'verification/kernels/runtime_support.py')
    assert runtime['dense_startup_sha256'] == digest(runtime_dir / 'dense_startup.json')
    assert runtime['all_literal_rows_used'] is True
    portable_boot = read_json(runtime_dir / 'dense_startup.json')
    assert portable_boot['one_cells'] == newboot[2]
    assert portable_boot['canonical_steps'] == 409835 and portable_boot['head'] == -5
    receipt_mode = 'COMPLETE_PORTABLE_RUNTIME_REPLAY'
else:
    runtime = read_json(runtime_dir / 'runtime228_composed.json')
    cases_path = runtime_dir / 'runtime228_composed_cases.json'
    assert runtime['status'] == 'UNIVERSAL_MATHEMATICAL_PASS'
    assert runtime['table_sha256'] == digest(local / 'k228_normalized.tm')
    assert runtime['sites_sha256'] == digest(changed_path)
    # These are the retained discovery engines, rather than the later portable
    # modules whose import paths and inactive legacy entry points were cleaned.
    assert runtime['engine_sha256'] == digest(root / 'verification/kernels/symbolic_runtime.py')
    assert runtime['helper_sha256'] == digest(root / 'verification/kernels/independent_runtime.py')
    assert runtime['expected_cases'] == 6656 and runtime['all_rows_used'] is True
    receipt_mode = 'COMPLETE_DISCOVERY_RUNTIME_RECEIPT'
cases = read_json(cases_path)
assert runtime['cases_sha256'] == digest(cases_path)
assert [(c['index'], c['positive']) for c in cases] == [
    (i, positive) for i, (pc, op, arg) in enumerate(changed)
    for positive in ((False, True) if op == 'CD' else (False,))]
assert len(cases) == runtime['cases'] == 6656
assert sum(c['symbolic_steps'] for c in cases) == runtime['symbolic_steps'] == 1614426
assert all(len(c['duration']) == 13 and c['duration'][0] > 0
           and all(type(x) is int and x >= 0 for x in c['duration']) for c in cases)
assert set(map(tuple, runtime['used_rows'])) == set(normalized)
assert startup['new_sha256'] == digest(local / 'k228_normalized.tm')
assert startup['new_steps'] == 409835 and startup['final_state'] == 96 and startup['head'] == -5

receipt = {
    'status': 'INDEPENDENT_FINITE_INTERFACE_AND_BOOT_PASS',
    'source_coq_nodes': len(node_text),
    'source_leaves_original': len(original),
    'source_leaves_transformed': len(changed),
    'source_count_by_instruction': dict(Counter(op for pc, op, arg in changed)),
    'source_closed_root_bounds_height_break_continue': static_bounds(after),
    'replacement_paths': replacement_paths,
    'control_edges_no_stray_checked': control_edges,
    'outside_control_edges_preserved': outside_edges,
    'replacement_incoming_entry_counts_old_new': incoming,
    'canonical_sha256': digest(local / 'k228.tm'),
    'normalized_sha256': digest(local / 'k228_normalized.tm'),
    'source_sha256': digest(changed_path),
    'working_states': len(canstates),
    'rows': len(canonical),
    'canonical_start_dispatcher_halt': [qc, 83, canhalt],
    'independent_dense_boot_old_steps': 408419,
    'independent_dense_boot_new_steps': 409835,
    'old_boot_head_range': oldboot[3],
    'new_boot_head_range': newboot[3],
    'boot_final_head': -5,
    'boot_one_cells': 351,
    'boot_header_absolute': 176,
    'boot_gap_extra_above_64': 117,
    'boot_logical_registers': [registers[j] for j in physical],
    'boot_spare_count': 167,
    'runtime_guard_cases': len(cases),
    'runtime_receipt_mode': receipt_mode,
    'runtime_receipt_directory': str(runtime_dir.resolve().relative_to(root))
        if runtime_dir.resolve().is_relative_to(root) else str(runtime_dir.resolve()),
    'runtime_minimum_constant_duration': min(c['duration'][0] for c in cases),
    'runtime_maximum_symbolic_rule_count_per_case': max(c['symbolic_steps'] for c in cases),
    'scope': 'Independent finite interface, exact table conjugacy, receipt hashes, complete source/guard coverage, and fresh blank boot; quantified rule soundness and source equivalence are in the accompanying ordinary mathematical audit. No new Rocq endpoint.'
}
(output_dir / 'transfer_audit.json').write_text(json.dumps(receipt, indent=2) + '\n')
print(json.dumps(receipt, indent=2))
