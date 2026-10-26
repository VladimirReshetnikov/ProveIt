#!/usr/bin/env python3
"""Read-only source, exact-patch, and finite-sanity audit; NOT a Lean checker.

Run from any cwd with Python 3.9+: python3 -B audit/check_integrated.py
The default baseline is ../baseline, containing repository-relative source
paths. --baseline-tree overrides it. JSON goes to stdout. This script makes
no writes and runs no commands, compilers, network requests, or bundled code.
It uses explicit checks (not assert), so Python -O preserves every check.
"""
from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
PIN = '9f35798db4a63c25e435fca14d75931144657d7e'
COMPARISON_PIN = '91dce223cda86c0755b8a9b2504f84be04443fce'


class AuditFailure(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise AuditFailure(message)


def metrics(text):
    return {'physical_lines': len(text.splitlines()),
            'nonblank_lines': sum(bool(line.strip()) for line in text.splitlines()),
            'bytes': len(text.encode('utf-8')),
            'sha256': hashlib.sha256(text.encode('utf-8')).hexdigest()}


def strip_comments(text):
    """Preserve source offsets and newlines, including nested Lean comments."""
    out = []; i = 0; depth = 0; string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-':
                depth += 1; out.extend('  '); i += 2
            elif pair == '-/':
                depth -= 1; out.extend('  '); i += 2
            else:
                out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text):
                out.append(text[i+1]); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif pair == '/-':
            depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end-i)); i = end
        else:
            if text[i] == '"': string = True
            out.append(text[i]); i += 1
    require(depth == 0 and not string, 'Unclosed comment/string')
    return ''.join(out)


def norm(text):
    return re.sub(r'\s+', '', text)


PROOF = re.compile(r'(?m)^(?P<prefix>(?:(?:private|protected|noncomputable)\s+)*)'
                   r'(?P<kind>theorem|lemma)\s+(?P<name>[A-Za-z_][\w\'.]*)')


def proof_declarations(text):
    """Bounded parser for these files: top-level proofs, indented continuations.

    Not a general Lean parser. Any top-level non-comment line ends the previous
    declaration. Exact normalized non-proof scaffolding is compared separately,
    including structures, definitions, section/omit scopes, attributes, options,
    imports, and multiline command continuations.
    """
    clean = strip_comments(text)
    top = list(re.finditer(r'(?m)^\S[^\n]*', clean))
    proofs = {}
    for match in PROOF.finditer(clean):
        end = next((line.start() for line in top if line.start() > match.start()), len(clean))
        block = clean[match.start():end]
        divider = block.find(':=')
        require(divider >= 0, 'Unsupported proof syntax: '+match['name'])
        require(match['name'] not in proofs, 'Repeated unqualified proof name: '+match['name'])
        proofs[match['name']] = {
            'start': match.start(), 'end': end, 'body_start': match.start()+divider+2,
            'private': 'private' in match['prefix'].split(),
            'header': norm(block[:divider]), 'body': norm(block[divider+2:]),
            'physical_lines': len(text[match.start():end].rstrip().splitlines())}
    return clean, proofs


def scaffold(clean, proofs, omit=()):
    chunks = []; cursor = 0
    for name, proof in proofs.items():
        chunks.append(clean[cursor:proof['start']])
        if name not in omit:
            chunks.extend((clean[proof['start']:proof['body_start']], '<PROOF:'+name+'>'))
        cursor = proof['end']
    chunks.append(clean[cursor:])
    return norm(''.join(chunks))


def inspect_source(before, after, label, added=(), removed=(), changed=()):
    ac, a = proof_declarations(before); bc, b = proof_declarations(after)
    require(set(b)-set(a) == set(added), label+': unexpected added proofs')
    require(set(a)-set(b) == set(removed), label+': unexpected removed proofs')
    for name in removed:
        require(a[name]['private'], label+': removed public proof '+name)
    actual_changed = []
    for name in set(a) & set(b):
        require(a[name]['header'] == b[name]['header'], label+': changed proof header '+name)
        if a[name]['body'] != b[name]['body']: actual_changed.append(name)
    require(set(actual_changed) == set(changed), label+': unlisted/unchanged proof-body edit')
    require(scaffold(ac, a, removed) == scaffold(bc, b, added),
            label+': changed non-proof code, context, attribute, option, or import')
    forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', bc)
    require(not forbidden, label+': forbidden trust/unsafe marker '+str(forbidden))
    return {'existing_headers_preserved': True, 'all_nonproof_code_and_context_preserved': True,
            'definitions_structures_imports_and_outer_options_omit_scopes_preserved': True,
            'added_proofs': sorted(added), 'removed_private_proofs': sorted(removed),
            'changed_proof_bodies': sorted(actual_changed), 'forbidden_markers_absent': True,
            'before': metrics(before), 'after': metrics(after),
            'physical_line_saving': metrics(before)['physical_lines']-metrics(after)['physical_lines'],
            'nonblank_line_saving': metrics(before)['nonblank_lines']-metrics(after)['nonblank_lines']}


def patch_path(value):
    path = value.split('\t', 1)[0].strip()
    require(path.startswith(('a/', 'b/')), 'Unexpected patch path '+path)
    path = path[2:]
    require(path.startswith(PREFIX) and '..' not in Path(path).parts,
            'Unsafe or non-target patch path '+path)
    return path


def parse_patch(text):
    lines = text.splitlines(keepends=True); result = []; i = 0
    while i < len(lines):
        require(lines[i].startswith('--- '), 'Unexpected patch record '+lines[i].rstrip())
        old = patch_path(lines[i][4:]); i += 1
        require(i < len(lines) and lines[i].startswith('+++ '), 'Missing patch destination')
        new = patch_path(lines[i][4:]); i += 1
        require(old == new, 'Patch renames/additions/deletions are unsupported')
        hunks = []
        while i < len(lines) and not lines[i].startswith('--- '):
            match = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
            require(match is not None, 'Bad hunk header '+lines[i].rstrip()); i += 1
            old_count = int(match[2] or 1); new_count = int(match[4] or 1)
            old_lines = []; new_lines = []
            while i < len(lines) and not lines[i].startswith(('@@ ', '--- ')):
                line = lines[i]; i += 1
                require(bool(line) and line[0] in ' +-', 'Unsupported diff line '+line.rstrip())
                if line[0] in ' -': old_lines.append(line[1:])
                if line[0] in ' +': new_lines.append(line[1:])
            require(len(old_lines) == old_count and len(new_lines) == new_count,
                    'Hunk line-count mismatch')
            hunks.append((int(match[1])-1, old_lines, new_lines))
        require(bool(hunks), 'Empty file patch')
        result.append((old, hunks))
    require(bool(result), 'Empty patch')
    return result


def apply_patch_memory(state, patch):
    changed = []
    for path, hunks in parse_patch(patch):
        require(path in state, 'Patch baseline missing '+path)
        lines = state[path].splitlines(keepends=True); cursor = 0
        for expected, old, new in hunks:
            # No context fuzz; offsets alone may change under composition.
            positions = [p for p in range(cursor, len(lines)-len(old)+1)
                         if lines[p:p+len(old)] == old]
            require(len(positions) == 1, 'Hunk lacks one unique exact match: '+path)
            pos = positions[0]; lines[pos:pos+len(old)] = new; cursor = pos+len(new)
        state[path] = ''.join(lines); changed.append(path)
    require(len(changed) == len(set(changed)), 'Repeated patch target')
    return changed


def finite_sanity():
    """Independent bounded arithmetic controls, never a proof of Lean elaboration."""
    def divides(m, value):
        return value == 0 if m == 0 else value % m == 0

    def power_eq_one(g, k, modulus):
        # ZMod 0 is the integers, not arithmetic modulo zero.
        return g**k == 1 if modulus == 0 else pow(g, k, modulus) == 1 % modulus

    cast_cases = 0
    for g in range(1, 18):
        for modulus in range(19):
            for k in range(9):
                require(power_eq_one(g, k, modulus) == divides(modulus, g**k-1),
                        'Guarded natural power-cast equivalence failed')
                cast_cases += 1
    require(not power_eq_one(0, 1, 2) and divides(2, max(0**1-1, 0)),
            'Missing-g>=1 counterexample no longer works')

    def order_of_power(x, k, modulus):
        if modulus == 0:
            return 1 if x**k == 1 else 0
        value = pow(x, k, modulus)
        if math.gcd(value, modulus) != 1: return 0
        power = 1 % modulus
        for order in range(1, modulus+1):
            power = power*value % modulus
            if power == 1 % modulus: return order
        raise AuditFailure('Finite unit order not found')

    crt_cases = 0; zero_factor_cases = 0
    for a in range(13):
        for b in range(13):
            if math.gcd(a, b) != 1: continue
            for x in range(10):
                for k in range(6):
                    actual = order_of_power(x, k, a*b)
                    expected = math.lcm(order_of_power(x, k, a), order_of_power(x, k, b))
                    require(actual == expected, 'CRT order product failed')
                    crt_cases += 1
                    zero_factor_cases += int(a == 0 or b == 0)

    auxiliary = 120199; d = 47*2011; exponent = 94517*(auxiliary-1)
    require(all(auxiliary % divisor for divisor in range(2, math.isqrt(auxiliary)+1)),
            'Auxiliary is not prime')
    require(pow(2, exponent, auxiliary**2) == 7300767062,
            'Literal auxiliary lift mismatch')
    require(7300767062 == 1+auxiliary*60739 and 0 < 60739 < auxiliary,
            'Lift witness digit mismatch')
    order_instances = []
    for k in range(5):
        modulus = d*auxiliary**(k+1)
        generator = pow(2, exponent, modulus)
        expected_order = auxiliary**k
        require(pow(generator, expected_order, modulus) == 1, 'Full-order power failed')
        if k:
            require(pow(generator, auxiliary**(k-1), modulus) != 1,
                    'Prime-power proper-divisor order exclusion failed')
        require(generator % (d*auxiliary) == 1, 'Full block projection failed')
        require((d*auxiliary)*auxiliary**k == modulus, 'Modulus factorization failed')
        order_instances.append({'k': k, 'modulus': modulus, 'expected_order': expected_order})

    mask_cases = 0; mask_guard_cases = 0
    multiples = (0, 1, 2, 7, 10**6, 10**30, 2**100)
    for residue in range(2048):
        for multiplier in multiples:
            x = 2048*multiplier+residue
            require((x & 8) == (residue & 8), 'Bit3 residue invariance failed')
            if x % 2048 <= 5:
                require((x & 8) == 0, 'Guarded bit3 clearance failed')
                mask_guard_cases += 1
            mask_cases += 1
    require((8 & 8) != 0 and 8 % 2048 > 5, 'Missing-residue-bound control failed')

    coprime_cases = 0
    for x in range(513):
        if math.gcd(x, 47) == 1:
            require(x > 0, 'Coprimality with 47 failed to imply natural positivity')
            coprime_cases += 1
    require(math.gcd(0, 47) == 47 and math.gcd(0, 1) == 1,
            'Coprimality nontrivial-modulus controls failed')
    return {'scope': 'Bounded independent arithmetic sanity only; not general proof or Lean validation.',
            'guarded_power_cast_cases': cast_cases,
            'guarded_power_cast_edges': ['m=0 (integers)', 'm=1', 'g=1', 'k=0'],
            'missing_g_ge_one_counterexample': {'g': 0, 'k': 1, 'm': 2,
                'cast_power_equals_one': False, 'm_divides_natural_truncated_subtraction': True},
            'crt_order_cases': crt_cases, 'crt_zero_factor_cases': zero_factor_cases,
            'literal_prime_power_order_instances': order_instances,
            'literal_lift_witness': {'prime': auxiliary, 'residue_mod_prime_square': 7300767062,
                                     'nonzero_lift_digit': 60739},
            'bit3_residue_representatives': mask_cases, 'bit3_guard_satisfying_cases': mask_guard_cases,
            'bit3_no_guard_counterexample': 8,
            'natural_coprime47_positive_cases': coprime_cases,
            'coprime1_does_not_imply_positive': {'x': 0, 'gcd_0_1': 1}}


def exact_scope_controls(baseline):
    power = (ROOT/'power/proposed/CurrentPowerCoordinates2011.lean').read_text(encoding='utf-8')
    prime = (ROOT/'power/proposed/PrimePowerOrder.lean').read_text(encoding='utf-8')
    units = (ROOT/'units/candidates/CurrentControllerUnits2011.lean').read_text(encoding='utf-8')
    masks = (ROOT/'masks/candidates/CurrentWordPadding2011.lean').read_text(encoding='utf-8')
    pc, pp = proof_declarations(power)
    _, qp = proof_declarations(prime)
    uc, up = proof_declarations(units)
    mc, mp = proof_declarations(masks)
    require('[NeZero' not in qp['pow_cast_eq_one_iff']['header'],
            'Unintended nonzero-modulus hypothesis in generic cast equivalence')
    require('(hg:1≤g)' in qp['pow_cast_eq_one_iff']['header'], 'Lost natural subtraction guard')
    require('[NeZero' not in pp['order_product']['header'], 'Lost zero-factor CRT scope')
    require('order_transport' not in pc, 'Deleted transport helper still referenced')
    require('generator_cast_C0' not in pp['full_order']['body'], 'Cyclic full_order/C0 dependency')
    require(pp['full_order']['start'] < pp['generator_cast_C0']['start'], 'Order dependency reversed')
    require(len(re.findall(r'\bGamma_pos\b', uc)) == 1, 'Gamma_pos self-reference/cycle risk')
    require(up['coprime_Gamma_47']['start'] < up['Gamma_pos']['start'], 'Gamma dependency reversed')
    require('(hx:x%2048≤5)' in mp['bit3_clear_of_residue']['header'], 'Lost low-residue guard')
    require('omit[NeZero(N*2011)]in' in norm(mc), 'Existing omitted NeZero scope lost')
    for name in ('exists_coordinates', 'exists_base_power_coordinates'):
        _, old = proof_declarations(baseline[PREFIX+'CurrentPowerCoordinates2011.lean'])
        require(old[name]['body'] == pp[name]['body'], 'Changed equivalence/witness construction '+name)
    return {'unrestricted_modulus_m_including_zero_retained': True,
            'unrestricted_CRT_factors_including_zero_and_one_retained': True,
            'natural_subtraction_and_low_residue_guards_retained': True,
            'existing_omitted_NeZero_context_retained': True,
            'coordinate_equivalence_and_base_power_witness_bodies_unchanged': True,
            'no_remaining_deleted_helper_reference': True,
            'k_zero_specialization_dependency_acyclic': True,
            'Gamma_pos_dependency_acyclic': True,
            'optional_Gamma_pos_dependency_tradeoff':
                'Now depends on literal-K modular certificates through coprime_Gamma_47; not recommended when elementary-positivity independence is preferred.'}


def late_source_binding(baseline_tree):
    record = json.loads((ROOT/'catalog/late91dce/candidate_binding.json').read_text(encoding='utf-8'))
    require(record['source_pin'] == PIN and record['final_comparison_pin'] == COMPARISON_PIN,
            'Wrong late-boundary source/comparison pins')
    require(len(record['records']) == 19 and record['all_identical'],
            'Incomplete/nonidentical late-boundary source binding')
    seen = set()
    for item in record['records']:
        path = item['path']
        require(path.startswith(PREFIX) and '..' not in Path(path).parts and path not in seen,
                'Unsafe or duplicate late-boundary source path')
        seen.add(path)
        require(item['byte_identical'] and item['old_git_blob'] == item['late_git_blob'],
                'Git-blob identity changed in late-boundary evidence: '+path)
        content = (baseline_tree/path).read_text(encoding='utf-8')
        require(metrics(content)['sha256'] == item['old_sha256'] == item['late_sha256'],
                'Late-boundary target/dependency baseline mismatch: '+path)
    return {'source_pin': PIN, 'comparison_pin': COMPARISON_PIN,
            'recorded_target_and_dependency_files': len(seen),
            'all_baseline_bytes_match_old_and_late_recorded_sha256': True,
            'old_and_late_recorded_git_blob_ids_equal': True,
            'scope': 'Checks supplied comparison receipts against baseline bytes; no remote fetch or independent git-object resolution.'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-tree', type=Path, default=ROOT/'baseline',
                        help='Root containing repository-relative baseline sources (read-only)')
    args = parser.parse_args()
    config = json.loads((ROOT/'audit/variants.json').read_text(encoding='utf-8'))
    require(config['source_pin'] == PIN, 'Unexpected proposal source pin')
    variants = config['variants']
    require(bool(variants), 'No candidate variants configured')
    require(len({v['name'] for v in variants}) == len(variants), 'Duplicate variant name')
    for variant in variants:
        for path in [variant['patch']] + [spec['candidate'] for spec in variant['files'].values()]:
            require(not Path(path).is_absolute() and '..' not in Path(path).parts,
                    'Unsafe artifact path '+path)
    inventory = json.loads((ROOT/'catalog/fresh_source_inventory.json').read_text(encoding='utf-8'))
    require(inventory['pin'] == PIN, 'Unexpected source inventory pin')
    indexed = {item['path']: item for item in inventory['sources']}
    names = {name for variant in variants for name in variant['files']}
    baseline = {PREFIX+name: (args.baseline_tree/PREFIX/name).read_text(encoding='utf-8')
                for name in names}
    for path, content in baseline.items():
        require(path in indexed and metrics(content)['sha256'] == indexed[path]['sha256'],
                'Baseline differs from pinned inventory: '+path)
    expected_patches = {variant['patch'] for variant in variants}
    delivered_patches = {str(path.relative_to(ROOT)) for family in ('power', 'masks', 'units')
                         for path in (ROOT/family/'patches').glob('*.patch')}
    require(expected_patches == delivered_patches, 'Missing or unexpected candidate patches')
    expected_candidates = {spec['candidate'] for variant in variants for spec in variant['files'].values()}
    delivered_candidates = {str(path.relative_to(ROOT)) for family in ('power', 'masks', 'units')
                            for dirname in ('candidate', 'candidates', 'proposed')
                            for path in (ROOT/family/dirname).glob('*.lean')}
    require(expected_candidates == delivered_candidates, 'Missing or unexpected full-file candidates')
    require(not (ROOT/'masks/patches/q_prefix.patch').exists(), 'Excluded q_prefix patch remains')
    checks = {}; by_name = {variant['name']: variant for variant in variants}
    for variant in variants:
        state = dict(baseline)
        paths = apply_patch_memory(state, (ROOT/variant['patch']).read_text(encoding='utf-8'))
        require(set(paths) == {PREFIX+name for name in variant['files']},
                variant['name']+': patch target mismatch')
        files = {}
        for name, spec in variant['files'].items():
            proposed = (ROOT/spec['candidate']).read_text(encoding='utf-8')
            require(state[PREFIX+name] == proposed, variant['name']+': candidate reconstruction mismatch')
            files[name] = inspect_source(baseline[PREFIX+name], proposed, variant['name']+'/'+name,
                                         spec.get('added', ()), spec.get('removed', ()), spec['changed'])
        checks[variant['name']] = {'exact_patch_replay': True, 'files': files,
                                  'physical_line_saving': sum(x['physical_line_saving'] for x in files.values()),
                                  'nonblank_line_saving': sum(x['nonblank_line_saving'] for x in files.values())}
    compositions = {}
    for plan, selected in config['compositions'].items():
        require(all(name in by_name for name in selected), 'Unknown composition member')
        require(len(selected) == len(set(selected)), 'Repeated composition member')
        final_state = None; order_count = 0
        for order in itertools.permutations(selected):
            state = dict(baseline)
            for name in order:
                apply_patch_memory(state, (ROOT/by_name[name]['patch']).read_text(encoding='utf-8'))
            if final_state is None: final_state = state
            require(state == final_state, 'Composition depends on patch order: '+plan)
            order_count += 1
        changed = [path for path in baseline if final_state[path] != baseline[path]]
        compositions[plan] = {'variants': selected, 'all_orders_replayed': order_count,
                              'exact_patch_composition': True, 'changed_files': sorted(changed),
                              'physical_line_saving': sum(metrics(baseline[p])['physical_lines']-
                                                         metrics(final_state[p])['physical_lines'] for p in changed),
                              'nonblank_line_saving': sum(metrics(baseline[p])['nonblank_lines']-
                                                         metrics(final_state[p])['nonblank_lines'] for p in changed)}
    print(json.dumps({'source_pin': PIN, 'status': 'PASS_SOURCE_PATCH_AND_FINITE_SANITY_ONLY',
                      'lean_status': 'UNCOMPILED: no elaboration, kernel, axiom, or performance checks',
                      'baseline_targets_match_recorded_sha256': True,
                      'metric_scope': 'Complete affected production files; includes every added/removed helper. Regression/tooling files are separate.',
                      'prior_proposal_compatibility': 'Bounded documentary novelty review only; no claim that all prior Lean patches compile together.',
                      'variants': checks, 'compositions': compositions,
                      'exact_scope_controls': exact_scope_controls(baseline),
                      'late_boundary_source_binding': late_source_binding(args.baseline_tree),
                      'finite_sanity': finite_sanity()}, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    try:
        main()
    except (AuditFailure, OSError, ValueError, KeyError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, indent=2))
        raise SystemExit(1)
