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
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
PIN = '9d9d1123b39927d30363f1dcd53c23f0575c30ee'
COMPARISON_PIN = '60fcb2a69b7f1fdd4c3592ea5f164223cad50abe'


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


def tokens(text):
    # Bounded lexical normalization: retain identifier boundaries and strings.
    return tuple(re.findall(r'"(?:\\.|[^"\\])*"|[^\W\d][\w\']*|[0-9]+|[^\s]', text))


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
            'header_tokens': tokens(block[:divider]), 'body_tokens': tokens(block[divider+2:]),
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
    return tokens(''.join(chunks))


def inspect_source(before, after, label, added=(), removed=(), changed=()):
    ac, a = proof_declarations(before); bc, b = proof_declarations(after)
    require(set(b)-set(a) == set(added), label+': unexpected added proofs')
    require(set(a)-set(b) == set(removed), label+': unexpected removed proofs')
    for name in removed:
        require(a[name]['private'], label+': removed public proof '+name)
    actual_changed = []
    for name in set(a) & set(b):
        require(a[name]['header_tokens'] == b[name]['header_tokens'], label+': changed proof header '+name)
        if a[name]['body_tokens'] != b[name]['body_tokens']: actual_changed.append(name)
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


def source_binding(baseline_tree):
    record = json.loads((ROOT/'evidence/git_source_bindings.json').read_text(encoding='utf-8'))
    require(record['source_pin'] == PIN, 'Wrong source-binding pin')
    require(record['count'] == len(record['files']) == 702, 'Incomplete source-binding inventory')
    seen = set(); bound = {}
    for item in record['files']:
        path = item['path']
        require(path.startswith('Computability/DiophantineConsistency/Lean/') and
                '..' not in Path(path).parts and path not in seen, 'Unsafe/duplicate source-binding path')
        seen.add(path)
        data = (baseline_tree/path).read_bytes()
        require(hashlib.sha256(data).hexdigest() == item['sha256'], 'Baseline SHA mismatch: '+path)
        blob = hashlib.sha1(b'blob '+str(len(data)).encode('ascii')+b'\0'+data).hexdigest()
        require(blob == item['git_blob_sha1'], 'Baseline Git blob mismatch: '+path)
        bound[path] = data.decode('utf-8')
    return bound, {'source_pin': PIN, 'recorded_Lean_files': len(seen),
                   'all_recorded_sha256_and_git_blob_sha1_match_baseline': True,
                   'scope': 'Checks supplied local commit-binding receipts against source bytes; not remote commit resolution, elaboration, or proof review of all files.'}


def late_source_binding(baseline_tree, candidate_paths):
    record = json.loads((ROOT/'catalog/late60fcb/source_binding.json').read_text(encoding='utf-8'))
    require(record['source_pin'] == PIN and record['comparison_cutoff'] == COMPARISON_PIN,
            'Wrong late source/comparison pin')
    require(record['all_four_targets_unchanged'] and record['selected_context_count'] == 15 and
            len(record['bindings']) == 19, 'Incomplete late comparison binding')
    seen = set(); targets = set()
    for item in record['bindings']:
        path = item['path']
        require(path.startswith('Computability/') and '..' not in Path(path).parts and path not in seen,
                'Unsafe/duplicate late-binding path')
        seen.add(path)
        require(item['unchanged'] and item['source_pin_blob'] == item['comparison_cutoff_blob'],
                'Changed late source/context blob: '+path)
        data = (baseline_tree/path).read_bytes()
        blob = hashlib.sha1(b'blob '+str(len(data)).encode('ascii')+b'\0'+data).hexdigest()
        require(blob == item['source_pin_blob'], 'Late-bound source/context byte mismatch: '+path)
        if item['role'] == 'target': targets.add(path)
        else: require(item['role'] == 'selected_dependency_or_context', 'Unknown late-binding role')
    require(targets == set(candidate_paths), 'Wrong late-bound candidate targets')
    return {'source_pin': PIN, 'comparison_cutoff': COMPARISON_PIN,
            'targets_bound_to_equal_old_and_late_blob_receipts': len(targets),
            'selected_dependency_or_context_files_bound': len(seen)-len(targets),
            'all_19_delivered_baseline_bytes_match_both_recorded_git_blobs': True,
            'scope': 'Selected target/context identity only, not unchanged full transitive closure, remote commit resolution, or compiled migration.'}


def documentary_binding(baseline, config):
    record = json.loads((ROOT/'catalog/novelty_decisions.json').read_text(encoding='utf-8'))
    require(record['pin'] == PIN and record['all_prior_outcomes_assumed_available'], 'Wrong novelty boundary')
    require(record['primary_saved_lines'] == 15 and record['optional_housekeeping_saved_lines'] == 2,
            'Wrong documentary savings boundary')
    expected = {spec['candidate']: (filename, variant['patch']) for variant in config['variants']
                for filename, spec in variant['files'].items()}
    seen = set()
    for item in record['decisions']:
        files = item['files']; candidate = files['candidate']['path']
        require(candidate in expected and candidate not in seen, 'Unbound/duplicate documentary candidate')
        seen.add(candidate); filename, patch = expected[candidate]
        require(files['patch']['path'] == patch, 'Documentary patch mismatch')
        contents = {}
        for role in ('source', 'candidate', 'patch'):
            path = files[role]['path']
            require(not Path(path).is_absolute() and '..' not in Path(path).parts, 'Unsafe documentary path')
            data = (ROOT/path).read_bytes()
            require(hashlib.sha256(data).hexdigest() == files[role]['sha256'], 'Documentary SHA mismatch: '+path)
            contents[role] = data.decode('utf-8')
            require(len(contents[role].splitlines()) == files[role]['lines'], 'Documentary line mismatch: '+path)
        require(contents['source'] == baseline[PREFIX+filename], 'Documentary source differs from baseline')
        require(len(contents['source'].splitlines())-len(contents['candidate'].splitlines()) == item['saved_lines'],
                'Wrong per-candidate documentary savings')
    require(seen == set(expected), 'Incomplete documentary candidate binding')
    return {'exact_source_candidate_patch_receipts_checked': len(seen),
            'all_prior_outcomes_assumed_available': True,
            'scope': 'Binds documentary decisions to the delivered bytes; does not independently mechanize the manuscript novelty review.'}


def exact_scope_controls(baseline, candidates):
    names = ('CurrentControllerPositions2011.lean', 'CurrentWordRephase2011.lean',
             'CurrentPackingRank2011.lean', 'NativePackingPopulation.lean')
    parsed = {n: proof_declarations(candidates[PREFIX+n]) for n in names}
    old = {n: proof_declarations(baseline[PREFIX+n]) for n in names}
    ps, pp = parsed[names[0]]; rs, rp = parsed[names[1]]
    ks, kp = parsed[names[2]]; ms, mp = parsed[names[3]]
    require('defauxiliary:ℕ:=120199' in norm(strip_comments(baseline[PREFIX+'CurrentControllerData2011.lean'])),
            'Literal auxiliary changed')
    require('defposition(k:ℕ)(j:ZMod(auxiliary^k)):ℕ:=2+(auxiliary-1)*j.val' in norm(ps),
            'Position definition changed')
    require('(hrw:rw<k)' in pp['optional_stride_lt']['header'], 'Lost strict stride bound')
    require('(k:ℕ)' in pp['position_budget']['header'], 'Lost k=0 domain')
    require('omit[NeZeroN]in' in norm(rs), 'Lost rephase N=0 omission')
    require('omit[NeZeroN]in' in norm(ks), 'Lost cube-bound N=0 omission')
    require('(hm:A&&&M=0)' in mp['disjoint_add_lt']['header'], 'Lost disjointness premise')
    require('(hA:A<2^u)(hM:M<2^u)' in mp['disjoint_add_lt']['header'], 'Lost strict block bounds')
    require('(hC:0<C)(hCF:C+F<qN)' in kp['rank_gt_twice_window']['header'], 'Lost physical rank domain')
    old_rephase = old[names[1]][1]['normalization_of_rotation_eq']['body']
    new_rephase = rp['normalization_of_rotation_eq']['body']
    marker = '·havehnew:=word_binaryRotation47W\'c'
    require(marker in old_rephase and marker in new_rephase, 'Missing modular-transport block')
    require(old_rephase.split(marker,1)[1] == new_rephase.split(marker,1)[1],
            'Changed ordinary-multiplier modular transport')
    marker = 'havehn:=hc.trans_le'
    require(old[names[2]][1]['rank_gt_twice_window']['body'].split(marker,1)[1] ==
            kp['rank_gt_twice_window']['body'].split(marker,1)[1], 'Changed rank lower bound/cast bridge')
    unchanged = {
        names[0]: ['optional_next_lt','optional_stride_lt','position_ne_three','cell_val','cell_injective','support_card','support_safe','cyclicSupport_safe'],
        names[1]: ['constructedWord_eq','normalization_rephase','marked_packing_rephase','packing_rephase'],
        names[2]: ['fourBlocks_cast','fourBlocks_ge_cube','fourBlocks_population','packing_rank_population'],
        names[3]: ['four_block_exact','mask_population','calibrated_population']}
    for filename, proofs in unchanged.items():
        for theorem in proofs:
            require(old[filename][1][theorem]['body'] == parsed[filename][1][theorem]['body'],
                    'Changed guard/witness/domain-sensitive body: '+filename+'/'+theorem)
    ds, dp = proof_declarations(baseline[PREFIX+'CurrentDummySafety2011.lean'])
    for name in ['safe_exponent_bounds','safe_increment_bound','safe_normalized_increment',
                 'exists_safe_normalized_increment','safe_rank_decrement']:
        require('(hnext:j.val+1<N)(htime:j.val+s<N)' in dp[name]['header'],
                'Missing original physical safety guards: '+name)
    return {'literal_auxiliary_120199_and_affine_position_definition_retained': True,
            'k_zero_and_strict_stride_domains_retained': True,
            'N_zero_omit_scopes_retained': True,
            'rank_and_mask_hypotheses_retained': True,
            'actual_dummy_safety_module_unchanged_and_guards_bound': True,
            'ordinary_multiplier_equality_not_substituted_for_modular_transport': True,
            'modular_transport_block_and_rank_cast_bridge_unchanged': True,
            'selected_witness_and_boundary_sensitive_bodies_unchanged': unchanged}


def dependency_pricing(baseline, candidates, variants):
    records = []
    for variant in variants:
        for filename, spec in variant['files'].items():
            bc, before = proof_declarations(baseline[PREFIX+filename])
            ac, after = proof_declarations(candidates[PREFIX+filename])
            for name in spec['changed']:
                qualified = lambda s: set(re.findall(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+", s))
                old_refs = qualified(bc[before[name]['body_start']:before[name]['end']])
                new_refs = qualified(ac[after[name]['body_start']:after[name]['end']])
                records.append({'file': filename, 'proof': name,
                    'new_qualified_identifier_spellings': sorted(new_refs-old_refs),
                    'removed_qualified_identifier_spellings': sorted(old_refs-new_refs)})
    return {'new_imports': 0, 'new_production_declarations': 0, 'removed_production_declarations': 0,
            'new_helper_lines': 0,
            'qualified_spelling_delta_scope': 'Lexical proof-body diagnostic only, not an elaborated dependency or axiom graph.',
            'proof_body_qualified_spelling_deltas': records,
            'prices': [
                {'variant': 'literal_affine_positions', 'cost': 'More explicit dependence on auxiliary=120199 and large numeral normalization in the budget and injectivity proofs. No new module or positivity-certificate dependency. No performance claim.'},
                {'variant': 'exact_rephase_fields', 'cost': 'Unfolds the same raw definition twice locally instead of proving one function equality. Same existing recurrence, decomposition, and modular transport dependencies.'},
                {'variant': 'direct_rank_growth', 'cost': 'Uses existing Nat.lt_two_pow_self at 3*u instead of u, plus existing power-multiplication rewriting. No new helper or theorem-layer dependency.'},
                {'variant': 'disjoint_add_housekeeping', 'cost': 'Same add/and/or identity and strict OR bound; only local equality bookkeeping is removed.'}],
            'lean_dependency_graph_axioms_and_runtime': 'UNMEASURED; no Lean execution'}


def finite_sanity():
    """Independent bounded arithmetic only, never Lean validation."""
    p = 120199; position_cases = 0; stride_cases = 0
    for k in range(7):
        q = p**k; big = p**(k+1)
        reps = sorted({0, q-1, q//2, min(1,q-1), min(2,q-1)})
        images = []
        for j in reps:
            pos = 2+(p-1)*j
            require(pos+q+p <= big+3, 'Affine position budget failed')
            require(pos+1 < big, 'Affine next-cell safety consequence failed')
            images.append(pos); position_cases += 1
            for rw in range(k):
                require(pos+p**rw < big, 'Physical stride safety failed')
                stride_cases += 1
        require(len(images) == len(set(images)), 'Affine injectivity failed')
    physical_cases = 0; stride_zero_cases = 0
    for N in range(13):
        for j in range(max(1,N)):
            for s in range(N+3):
                if j+1 < N and j+s < N:
                    require(4022 <= N*2011 and 2999+2011*j <= N*2011-1023 and
                            977+2011*(j+s) <= N*2011-1034, 'Physical exponent bounds failed')
                    physical_cases += 1; stride_zero_cases += int(s == 0)
    require(not (2999+2011 <= 2*2011-1023), 'Final-cell safety counterexample failed')
    require(not (977+2011*2 <= 2*2011-1034), 'Missing temporal bound counterexample failed')
    growth_cases = 0
    for u in range(257):
        require(2*u <= 3*u < 2**(3*u), 'Direct strict rank-growth arithmetic failed')
        growth_cases += 1
    disjoint_cases = 0
    for u in range(8):
        q = 2**u
        for A in range(q):
            for M in range(q):
                require(A+M == (A&M)+(A|M), 'Add/and/or identity failed')
                if A&M == 0:
                    require(A+M == A|M and A+M < q, 'Disjoint strict sum bound failed')
                    disjoint_cases += 1
    require(1 < 2 and not 1+1 < 2, 'Missing disjointness counterexample failed')
    require((2&0) == 0 and not 2+0 < 2, 'Missing strict representative bound counterexample failed')
    transport_cases = 0
    for n in range(1,8):
        modulus = 2**n-1
        for W in range(2*n+1):
            Wprime = W+n
            for source in range(1,min(2**n,33)):
                lhs = (7+2**Wprime)*source; rhs = (7+2**W)*source
                require(lhs % modulus == rhs % modulus, 'Cyclic multiplier congruence failed')
                require(lhs != rhs, 'Ordinary multipliers unexpectedly equal')
                transport_cases += 1
    require(2**1 != 2**4 and (2**4-2**1) % (2**3-1) == 0,
            'Ordinary-vs-modular counterexample failed')
    return {'scope': 'Bounded independent arithmetic sanity only; not general proof, tactic success, or Lean elaboration.',
            'literal_affine_position_cases': position_cases, 'physical_stride_cases': stride_cases,
            'position_edges': ['k=0 singleton', 'largest representative', 'unchanged downstream rw<k'],
            'physical_exponent_guard_cases': physical_cases, 'physical_stride_zero_cases': stride_zero_cases,
            'growth_bound_cases_including_u_zero': growth_cases, 'disjoint_sum_cases_including_u_zero': disjoint_cases,
            'cyclic_transport_congruence_cases_with_unequal_ordinary_products': transport_cases,
            'negative_controls': ['final cell breaks kernel exponent budget', 'dropping temporal position bound breaks temporal exponent budget',
                'overlapping bits can carry out of window', 'disjointness alone does not imply strict block bound',
                '2 and 16 are congruent modulo 7 but not equal']}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-tree', type=Path, default=ROOT/'baseline',
                        help='Root containing repository-relative baseline sources (read-only)')
    args = parser.parse_args()
    config = json.loads((ROOT/'audit/variants.json').read_text(encoding='utf-8'))
    require(config['source_pin'] == PIN, 'Unexpected proposal source pin')
    variants = config['variants']; alternatives = config['isolated_alternatives']
    require(len(variants) == 4 and len({v['name'] for v in variants}) == 4, 'Wrong/duplicate candidate variants')
    for variant in variants:
        for path in [variant['patch']] + [spec['candidate'] for spec in variant['files'].values()]:
            require(not Path(path).is_absolute() and '..' not in Path(path).parts, 'Unsafe artifact path '+path)
    for alt in alternatives:
        require(not Path(alt['patch']).is_absolute() and '..' not in Path(alt['patch']).parts, 'Unsafe alternative path')
    baseline, binding = source_binding(args.baseline_tree)
    expected_patches = {v['patch'] for v in variants} | {a['patch'] for a in alternatives}
    actual_patches = {str(p.relative_to(ROOT)) for family in ('safety','population','rephase')
                      for p in (ROOT/family/'patches').glob('*.patch')}
    require(expected_patches == actual_patches, 'Missing/unexpected proposal patch')
    expected_candidates = {spec['candidate'] for v in variants for spec in v['files'].values()}
    actual_candidates = {str(p.relative_to(ROOT)) for family in ('safety','population','rephase')
                         for dirname in ('candidate','candidates','proposed')
                         for p in (ROOT/family/dirname).glob('*.lean')}
    require(expected_candidates == actual_candidates, 'Missing/unexpected full-file candidate')
    checks = {}; candidates = {}; by_name = {v['name']: v for v in variants}
    for variant in variants:
        state = dict(baseline)
        paths = apply_patch_memory(state, (ROOT/variant['patch']).read_text(encoding='utf-8'))
        require(set(paths) == {PREFIX+n for n in variant['files']}, 'Wrong patch targets: '+variant['name'])
        files = {}
        for name, spec in variant['files'].items():
            proposed = (ROOT/spec['candidate']).read_text(encoding='utf-8')
            require(state[PREFIX+name] == proposed, 'Candidate reconstruction mismatch: '+variant['name'])
            files[name] = inspect_source(baseline[PREFIX+name], proposed, variant['name']+'/'+name,
                                        spec.get('added',()), spec.get('removed',()), spec['changed'])
            candidates[PREFIX+name] = proposed
        checks[variant['name']] = {'exact_patch_replay': True, 'files': files,
            'physical_line_saving': sum(f['physical_line_saving'] for f in files.values()),
            'nonblank_line_saving': sum(f['nonblank_line_saving'] for f in files.values())}
    isolated = {}
    filename = 'CurrentControllerPositions2011.lean'; _, combined = proof_declarations(candidates[PREFIX+filename])
    require({a['name'] for a in alternatives} == set(by_name['literal_affine_positions']['files'][filename]['changed']),
            'Wrong isolated alternatives')
    for alt in alternatives:
        state = dict(baseline)
        require(apply_patch_memory(state, (ROOT/alt['patch']).read_text(encoding='utf-8')) == [PREFIX+filename],
                'Wrong isolated target')
        check = inspect_source(baseline[PREFIX+filename], state[PREFIX+filename], alt['name'], changed=[alt['name']])
        _, one = proof_declarations(state[PREFIX+filename])
        require(one[alt['name']]['body'] == combined[alt['name']]['body'], 'Isolated/combined proof mismatch')
        isolated[alt['name']] = check
    compositions = {}
    for plan, selected in config['compositions'].items():
        require(all(n in by_name for n in selected) and len(selected) == len(set(selected)), 'Bad composition')
        final_state = None; order_count = 0
        for order in itertools.permutations(selected):
            state = dict(baseline)
            for name in order:
                apply_patch_memory(state, (ROOT/by_name[name]['patch']).read_text(encoding='utf-8'))
            if final_state is None: final_state = state
            require(state == final_state, 'Order-dependent composition: '+plan)
            order_count += 1
        changed = [p for p in baseline if final_state[p] != baseline[p]]
        compositions[plan] = {'variants': selected, 'exact_patch_orders_replayed': order_count,
            'changed_files': sorted(changed),
            'physical_line_saving': sum(metrics(baseline[p])['physical_lines']-metrics(final_state[p])['physical_lines'] for p in changed),
            'nonblank_line_saving': sum(metrics(baseline[p])['nonblank_lines']-metrics(final_state[p])['nonblank_lines'] for p in changed)}
    print(json.dumps({'source_pin': PIN, 'status': 'PASS_SOURCE_PATCH_AND_FINITE_SANITY_ONLY',
        'lean_status': 'UNCOMPILED: no elaboration, kernel, axiom, or performance checks',
        'metric_scope': 'Complete affected production files, including all helpers. Tools, reports, checks, and duplicate alternatives are not production savings.',
        'prior_proposal_compatibility': 'Bounded documentary novelty review only; no claim of cumulative Lean elaboration of all assumed-applied proposals.',
        'source_binding': binding, 'late_source_binding': late_source_binding(args.baseline_tree,candidates),
        'variants': checks, 'compositions': compositions,
        'isolated_alternatives': {'scope': 'Each checked against baseline and combined proof body. Alternatives to the combined safety patch, not a promise of arbitrary-order exact patch composition.', 'checks': isolated},
        'exact_scope_controls': exact_scope_controls(baseline,candidates),
        'dependency_pricing': dependency_pricing(baseline,candidates,variants),
        'finite_sanity': finite_sanity(),
        'documentary_boundary_binding': documentary_binding(baseline,config)}, indent=2, ensure_ascii=False))


if __name__ == '__main__':
    try:
        main()
    except (AuditFailure, OSError, ValueError, KeyError, IndexError, TypeError) as exc:
        print(json.dumps({'status': 'FAIL', 'error': str(exc)}, indent=2))
        raise SystemExit(1)
