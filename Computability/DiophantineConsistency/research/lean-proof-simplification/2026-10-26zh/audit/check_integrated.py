#!/usr/bin/env python3
"""Read-only source/patch/math audit. Not a Lean parser or kernel checker.

Default stdout JSON. No git, network, compiler, subprocess, imports of bundled
scripts, or source writes. --output is the only write, and must be explicit.
Run from any cwd: python3 -B audit/check_integrated.py
"""
from __future__ import annotations
import argparse
import hashlib
import itertools
import math
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PREFIX = 'Computability/DiophantineConsistency/Lean/DiophantineConsistency/'
PIN = '09d65a93c9df8684c1a226341d6a5120623d1cdb'

class AuditFailure(RuntimeError):
    pass

def require(ok, message):
    if not ok:
        raise AuditFailure(message)

def metrics(text):
    data = text.encode('utf-8')
    return {'physical_lines': len(text.splitlines()),
            'nonblank_lines': sum(bool(x.strip()) for x in text.splitlines()),
            'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}

def strip_comments(text):
    # Nested Lean comments; string literals are retained, never interpreted.
    out = []; i = 0; depth = 0; string = False
    while i < len(text):
        pair = text[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif string:
            out.append(text[i])
            if text[i] == '\\' and i + 1 < len(text): out.append(text[i+1]); i += 2
            else:
                if text[i] == '"': string = False
                i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out.extend(' ' * (end - i)); i = end
        else:
            if text[i] == '"': string = True
            out.append(text[i]); i += 1
    require(depth == 0 and not string, 'Unclosed comment/string in audited Lean source')
    return ''.join(out)

def norm(s):
    return re.sub(r'\s+', '', s)

DECL = re.compile(r'(?m)^(?P<prefix>(?:(?:private|protected|noncomputable)\s+)*)'
                  r'(?P<kind>theorem|lemma|def|abbrev|opaque|axiom|constant|structure|inductive)'
                  r'\s+(?P<name>[A-Za-z_][\w\'.]*)')

def declarations(text):
    clean = strip_comments(text)
    starts = list(DECL.finditer(clean)); result = {}
    for index, match in enumerate(starts):
        end = starts[index+1].start() if index+1 < len(starts) else len(clean)
        body = clean[match.start():end].strip()
        divider = body.find(':=')
        require(divider >= 0, 'Unsupported declaration syntax: ' + match['name'])
        require(match['name'] not in result, 'Duplicate declaration name: ' + match['name'])
        result[match['name']] = {'kind': match['kind'], 'private': 'private' in match['prefix'],
                                 'header': norm(body[:divider]), 'body': norm(body),
                                 'physical_lines': len(text[match.start():end].rstrip().splitlines())}
    return result

def import_lines(text):
    return re.findall(r'(?m)^import\s+(.+)$', strip_comments(text))

def context_commands(text):
    return [norm(x) for x in re.findall(
        r'(?m)^(?:namespace|end|open|variable|omit|include|set_option|attribute)\b[^\n]*', strip_comments(text))]

def inspect_source(before, after, name, changed_defs=(), added=(), removed=()):
    a = declarations(before); b = declarations(after)
    require(import_lines(before) == import_lines(after), name + ': import changes')
    require(context_commands(before) == context_commands(after), name + ': context/attribute/option changes')
    require(set(b) - set(a) == set(added), name + ': unexpected added declarations')
    require(set(a) - set(b) == set(removed), name + ': unexpected removed declarations')
    for deleted in removed:
        require(a[deleted]['private'], name + ': deleted public declaration')
    for key in set(a) & set(b):
        require(a[key]['header'] == b[key]['header'], name + ': changed declaration header ' + key)
        if a[key]['kind'] not in ('theorem', 'lemma') and key not in changed_defs:
            require(a[key]['body'] == b[key]['body'], name + ': changed definition body ' + key)
    for key in added:
        require(b[key]['kind'] in ('theorem', 'lemma'), name + ': new non-proof declaration')
    tokens = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', strip_comments(after))
    require(not tokens, name + ': prohibited trust/unsafe markers ' + str(tokens))
    return {'imports_preserved': True, 'existing_headers_preserved': True,
            'definitions_preserved_except': list(changed_defs),
            'context_commands_preserved': True, 'added_declarations': list(added),
            'removed_private_declarations': list(removed), 'forbidden_markers_absent': True,
            'before': metrics(before), 'after': metrics(after),
            'physical_line_saving': metrics(before)['physical_lines'] - metrics(after)['physical_lines'],
            'nonblank_line_saving': metrics(before)['nonblank_lines'] - metrics(after)['nonblank_lines']}

def patch_path(s):
    p = s.split('\t', 1)[0].strip()
    require(p.startswith(('a/', 'b/')), 'Unexpected patch path ' + p)
    p = p[2:]
    require(p.startswith(PREFIX) and '..' not in Path(p).parts, 'Unsafe/non-target patch path ' + p)
    return p

def parse_patch(text):
    lines = text.splitlines(keepends=True); result = []; i = 0
    while i < len(lines):
        require(lines[i].startswith('--- '), 'Unexpected patch record ' + lines[i].rstrip())
        old = patch_path(lines[i][4:]); i += 1
        require(i < len(lines) and lines[i].startswith('+++ '), 'Missing patch destination')
        new = patch_path(lines[i][4:]); i += 1
        require(old == new, 'Renames/additions/deletions not accepted in this audit')
        hunks = []
        while i < len(lines) and not lines[i].startswith('--- '):
            match = re.match(r'@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', lines[i])
            require(bool(match), 'Bad hunk header ' + lines[i].rstrip()); i += 1
            old_count = int(match[2] or 1); new_count = int(match[4] or 1)
            old_lines = []; new_lines = []
            while i < len(lines) and not lines[i].startswith(('@@ ', '--- ')):
                line = lines[i]; i += 1
                require(line[0] in ' +-','Unsupported diff line ' + line.rstrip())
                if line[0] in ' -': old_lines.append(line[1:])
                if line[0] in ' +': new_lines.append(line[1:])
            require(len(old_lines) == old_count and len(new_lines) == new_count, 'Hunk line count mismatch')
            hunks.append((int(match[1])-1, old_lines, new_lines))
        result.append((old, hunks))
    return result

def apply_patch_memory(state, patch):
    changed = []
    for path, hunks in parse_patch(patch):
        require(path in state, 'Patch baseline missing ' + path)
        lines = state[path].splitlines(keepends=True); cursor = 0
        for expected, old, new in hunks:
            # Exact whole-hunk matching, no context fuzz. Offset allowed for composition.
            positions = [p for p in range(cursor, len(lines)-len(old)+1) if lines[p:p+len(old)] == old]
            require(len(positions) == 1, 'Patch hunk needs exactly one exact match: ' + path)
            pos = positions[0]; lines[pos:pos+len(old)] = new; cursor = pos + len(new)
        state[path] = ''.join(lines); changed.append(path)
    return changed

VARIANTS = [
    {'name':'physical_order_iso', 'patch':'physical/patches/order_iso.patch',
     'files':{'WangTiles942PhysicalOrder.lean':'physical/candidate/order_iso/WangTiles942PhysicalOrder.lean'}},
    {'name':'physical_fin_pred', 'patch':'physical/patches/fin_pred.patch',
     'files':{'WangTiles942PhysicalOrder.lean':'physical/candidate/fin_pred/WangTiles942PhysicalOrder.lean'},
     'changed_defs':['nonStartIndex']},
    {'name':'physical_combined', 'patch':'physical/patches/combined.patch',
     'files':{'WangTiles942PhysicalOrder.lean':'physical/candidate/combined/WangTiles942PhysicalOrder.lean'},
     'changed_defs':['nonStartIndex']},
    {'name':'controller_coprime', 'patch':'controller/patches/controller_coprime_cardinality.patch',
     'files':{'ControllerAuxiliaryChoice.lean':'controller/proposed/ControllerAuxiliaryChoice.lean'}},
    {'name':'controller_hs_inline', 'patch':'controller/patches/controller_hs_inline.patch',
     'files':{'CurrentControllerData2011.lean':'controller/proposed/CurrentControllerData2011.lean'},
     'removed':['hs_mod_of']},
    {'name':'word_marker_tail', 'patch':'word/patches/marker_tail.patch',
     'files':{'CurrentWordTopBounds2011.lean':'word/candidates/CurrentWordTopBounds2011.lean'},
     'added':['word_marker_tail','tail_outer_bare_zero','convolution_marker_tail']},
]

def finite_sanity():
    support = set(range(951)) | set(range(960,986)) | {1004}
    bare = []; reflected = 0
    for h in range(1991,2011):
        survivors = [d for d in (18,1004,2020) if (h-d)%2011 in support]
        require(survivors == ([1004] if h == 2008 else []), 'Bare-tail collision mismatch')
        if survivors: bare.append({'field':h, 'offset':1004, 'source':1004})
        for p in range(986):
            source = h-1005+p
            require(986 <= source < 2011, 'Reflected source out of interval')
            require((source in support) == (h+p == 2009), 'Reflected support mismatch')
            reflected += 1
    require(1990-1005 in support, 'Sharp lower boundary counterexample lost')
    # Actual Start tile west=2: its complemented west bit7 at source985 is1.
    start_weight = 1 + 2**10 * (1 + 2 + 2**8*435 + 2**17*3 + 2**25)
    start_west_bit7 = (255-2)//2**7%2
    require(start_west_bit7 == 1 and 2*start_weight == 69752854530,
            'Actual Start lower-bound counterexample arithmetic failed')
    cyclic = 0
    for n in (1,2,3,7):
        modulus = n*2011
        for j in range(n):
            for h in range(1991,2011):
                for d in (18,1004,2020):
                    residue = ((j*2011+h-d)%modulus)%2011
                    require(residue == (h-d)%2011, 'Cyclic bare-residue mismatch')
                    if residue in support:
                        require(h == 2008 and d == 1004, 'Unexpected cyclic bare source')
                        require((j*2011+h-d)%modulus == j*2011+1004, 'Marker from wrong cell')
                    cyclic += 1
                for p in range(986):
                    actual = (j*2011+h-(1005-p))%modulus
                    require(actual == j*2011+(h-1005+p), 'Reflected source cell/wrap mismatch')
                    cyclic += 1
    coprime = 0
    for p in (2,3,5,7):
        for c0 in range(p,5*p,p):
            for t in range(c0):
                for b in range(c0):
                    if b%p == 0: continue
                    e = 1 if t%p == 0 else 0
                    a = (t-e*b)%c0
                    require(e <= 1 and 0 < a < c0 and a%p != 0, 'Boolean cardinality choice failed')
                    for n in range(5): require(math.gcd(a,p**n) == 1, 'Coprimality failed')
                    coprime += 1
    hs = []
    for modulus,b,k,bs,answer in [(47,37,26,6,29),(2011,1283,1995,1091,674),(120199,37435,114787,99283,36379)]:
        require(pow(b,2,modulus) == bs and (1+b*k+bs)%modulus == answer, 'Hs arithmetic mismatch')
        hs.append({'modulus':modulus,'result':answer})
    maps = []; total = 0
    for n in range(7):
        mono = 0; count = 0
        for f in itertools.product(range(n), repeat=n):
            count += 1
            if all(f[i] < f[i+1] for i in range(n-1)):
                mono += 1; require(f == tuple(range(n)), 'StrictMono endomap counterexample')
        require(mono == 1, 'Identity not unique in finite endomap enumeration')
        total += count; maps.append({'n':n,'endomaps':count,'strict_mono':mono})
    return {'scope':'Finite sanity checks only; not Lean elaboration or general proofs.',
            'word_reflected_position_cases':reflected,'word_bare_cases':60,
            'word_bare_survivors':bare,'word_cyclic_cases':cyclic,
            'word_lower_boundary_counterexample':{'N':1,'tile':'Start', 'dummy':0, 'marker':0,
                'field':1990,'position':0,'source':985,'source_digit':start_west_bit7,
                'actual_convolution':2*start_weight,'wrong_tail_formula':0},
            'coprime_cardinality_cases':coprime,'hs_numeric_checks':hs,
            'finite_endomaps_checked':total,'finite_endomaps_by_size':maps}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline-tree', type=Path, default=ROOT/'baseline',
                        help='Root containing repository-relative baseline files (read-only)')
    parser.add_argument('--output', type=Path, help='Explicit optional JSON output; otherwise stdout only')
    args = parser.parse_args()
    names = {f for variant in VARIANTS for f in variant['files']}
    baseline = {PREFIX+name:(args.baseline_tree/PREFIX/name).read_text(encoding='utf-8') for name in names}
    inventory = json.loads((ROOT/'evidence/main_inventory.json').read_text(encoding='utf-8'))
    indexed = {x['path']:x for x in inventory['files']}
    for path, content in baseline.items():
        require(path in indexed and metrics(content)['sha256'] == indexed[path]['sha256'],
                'Baseline does not match pinned source inventory: ' + path)
    source_state = json.loads((ROOT/'evidence/source_state.json').read_text(encoding='utf-8'))
    require(source_state['source_pin'] == PIN, 'Wrong source pin')
    core_source = (args.baseline_tree/PREFIX/'WangTiles942Core.lean').read_text(encoding='utf-8')
    require('def start : Tile := ⟨2, 435, 3, 1⟩' in core_source,
            'Start tile counterexample source changed')
    expected_patches = {v['patch'] for v in VARIANTS}
    delivered_patches = {str(p.relative_to(ROOT)) for d in ('physical','controller','word')
                         for p in (ROOT/d/'patches').glob('*.patch')}
    require(expected_patches == delivered_patches, 'Unexpected or missing per-candidate patches')
    require(not (ROOT/'controller/proposed/ControllerResidueLift.lean').exists(),
            'Withdrawn exists_coordinate candidate is still delivered')
    regression = (ROOT/'physical/candidate/PhysicalOrderRegressionChecks.lean').read_text(encoding='utf-8')
    require('⟨(abstractIndex j).val-1' in regression and 'omega⟩ := rfl' in regression,
            'Optional Fin.pred requires prepared original-constructor rfl regression')
    checks = {}; patched = {}
    for variant in VARIANTS:
        state = dict(baseline)
        paths = apply_patch_memory(state,(ROOT/variant['patch']).read_text(encoding='utf-8'))
        require(set(paths) == {PREFIX+f for f in variant['files']}, variant['name']+': patch target mismatch')
        item = {}
        for name, candidate in variant['files'].items():
            original = baseline[PREFIX+name]; proposed = (ROOT/candidate).read_text(encoding='utf-8')
            require(state[PREFIX+name] == proposed, variant['name']+': patch does not reconstruct candidate')
            item[name] = inspect_source(original,proposed,variant['name']+'/'+name,
                                       variant.get('changed_defs',()),variant.get('added',()),variant.get('removed',()))
        checks[variant['name']] = {'exact_patch_replay':True,'files':item,
                                  'physical_line_saving':sum(v['physical_line_saving'] for v in item.values()),
                                  'nonblank_line_saving':sum(v['nonblank_line_saving'] for v in item.values())}
        patched[variant['name']] = state
    # Proof-only core changes are disjoint. Richer word API and Fin.pred stay optional.
    plans = {'core':['physical_order_iso','controller_coprime','controller_hs_inline'],
             'core_plus_word':['physical_order_iso','controller_coprime','controller_hs_inline','word_marker_tail'],
             'core_plus_pred':['physical_fin_pred','physical_order_iso','controller_coprime','controller_hs_inline'],
             'all':['physical_fin_pred','physical_order_iso','controller_coprime','controller_hs_inline','word_marker_tail']}
    compositions = {}
    by_name = {v['name']:v for v in VARIANTS}
    for plan, variants in plans.items():
        state = dict(baseline)
        for name in variants: apply_patch_memory(state,(ROOT/by_name[name]['patch']).read_text(encoding='utf-8'))
        if 'physical_fin_pred' in variants:
            require(state[PREFIX+'WangTiles942PhysicalOrder.lean'] == patched['physical_combined'][PREFIX+'WangTiles942PhysicalOrder.lean'],
                    'Composed physical options differ from supplied combined candidate')
        changed = {p for p in baseline if state[p] != baseline[p]}
        compositions[plan] = {'variants':variants,'changed_files':sorted(changed),
                              'before_physical_lines':sum(metrics(baseline[p])['physical_lines'] for p in changed),
                              'after_physical_lines':sum(metrics(state[p])['physical_lines'] for p in changed),
                              'physical_line_saving':sum(metrics(baseline[p])['physical_lines']-metrics(state[p])['physical_lines'] for p in changed),
                              'exact_patch_composition':True}
    report = {'source_pin':PIN,'status':'PASS_SOURCE_PATCH_AND_FINITE_SANITY_ONLY',
              'lean_status':'NOT_RUN: no Lean elaboration, kernel, axiom or performance checks',
              'prior_proposal_compatibility':'Bounded documentary review only; see catalog. No theorem claims all prior patches were built together.',
              'baseline_targets_match_recorded_sha256':True,
              'withdrawn_exists_coordinate_candidate_absent':True,
              'metric_scope':'Complete affected production files, including all new and removed helpers; regression files and tooling accounted separately.',
              'prepared_uncompiled_physical_regression':metrics(regression),
              'variants':checks,'compositions':compositions,'finite_sanity':finite_sanity()}
    output = json.dumps(report,indent=2,ensure_ascii=False)+'\n'
    if args.output: args.output.write_text(output,encoding='utf-8')
    print(output,end='')

if __name__ == '__main__':
    try: main()
    except (AuditFailure, OSError, ValueError) as exc:
        print(json.dumps({'status':'FAIL','error':str(exc)},indent=2))
        raise SystemExit(1)
