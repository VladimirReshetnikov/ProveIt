#!/usr/bin/env python3
"""Read-only, offline integrated source checks. Prints JSON; never runs Lean.

--baseline accepts the repository root, Lean root, or module directory.
Default: sibling baseline/ (delivery) or upstream/ (working snapshot).
All comparisons are textual; they do not check Lean elaboration or soundness.
"""
from pathlib import Path
import argparse
import difflib
import hashlib
import json
import re
import sys

ROOT = Path(__file__).resolve().parent.parent
REL = Path('Computability/DiophantineConsistency/Lean/DiophantineConsistency')
PIN = '22e020937caa81d0cb72a4f63071d6c0bcc1eba9'
EXPECTED = {
    'WangTiles942RowStep.lean': 'f4b6f60e4dece143de6d45120c8aa8ae84691d50b1b888e6e0dcb0226f17f84b',
    'WangTiles942HeadBounds.lean': 'bed402c366871656a605ebef749451631c88b34ce57118fa6bea583fce700754',
}

def require(ok, reason):
    if not ok:
        raise ValueError(reason)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def locate(base):
    for directory in (base, base / 'DiophantineConsistency',
                      base / 'Lean/DiophantineConsistency', base / REL):
        if (directory / 'WangTiles942RowStep.lean').is_file():
            return directory
    return None

def signatures(text):
    return {m.group(1): m.group(0).split(':=', 1)[0]
            for m in re.finditer(r'(?m)^theorem (\w+)\b[\s\S]*?:=', text)}

def declaration(text, name):
    m = re.search(r'(?m)^(?:private )?theorem ' + re.escape(name) + r'\b', text)
    require(m is not None, 'Missing theorem ' + name)
    next_m = re.search(r'(?m)^(?:theorem|private theorem|/--|end )', text[m.end():])
    return text[m.start():m.end() + next_m.start() if next_m else len(text)]

def stats(text):
    return {'physical_lines': len(text.splitlines()),
            'nonblank_lines': sum(bool(s.strip()) for s in text.splitlines()),
            'utf8_bytes': len(text.encode())}

def proof_lines(text, names):
    total = 0
    for name in names:
        dec = declaration(text, name)
        require(':= by' in dec, 'Expected tactic body ' + name)
        total += stats(dec.split(':= by', 1)[1].strip())['nonblank_lines']
    return total

def uncomment(text):
    out = []
    depth = i = 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth:
                out.append(text[i])
            i += 1
    require(depth == 0, 'Unterminated block comment')
    return ''.join(out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path)
    args = parser.parse_args()
    roots = [args.baseline] if args.baseline else [ROOT / 'baseline', ROOT / 'upstream']
    base = next((found for root in roots if (found := locate(root)) is not None), None)
    require(base is not None, 'Pinned baseline missing; supply --baseline PATH')
    hashes = {name: sha((base / name).read_bytes()) for name in EXPECTED}
    require(hashes == EXPECTED, 'Pinned source hashes do not match')
    head_dir = 'strip/head_only' if (ROOT / 'strip/head_only').is_dir() else 'strip'
    configurations = [
        ('head', 'WangTiles942HeadBounds.lean', head_dir + '/patched', head_dir + '/WangTiles942HeadBounds.patch'),
        ('causality', 'WangTiles942RowStep.lean', 'row/candidate', 'row/receiver_causality.patch'),
        ('canonical', 'WangTiles942RowStep.lean', 'machine/patched', 'machine/canonical-row.patch'),
        ('combined', 'WangTiles942RowStep.lean', 'row/combined', 'row/combined/causality-and-canonical-row.patch'),
    ]
    metrics = {}
    candidates = {}
    for label, name, folder, patch_path in configurations:
        original = (base / name).read_text()
        candidate = (ROOT / folder / name).read_text()
        expected_diff = ''.join(difflib.unified_diff(original.splitlines(keepends=True),
             candidate.splitlines(keepends=True), fromfile='a/' + str(REL / name),
             tofile='b/' + str(REL / name)))
        require(expected_diff == (ROOT / patch_path).read_text(), label + ' patch is not exact source-to-candidate diff')
        before_sig, after_sig = signatures(original), signatures(candidate)
        require(all(after_sig.get(k) == v for k, v in before_sig.items()),
                label + ' changed an existing public signature')
        require(not re.search(r'\b(sorry|admit|axiom|native_decide)\b', uncomment(candidate)),
                label + ' introduces proof escape')
        before, after = stats(original), stats(candidate)
        metrics[label] = {'before': before, 'after': after,
                         'delta': {k: after[k] - before[k] for k in before},
                         'existing_public_signatures_preserved': len(before_sig),
                         'new_public_theorems': sorted(set(after_sig) - set(before_sig)),
                         'candidate_sha256': sha(candidate.encode()), 'exact_patch_diff': True}
        candidates[label] = candidate
    row = (base / 'WangTiles942RowStep.lean').read_text()
    old_causal = ['far_west_zero', 'far_east_zero', 'far_pass']
    old_canon = ['receiver_south', 'south_step']
    new_causal = ['receive_at_next_head', 'far_pass_or_finish']
    new_canon = ['receiver_tile', 'row_tile_eq_stepTile']
    for label, old_names, new_names in [
        ('causality', old_causal, new_causal), ('canonical', old_canon, new_canon),
        ('combined', old_causal + old_canon, new_causal + new_canon)]:
        before = proof_lines(row, old_names)
        after = proof_lines(candidates[label], old_names + new_names)
        metrics[label]['affected_proof_nonblank'] = {'before': before, 'after': after, 'delta': after - before}
    for name in new_causal:
        text = declaration(candidates['combined'], name)
        require('hTime' not in text and 'no_south438' not in text,
                name + ' unexpectedly depends on time or finish exclusion')
    require('no_south438' in declaration(candidates['combined'], 'far_pass'),
            'Combined far_pass lost derived finish exclusion')
    require('p < 215' not in candidates['combined'] and 'p ≠ 215' not in candidates['combined'],
            'Halt receiver target improperly excluded')
    # Check only the newly added import closure; unchanged pre-existing imports
    # are not re-audited. In particular, withdrawn proposal files are not inputs.
    visited = set()
    active = set()
    def visit(name):
        require(name != 'WangTiles942RowStep', 'New construction import reaches RowStep')
        require(name not in active, 'Local import cycle at ' + name)
        if name in visited:
            return
        active.add(name)
        text = (candidates['combined'] if name == 'WangTiles942RowStep'
                else (base / (name + '.lean')).read_text())
        for child in re.findall(r'(?m)^import DiophantineConsistency\.(\w+)', text):
            visit(child)
        active.remove(name)
        visited.add(name)
    visit('WangTiles942StepConstruction')
    require(hashes == {name: sha((base / name).read_bytes()) for name in EXPECTED},
            'Source changed during verification')
    report = {
        'status': 'PASS_TEXTUAL_INTEGRATED_CHECKS_NOT_LEAN_VERIFICATION', 'pin': PIN,
        'metrics': metrics, 'new_import_local_closure': sorted(visited),
        'distinct_existing_public_headers_preserved': 16,
        'all_retained_changes_physical_line_delta': metrics['head']['delta']['physical_lines'] + metrics['combined']['delta']['physical_lines'],
        'existing_public_theorem_headers_byte_identical': True,
        'causality_time_and_finish_independence_source_check': True,
        'canonical_and_combined_retain_derived_finish_exclusion': True,
        'baseline_hashes_unchanged': hashes,
        'withdrawn_proposals': [{'name': 'periodic marked-halting endpoint',
            'reason': 'Already implemented upstream in WangTiles942Soundness at commit 512e0f6a3; late comparison pin 1e2a853935a6155cbcf2aa199aaca51946c4fff9.',
            'status': 'WITHDRAWN_NOT_RECOMMENDED_NOT_PACKAGED'},
            {'name': 'absolute-value trace cleanup', 'reason': 'Exact duplicate found in final 21-manuscript exclusion corpus.',
             'status': 'WITHDRAWN_NOT_RECOMMENDED_NOT_PACKAGED'},
            {'name': 'first-failure boundary abstraction', 'reason': 'Exact duplicate found in final 21-manuscript exclusion corpus.',
             'status': 'WITHDRAWN_NOT_RECOMMENDED_NOT_PACKAGED'}],
        'compiler_install_network_or_publication_attempted': False,
        'limitations': ['No Lean elaboration, tactic execution, kernel acceptance, or axiom audit.',
                       'No hypothetical post-adoption source tree exists; physical deltas refer only to the pin.',
                       'Use combined patch when selecting both RowStep proposals: standalone patch context overlaps.'],
    }
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    try:
        main()
    except (ValueError, OSError) as error:
        sys.exit('FAIL: ' + str(error))
