#!/usr/bin/env python3
"""Owned final publication readback. Reads files and Git objects; runs no proofs."""
from pathlib import Path
from collections import Counter
import argparse, hashlib, json, re, subprocess

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
REL = Path('Computability/BusyBeaver/Research/ZFC/k225-formal/verification/k215/simplification')
PHASE = ROOT / REL / 'phase22'
PREVIOUS = ROOT / REL / 'phase21' / 'lean'
BASE = '0d335c25cf703d370ceee628a8cb0e722afa2ea0'
CORE = ['README.md', 'capture-config.json', 'capture.json', 'capture.py', 'check-plan.json',
        'check.py', 'evidence.tar.gz', 'index.json', 'result-review.json', 'result.json', 'review_actual.py']
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
read = lambda p: json.loads(Path(p).read_text())

def git_bytes(rel):
    return subprocess.check_output(['git', 'show', BASE + ':' + str(rel)], cwd=ROOT)

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--documents', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert not args.output.exists()
    spec = read(PHASE / 'integration/source-spec.json')
    plan = read(PHASE / 'lean/check-plan.json')
    result = read(PHASE / 'lean/result.json')
    assert sha(PHASE / 'lean/result.json') == 'cd966bd654b04a3c2becbafc00ba1f13f2866fcbab64b5b6715cf6449461dc66'
    assert sha(PHASE / 'lean/check-plan.json') == '76838519fc4b0faa756eedbe9dd1eab7ea500fc8130c5d4b69cc1435d7000070'
    assert result['status'] == 'PASS' and len(plan['modules']) == result['provider_count'] == 226
    assert (len(result['fresh_modules']), len(result['reused_modules']), len(result['audits'])) == (56, 170, 2)
    for row in plan['modules']:
        assert sha(row['source']) == row['source_sha256']
        if row['module'].startswith('BusyBeaver.'):
            canonical = ROOT / 'Computability/BusyBeaver/Lean' / Path(*row['module'].split('.')).with_suffix('.lean')
            assert sha(canonical) == row['source_sha256'], canonical
    for row in spec['sources']:
        assert sha(row['canonical']) == sha(row['candidate']['path']) == row['candidate']['sha256']
        assert sha(row['before']['path']) == row['before']['sha256']
    assert len(spec['sources']) == 9
    assert len(plan['present_inputs']) == 68 and len(plan['absent_inputs']) == 16
    for p, h in plan['present_inputs'].items():
        assert sha(p) == h, p
    for p in plan['absent_inputs']:
        assert not Path(p).exists() and not Path(p).is_symlink(), p
    previous_pins = {}
    for name in CORE:
        p = PREVIOUS / name
        assert p.read_bytes() == git_bytes(p.relative_to(ROOT)), p
        previous_pins[name] = sha(p)
    machine_pins = {}
    for suffix in ['candidate-k215/k215.tm', 'candidate-k215/k215.native.tm',
                   'candidate-k215/sites215.json', 'k225-formal/generate_l2dom.py']:
        p = ROOT / 'Computability/BusyBeaver/Research/ZFC' / suffix
        assert p.read_bytes() == git_bytes(p.relative_to(ROOT)), p
        machine_pins[suffix] = sha(p)
    for name, status in [('source-peer.json', 'PASS_INDEPENDENT_FINAL_SOURCE_SPEC_CANONICAL_INTERFACE_AND_REPORT_READBACK'),
                         ('capture-review.json', 'PASS_INDEPENDENT_ARCHIVE_INDEX_AND_REQUIRED_COVERAGE_REVIEW')]:
        assert read(PHASE / 'integration' / name)['status'] == status
    capture = read(PHASE / 'lean/capture.json')
    assert sha(PHASE / 'lean/evidence.tar.gz') == capture['archive_sha256']
    assert sha(PHASE / 'lean/index.json') == capture['index_sha256']
    assert (capture['blob_members'], capture['logical_entries'], capture['source_aliases'], capture['raw_plan_files']) == (443, 719, 713, 563)
    assert capture['preserved_failed_contexts'] == 2 and capture['external_boundary_files'] == 11
    helper = read(PHASE / 'integration/helper-axioms/result.json')
    assert helper['profiles'] == [['SetTheory.BusyBeaver.ZFC.ProfileSyntax.iff_congr_iff', []]]
    for key, name in [('record_sha256', 'record.json'), ('source_sha256', 'ConstructiveCongruenceAudit.lean'), ('log_sha256', 'compiler.log')]:
        assert sha(PHASE / 'integration/helper-axioms' / name) == helper[key]
    metrics = read(PHASE / 'integration/metrics.json')
    assert metrics['source_savings'] == {'lines': 179, 'bytes': 10782}
    for row in metrics['sources']:
        for key in ['before', 'after']:
            b = Path(row[key]['path']).read_bytes()
            assert len(b) == row[key]['bytes'] and len(b.splitlines()) == row[key]['lines']
    links_checked = 0
    documents = read(args.documents)['documents']
    link_re = re.compile(r'(?<!!)\[[^\]]*\]\(([^)]+)\)')
    for row in documents:
        p = ROOT / row['canonical']
        assert sha(p) == row['candidate_sha256'], p
        current = Counter(link_re.findall(p.read_text()))
        old = Counter(link_re.findall(git_bytes(p.relative_to(ROOT)).decode())) if row['before_sha256'] else Counter()
        for link in (current - old):
            if '://' in link or link.startswith('#'):
                continue
            target = link.split('#', 1)[0].strip('<>')
            assert target and (p.parent / target).resolve().exists(), (p, link)
            links_checked += 1
    report = {'status': 'PASS_FINAL_CANONICAL_SOURCE_EVIDENCE_AND_DOCUMENT_LINK_READBACK',
              'auditor_sha256': sha(__file__), 'providers': 226, 'changed_sources': 9,
              'present_pins': 68, 'required_absences': 16,
              'phase21_leaf_pins_unchanged': previous_pins, 'machine_and_producer_pins_unchanged': machine_pins,
              'documents': len(documents), 'new_or_added_local_links_checked': links_checked,
              'compiler_or_captured_code_execution': False, 'goal_remains_active': True}
    args.output.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))

if __name__ == '__main__':
    main()
