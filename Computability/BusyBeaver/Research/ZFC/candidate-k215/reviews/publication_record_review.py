#!/usr/bin/env python3
"""Own read-only publication binding; no supplied imports or machine replay."""
from pathlib import Path
import gzip, hashlib, json, re

ROOT = Path('/home/codex/.codex/worktrees/ec20/Proofs')
C = ROOT / 'Computability/BusyBeaver/Research/ZFC/candidate-k215'
OUT = Path(__file__).resolve().parent
RUN = Path('/tmp/k215-fresh/run1')
sha = lambda b: hashlib.sha256(b).hexdigest()
read = lambda p: json.loads(p.read_bytes())

def need(x, reason):
    if not x:
        raise ValueError(reason)

pins = read(C / 'code/frozen-runtime-inputs.json')
actual = read(RUN / 'actual.json')
need(len(pins['files']) == 8, 'eight frozen inputs')
for row in pins['files']:
    raw = (C / row['source']).read_bytes()
    need(sha(raw) == row['sha256'] == actual['before'][row['copy']], row['source'])
    need(raw == (RUN / row['copy']).read_bytes(), 'copy identity ' + row['source'])
need(actual['before'] == actual['after'], 'unchanged original execution inputs')

index = read(C / 'verification/evidence-index.json')
need(len(index['files']) == 7, 'complete original actual archive')
for row in index['files']:
    stored = (C / row['stored']).read_bytes()
    need(sha(stored) == row['stored_sha256'] and len(stored) == row['stored_bytes'], 'stored identity')
    raw = gzip.decompress(stored) if row['gzip'] else stored
    need(sha(raw) == row['raw_sha256'] and len(raw) == row['raw_bytes'], 'raw identity')
    need(raw == (RUN / row['run_path']).read_bytes(), 'original run identity ' + row['run_path'])

for name in ['review.json', 'review.md', 'inspection.json', 'inspect.py',
             'actual-review.json', 'actual-review-freeze.json', 'review_actual.py']:
    need((C / 'reviews' / name).read_bytes() ==
         (Path('/tmp/k215-permuted-partial-peer') / name).read_bytes(), 'unchanged independent receipt ' + name)
for name in ['evidence/root-runner.py', 'verification/root-runner.py']:
    need((C / name).read_bytes() == Path('/tmp/k215-fresh/run.py').read_bytes(), 'original runner ' + name)
for name in ['source_language.py', 'build221.py']:
    need((C / 'code' / name).read_bytes() == (C / 'research/composition-allocation' / name).read_bytes(), 'portable helper ' + name)
need((C / 'source_language.py').read_bytes() == (C / 'code/source_language.py').read_bytes(), 'reconstruction helper')
need((C / 'provenance/permuted-commands/sections/source_calibration.tex').read_bytes() ==
     Path('/tmp/zfc-intake197/extracted/K216_Permuted_Commands_2026-10-21/sections/source_calibration.tex').read_bytes(), 'exact inherited calibration')

docs = ['README.md', 'proof.md', 'reproduction.md', 'NOTICE.md',
        'research/composition-allocation/README.md']
links = []
for name in docs:
    p = C / name
    for target in re.findall(r'\[[^\]]*\]\(([^)]+)\)', p.read_text()):
        if target.startswith(('http:', 'https:', 'mailto:', '#')):
            continue
        path = target.split('#', 1)[0]
        need((p.parent / path).exists(), 'local link ' + name + ' -> ' + target)
        links.append({'from': name, 'target': target})

held = Path('/tmp/k216-permuted-partial-composition')
need((C / 'research/composition-allocation/check_allocated.py').read_bytes() ==
     (held / 'check_allocated.py').read_bytes(), 'unchanged original entry checker')
need(read(C / 'research/composition-allocation/allocation210-run2/allocation.json')['status'] == 'PREFIX_FAIL', 'original global-only rejection preserved')
for rel in ['check_allocated-v1.py', 'check_allocated-v2.py', 'entry-review-v2.diff', 'entry-review-v3.diff']:
    need((C / 'research/composition-allocation' / rel).read_bytes() == (held / rel).read_bytes(), 'failure/correction history ' + rel)

prov = read(C / 'provenance.json')
need(prov['actual_record_sha256'] == sha((RUN / 'actual.json').read_bytes()), 'provenance actual')
need(prov['independent_actual_review_sha256'] == sha((C / 'reviews/actual-review.json').read_bytes()), 'provenance actual peer')
need(prov['prospective_peer_sha256'] == sha((C / 'reviews/review.json').read_bytes()), 'provenance prospective peer')
need(sha((C / 'README.md').read_bytes()) == '930db896401f9a6d4903cff8d7ab0292e2497273612d31130aa046f69f1ee31b', 'final README')
need(sha((C / 'proof.md').read_bytes()) == 'd9225f80806f7c44fb7d228ddd6677217648d6f655b336d671291ace00fb51d1', 'final proof')

reviewed = docs + ['provenance.json', 'reconstruct.py', 'code/check_source.py', 'code/fresh_check.py',
    'code/prepare_actual_view.py', 'code/source_language.py', 'code/build221.py',
    'code/frozen-runtime-inputs.json', 'verification/evidence-index.json',
    'verification/portable-preparation.json', 'reviews/review_actual.py',
    'provenance/permuted-commands/sections/source_calibration.tex', 'licenses/LICENSE.ProveIt']
result = {
    'status': 'PASS_FOCUSED_INDEPENDENT_FINAL_PUBLICATION_REVIEW',
    'reviewer': '/root/review_upstream_reflection',
    'role': 'Author of the earlier independent prospective and actual/blank audits; not the composition/allocation/publication author.',
    'scope': 'Full final README, proof, reproduction, notice, portable reconstruction/source-check/runtime wrapper/archive-view code read; exact archive and prior review bindings, attribution and local links. No supplied code, solver, symbolic runtime or machine replay in this publication review.',
    'findings': [],
    'ordinary_proof_review': [
        'The complete ordered source word and both guarded ordinal CFGs identify the source with the separately calibrated Source159 210 program for all natural register values.',
        'Literal local marker diagrams are conditioned on their incoming edges and compare with their own constructed unfolding, not the earlier accepted217 whole table on arbitrary tapes.',
        'Every guarded primitive has a finite positive affine duration; source-step induction and unbounded sum of positive clocks transfer both halt and divergence.',
        'The complete finite blank prefix reaches exactly the source calibration root N=4 with all other logical registers0, nonempty40 unit spares and zero exterior; the compiler handles that finite cutoff.',
        'The ordinary all-natural source/compiler theorem and inherited dominated-calculus refutation equivalence give the stated ZFC-provable equivalence without assuming Con(ZFC). No kernel, internal PA, absolute nonhalting or minimality claim is made.'
    ],
    'portable_code_review': [
        'fresh_check.py copies eight exact inputs, refuses existing output, preserves failures, checks the literal blank tuple and invokes only the unchanged leaf under360seconds; semantic PASS/count/hash checks supplement returncode. Independent saved-case/blank checking remains separate.',
        'check_source.py retains the reviewed prefix/entry reader, local81 lemma and explicit108 contexts; adds pinned reference word/two-CFG equality and complete partial-subtree identity. It does not run the allocator or primitive runtime.',
        'reconstruct.py uses deterministic pinned parent DAG/table recipes and an invertible complete canonical map. prepare_actual_view.py restores exact compressed bytes and inputs for the unchanged portable auditor.',
        'Historical global-prefix failure and both local-entry reviewer corrections are retained rather than rewritten; portable runtime wrapper is reviewed but has not been rerun.'
    ],
    'actual_summary': {'cases':6176, 'symbolic_rules':1698790, 'rows':430, 'minimum_duration_constant':6,
        'blank_steps':95714, 'native_dispatcher':84, 'canonical_dispatcher':83},
    'bounded_metadata_checks': {'original_input_copies':8, 'original_raw_archive_files':7,
        'local_markdown_links':len(links), 'exact_prior_receipts':7},
    'links':links,
    'read_file_sha256':{name:sha((C / name).read_bytes()) for name in reviewed},
    'reviewer_script_sha256':sha(Path(__file__).read_bytes())
}
(OUT / 'review.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({'status':result['status'], 'review_sha256':sha((OUT / 'review.json').read_bytes()),
                  'links':len(links), 'files_read':len(reviewed)}, indent=2))
