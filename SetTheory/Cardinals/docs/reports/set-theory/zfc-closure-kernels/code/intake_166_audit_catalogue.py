"""Read-only batch166 catalogue/placement audit, adapted from batch165.

--catalogue-root permits scratch preview texts. --preview explicitly permits
WRITE166SHA; final audits require the actual reconciliation commit. No supplied
verifier, proof compiler, version query, manifest interpretation or build runs.
"""
from collections import Counter
from pathlib import Path
import argparse
import hashlib
import io
import json
import re
import subprocess
import zipfile

REPORTS = Path('SetTheory/Cardinals/docs/reports')
HOST = REPORTS / 'set-theory/zfc-closure-kernels'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--repo', type=Path, required=True)
    parser.add_argument('--catalogue-root', type=Path)
    parser.add_argument('--write-sha', default='WRITE166SHA')
    parser.add_argument('--preview', action='store_true')
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    assert __debug__, 'Keep assertions enabled.'
    repo = args.repo.resolve()
    catalogue = args.catalogue_root.resolve() if args.catalogue_root else repo
    assert not args.output.resolve().is_relative_to(repo), 'Evidence output must be external.'
    assert not args.output.exists(), 'Do not overwrite a previous audit.'
    git = lambda *command: subprocess.check_output(['git', '-C', str(repo), *command])

    def authored(relative):
        path = catalogue / relative
        return path if path.exists() else repo / relative

    tex = authored(REPORTS / 'manifest.tex').read_text()

    def escaped(i):
        n, i = 0, i - 1
        while i >= 0 and tex[i] == '\\':
            n, i = n + 1, i - 1
        return n % 2 == 1

    def group(pos):
        while tex[pos].isspace():
            pos += 1
        assert tex[pos] == '{'
        start, depth, pos = pos + 1, 1, pos + 1
        while depth:
            if tex[pos] in '{}' and not escaped(pos):
                depth += 1 if tex[pos] == '{' else -1
            pos += 1
        return tex[start:pos - 1], pos

    entries = []
    for match in re.finditer(r'^\\entry\s*(?=\{)', tex, re.M):
        pos, entry = match.end(), []
        for _ in range(5):
            value, pos = group(pos)
            entry.append(value)
        entry[1] = entry[1].replace('\\', '')
        entry[2] = entry[2].replace('\\', '')
        entries.append(entry)
    assert len(entries) == 290
    paths = [x[1] for x in entries]
    assert len(set(paths)) == 290
    assert all((repo / REPORTS / x[1] / x[2]).is_file() for x in entries)
    categories = Counter(x.split('/')[0] for x in paths)
    readme = authored(REPORTS / 'README.md').read_text()
    counts = {m.group(1): int(m.group(2)) for m in re.finditer(r'^\| \[`([^`]+)/`\].*\| (\d+) \|$', readme, re.M)}
    assert dict(categories) == counts and sum(counts.values()) == 290
    tracked = git('ls-files', '-z', '--', str(REPORTS)).decode().split('\0')
    root = repo / REPORTS
    artifacts = {(repo / x).parent for x in tracked if x and Path(x).suffix in ('.tex', '.pdf')
                 and len((repo / x).relative_to(root).parts) > 1
                 and (repo / x).relative_to(root).parts[0] in categories}
    minimal = {x for x in artifacts if not any(parent in artifacts for parent in x.parents if parent != root)}
    normalized = {x.parent if x.name in ('article', 'figures') and (x.parent / 'README.md').is_file() else x for x in minimal}
    assert {str(x.relative_to(root)) for x in normalized} == set(paths)

    incoming = authored(Path('docs/incoming/README.md')).read_text()
    rows = re.findall(r'^\| (\d+) \|', incoming, re.M)
    assert len(rows) == len(set(rows)) and rows[-1] == '166'
    assert 'Seventy manuscripts' in tex
    assert 'seventy manuscripts' in authored(HOST / 'README.md').read_text()
    assert all('6619bd0002' in value for value in (tex, readme, incoming))
    if not args.preview:
        assert re.fullmatch(r'[0-9a-f]{10,40}', args.write_sha)
        assert all('WRITE166SHA' not in value and args.write_sha in value for value in (tex, readme, incoming))
        git('cat-file', '-e', args.write_sha + '^{commit}')
    else:
        assert args.write_sha == 'WRITE166SHA' or re.fullmatch(r'[0-9a-f]{10,40}', args.write_sha)

    host = repo / HOST
    prefixes = {int(m.group(1)) for path in host.rglob('*') if path.is_file() and (m := re.match(r'^(\d{2})-', path.name))}
    assert set(range(1, 71)).issubset(prefixes)
    mapping = json.loads((host / 'data/intake-166-placement.json').read_text())
    assert mapping['batch'] == 166 and mapping['host_source'] == 70
    placed = [x for x in mapping['files'] if x['disposition'] == 'place_unchanged']
    archived = [x for x in mapping['files'] if x['disposition'] == 'archive_only']
    assert (len(placed), len(archived), len(mapping['files'])) == (170, 21, 191)
    package = mapping['archive']
    assert not (repo / package['archive']).exists()
    raw = git('show', package['arrival'] + ':' + package['archive'])
    assert hashlib.sha256(raw).hexdigest() == package['archive_sha256']
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        assert len([i for i in archive.infolist() if not i.is_dir()]) == 191
        payloads = {x['archive_member']: archive.read(x['archive_member']) for x in mapping['files']}
    for x in mapping['files']:
        assert hashlib.sha256(payloads[x['archive_member']]).hexdigest() == x['sha256']
        if x['disposition'] == 'place_unchanged':
            assert (repo / x['target']).read_bytes() == payloads[x['archive_member']]
            assert git('show', '6619bd0002:' + x['target']) == payloads[x['archive_member']]
    # These eighteen pending archives predate the244 arrival. Later committed
    # additions are allowed; no unrelated archive is retired by this batch.
    queue = json.loads((host/'data/intake-165-queue-supplement.json').read_text())
    assert queue['current_pending_count'] == 18
    for q in queue['current_pending']:
        assert (repo/q['path']).is_file()
        assert git('hash-object','--no-filters','--',str(repo/q['path'])).decode().strip() == q['git_blob']
    candidate = repo/'Computability/BusyBeaver/Research/ZFC/candidate-compensated244'
    input_pairs = {
        'machine/zfc_compensated244.tm':'zfc_compensated244.tm',
        'machine/zfc_compensated244_old.tm':'zfc_compensated244_old.tm',
        'machine/renumbering.json':'renumbering.json',
        'machine/facts.json':'facts.json',
        'proof/contextual_fold.tex':'proof/contextual_fold.tex',
        'proof/independent_audit.tex':'proof/independent_audit.tex',
        'runtime/verify_local_stuttering.py':'code/verify_local_stuttering.py',
        'runtime/contextual_fold_proof.json':'evidence/contextual_fold_proof.json',
        'runtime/local-stuttering-audit.json':'evidence/local-stuttering-audit.json'}
    originals = {x['relative']:payloads[x['archive_member']] for x in mapping['files']}
    for source,target in input_pairs.items():
        assert (candidate/target).read_bytes() == originals[source]
    for path in [host/'intake-166.md',host/'intake-166-reproduction.md',candidate/'README.md']:
        text = path.read_text()
        assert 'PENDING' not in text
        for link in re.findall(r'\]\(([^)]+)\)', text):
            if link.startswith(('https://','http://','#')): continue
            target = link.split('#',1)[0]
            assert ' ' not in target and (path.parent/target).exists(), (path,link)
    assert (host/'article.tex').read_bytes() == git('show','6619bd0002:'+str(HOST/'article.tex'))
    recovery = json.loads((host/'data/intake-166-recovery.json').read_text())
    assert recovery['status'] == 'RECOVERED_AND_PLACED_BYTES_MATCH'
    assert recovery['files_recovered'] == 191 and recovery['placed_pairs_compared'] == 170
    portable = json.loads((host/'data/intake-166-portable-execution.json').read_text())
    full = json.loads((host/'data/intake-166-full-runtime-execution.json').read_text())
    result = json.loads((host/'data/intake-166-full-runtime-verification.json').read_text())
    brief = json.loads((host/'data/intake-166-portable-verification.json').read_text())
    assert all(e['returncode'] == 0 and not e['timed_out'] and e['semantic_postchecks'] == 'PASS' for e in [portable,full])
    assert brief['runtime_dependency_smoke_cases'] == 1 and not brief['full_runtime_replayed_in_this_invocation']
    assert result['status'] == 'PASS' and result['complete'] and result['positive_progress_checked']
    assert result['counts'] == {'cases':8391,'symbolic_rules':2315075}
    assert len(result['rows']) == 488 and result['minimum_steps'] == 13
    assert hashlib.sha256((host/'data/intake-166-full-runtime-verification.json').read_bytes()).hexdigest() == full['result_sha256']
    delivered = json.loads(originals['runtime/candidate_1_full_symbolic.json'])
    assert {k:v for k,v in result.items() if k!='seconds'} == {k:v for k,v in delivered.items() if k!='seconds'}
    retained = json.loads((host/'data/intake-166-retained-local-execution.json').read_text())
    assert retained['status'] == 'PASS_RETAINED_LOCAL_EVIDENCE' and len(retained['records']) == 4
    assert all(e['returncode']==0 and not e['timed_out'] for e in retained['records'])
    endpoint_path = repo/'Computability/BusyBeaver/Research/ZFC/results/compensated244-binary-verification.json'
    endpoint_sha = '313c078f066db3452a5e6cb37ef5b8dbb6b515f302a0350b9fd3c0f3ad4abf34'
    assert hashlib.sha256(endpoint_path.read_bytes()).hexdigest() == endpoint_sha
    endpoint = json.loads(endpoint_path.read_text())
    assert endpoint['status'] == 'PASS' and not endpoint['prepare_only']
    assert (endpoint['named_axiom_probes'], endpoint['callers']) == (6, 6)
    assert endpoint['warnings'] == {'source':0,'audit':0}
    assert endpoint['only_standard_axioms']
    assert len(endpoint['commands']) == 2
    assert all(c['exit_code'] == 0 and not c['timed_out'] for c in endpoint['commands'])
    assert (repo/'Computability/BusyBeaver/Research/ZFC/compensated244_binary.md').is_file()
    assert all('18 October 2026' in value for value in (tex, readme, incoming))
    review_pins = {
        'data/intake-166-independent-write-fidelity-review.json':'97cc0fdc0cf0d6b53c3459ac53cb208a399c6cb34a131edfd17f0e6525ff2f56',
        'data/intake-166-independent-full-runtime-review.json':'3c14eaaa6edd0b2fb7ad8b5de2a273b6de89523dbdfb6972925e144a24ca3f6f'}
    for name,digest in review_pins.items():
        assert hashlib.sha256((host/name).read_bytes()).hexdigest() == digest
    record = dict(status='PREVIEW_PASS' if args.preview else 'PASS', batch=166,
                  placement='6619bd0002', write=args.write_sha,
                  collection_reports=290, all_catalogued_roots_match=True,
                  categories=dict(categories), host_sources=70,
                  placed=170, archive_only_at_collection_placement=21, recovered=191,
                  exact_candidate_promoted_inputs=9,
                  source_archive_retired_and_recoverable=True,
                  eighteen_prior_queued_archives_unchanged=True,
                  base_article_unchanged=True, portable_smoke_cases=1,
                  full_cases=8391, full_rules=2315075, full_binary_rows=488,
                  retained_four_jobs_are_evidence_retention_not_additional_independent_engine=True,
                  subsequent_external_endpoint_date='18 October 2026',
                  subsequent_external_endpoint_record_sha256=endpoint_sha,
                  subsequent_external_endpoint_reports=6, subsequent_external_endpoint_callers=6,
                  subsequent_external_endpoint_warnings=0, internal_PA_open=True,
                  independent_added_reviews=review_pins,
                  endpoint_scope='Exact previously completed root PASS record and published note; no replay or new provider audit.',
                  proof_compiler_calls=0, pdf_build_or_visual_review_claimed=False,
                  scope='Catalogue structure, exact original/placed/candidate bytes, links and actual result scope; no supplied verifier replay or delivery-checksum manifest interpretation.')
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(record, indent=2) + '\n')
    print(json.dumps(record, indent=2))


if __name__ == '__main__':
    main()
