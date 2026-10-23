"""Owned bounded source/raw history manifest; no code execution or object copying."""
from pathlib import Path
import argparse, hashlib, json
parser = argparse.ArgumentParser()
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
assert not args.out.exists()
allowed = {'.json', '.py', '.md', '.diff', '.patch', '.txt', '.lean', '.log', '.stdout', '.stderr'}
files = {}
def add(path, role):
    path = Path(path).absolute()
    assert path.is_file() and not path.is_symlink() and 'objects' not in path.parts
    assert path.suffix in allowed, path
    hashed = hashlib.sha256(path.read_bytes()).hexdigest()
    if str(path) in files: assert files[str(path)]['sha256'] == hashed
    else: files[str(path)] = {'path': str(path), 'sha256': hashed, 'role': role}

old = Path('/tmp/k215-phase23-sources-v1/source-spec-v1.json')
add(old, 'preserved_rejected_full_run_source_spec')
for row in json.loads(old.read_text())['sources']:
    for key in ['before', 'candidate']:
        if row[key] is not None:
            path = Path(row[key]['path'])
            assert hashlib.sha256(path.read_bytes()).hexdigest() == row[key]['sha256']
            add(path, 'preserved_rejected_full_run_source_snapshot')

groups = {
 '/tmp/k215-phase23-native': 'unadopted_native_v1_source_history',
 '/tmp/k215-phase23-native-v2': 'adopted_native_v2_source_and_census',
 '/tmp/k215-phase23-native-v2-peer': 'independent_native_review',
 '/tmp/k215-phase23-attempts': 'preserved_original_core_candidate_history',
 '/tmp/k215-phase23-attempts-peer': 'preserved_original_core_source_review',
 '/tmp/k215-phase23-warnings': 'warning_cleanup_source_and_caller_census',
 '/tmp/k215-phase23-core-repair-v1': 'preserved_first_math_repair_history',
 '/tmp/k215-phase23-core-repair-v2': 'final_equality_transport_repair_history',
 '/tmp/k215-phase24-attempt-lead': 'direct_extension_mathematical_followup',
 '/tmp/k215-phase23-source-peer': 'independent_source_reviews_and_censuses',
 '/tmp/k215-phase23-math-v1': 'preserved_unaccepted_focused_math_diagnostic',
 '/tmp/k215-phase23-math-v2': 'successful_focused_math_diagnostic_not_full_endpoint_basis',
 '/tmp/k215-phase23-check-draft': 'unexecuted_initial_helper_adaptation_history',
 '/tmp/k215-phase23-check-draft-v2': 'executed_owned_helper_adapter_runtime_and_review',
 '/tmp/k215-phase23-capture-draft-v1': 'preserved_stopped_source_preparation_history',
 '/tmp/k215-phase23-capture-draft-v2': 'unexecuted_capture_adaptation_history',
 '/tmp/k215-phase23-capture-draft-v3': 'owned_final_capture_helper_sources_and_review',
 '/tmp/k215-phase23-doc-draft-v2': 'preacceptance_documentation_draft_and_author_readback',
}
for directory, role in groups.items():
    directory = Path(directory); assert directory.is_dir(), directory
    for path in sorted(directory.rglob('*')):
        if path.is_file() and 'objects' not in path.parts and path.suffix in allowed:
            add(path, role)
for name in ['check_math.py', 'run_record.py', 'prepare_extras.py', 'source-adoption-v1.json', 'source-adoption-v2.json', 'preparation-history.json']:
    add(Path(__file__).parent / name, 'owned_integration_source_or_receipt')
for path in ['/tmp/k215-phase23-math-driver-peer.json', '/tmp/k215-phase23-repair-annotations-peer.json', '/tmp/k215-phase23-capture-tools-peer.json']:
    add(path, 'independent_helper_or_source_review_at_its_pinned_version')
with args.out.open('x') as stream:
    json.dump({'status': 'EXPLICIT_INERT_SOURCE_AND_RAW_HISTORY_EXTRAS', 'files': list(files.values()),
       'objects_included': False, 'compiler_execution': False,
       'scope': 'Bounded owned source packages and diagnostic source/log/record history. Historical paths are labels. Final full acceptance is separate.'}, stream, indent=2)
    stream.write('\n')
print(json.dumps({'files': len(files), 'manifest': str(args.out), 'sha256': hashlib.sha256(args.out.read_bytes()).hexdigest()}))
