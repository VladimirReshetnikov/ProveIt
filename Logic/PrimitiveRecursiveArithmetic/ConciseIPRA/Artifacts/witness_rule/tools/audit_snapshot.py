"""Verify the bundled historical source census without executing its code.

Run from any working directory with Python's standard library. This reads the
443 exact source byte strings under reference/corpus_sources and checks their
hashes and all recorded source metrics. It also verifies that the reviewed
boundary classification covers exactly the recorded coordinate frontier.

Classification is human/assistant review metadata: consistency checks here do
not prove that a file is a sound, complete iPRA checker. The original ZIP bytes
are not bundled or re-fetched by this script. No files are modified.
"""
from pathlib import Path
import ast
import gzip
import hashlib
import io
import json
import platform
import re
import sys
import tokenize
import zlib

ROOT = Path(__file__).resolve().parents[1]
EVIDENCE = ROOT / 'evidence'
SOURCES = ROOT / 'reference' / 'corpus_sources'
IGNORED_TOKENS = {
    tokenize.ENCODING, tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
    tokenize.DEDENT, tokenize.COMMENT, tokenize.ENDMARKER,
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text(encoding='utf-8'))


def metrics(raw):
    tree = ast.parse(raw)
    normalized = (ast.unparse(tree) + '\n').encode('utf-8')
    return {
        'bytes': len(raw),
        'gzip9_raw': len(gzip.compress(raw, compresslevel=9, mtime=0)),
        'ast_nodes': sum(1 for _ in ast.walk(tree)),
        'normalized_bytes': len(normalized),
        'gzip9_normalized': len(gzip.compress(normalized, compresslevel=9, mtime=0)),
        'tokens': sum(token.type not in IGNORED_TOKENS for token in
                      tokenize.tokenize(io.BytesIO(normalized).readline)),
        'imports': [ast.unparse(node) for node in tree.body
                    if isinstance(node, (ast.Import, ast.ImportFrom))],
        'public_driver': any(isinstance(node, ast.Call)
                             and isinstance(node.func, ast.Name)
                             and node.func.id == 'print'
                             for node in ast.walk(tree)),
    }


def main():
    census = read_json(EVIDENCE / 'recursive_corpus.json')
    reviewed = read_json(EVIDENCE / 'boundary_classification.json')
    frontier = read_json(EVIDENCE / 'frontier.json')
    require(census['snapshot'] == frontier['snapshot'], 'Snapshot identifiers disagree')
    rows = census['sources']
    by_hash = {row['sha256']: row for row in rows}
    require(len(by_hash) == len(rows), 'Repeated source hash in the census')
    require(len(rows) == census['distinct_python_count'], 'Source count disagrees')
    require(all(re.fullmatch(r'[0-9a-f]{64}', digest) for digest in by_hash),
            'Invalid SHA-256 source identifier')
    supplied = {path.name for path in SOURCES.glob('*.py') if path.is_file()}
    expected = {digest + '.py' for digest in by_hash}
    require(supplied == expected,
            'Bundled sources differ: missing=' + repr(sorted(expected - supplied))
            + ', extra=' + repr(sorted(supplied - expected)))

    computed = {}
    mismatches = []
    for digest, row in by_hash.items():
        raw = (SOURCES / (digest + '.py')).read_bytes()
        require(hashlib.sha256(raw).hexdigest() == digest,
                'Source SHA-256 mismatch: ' + digest)
        actual = metrics(raw)
        computed[digest] = actual
        for key, value in actual.items():
            if row.get(key) != value:
                mismatches.append({'sha256': digest, 'field': key,
                                   'recorded': row.get(key), 'actual': value})
    if mismatches:
        raise ValueError(json.dumps({
            'message': 'Historical-source measurements differ',
            'recorded_runtime': {'python': census['python'], 'zlib': census['zlib']},
            'current_runtime': {'python': platform.python_version(),
                                'zlib': zlib.ZLIB_RUNTIME_VERSION},
            'note': 'AST normalization and gzip can vary with the runtime.',
            'mismatch_count': len(mismatches), 'first_mismatches': mismatches[:20],
        }, indent=2))

    occurrence_count = sum(len(row['locations']) for row in rows)
    require(occurrence_count == census['python_source_occurrences_after_archive_dedup'],
            'Recorded source-location count disagrees')
    require(len(census['archives']) == census['distinct_archive_count'],
            'Recorded distinct-archive count disagrees')
    require(all(row['locations'] for row in rows), 'A source has no provenance location')

    minima = frontier['complete_checker_coordinate_minima']
    expected_boundary = {
        digest for digest, row in computed.items()
        if any(row[key] <= threshold for key, threshold in minima.items())
    }
    reviewed_by_hash = {row['sha256']: row for row in reviewed}
    require(len(reviewed_by_hash) == len(reviewed), 'Repeated boundary classification')
    require(set(reviewed_by_hash) == expected_boundary,
            'Reviewed boundary does not cover exactly the measured frontier candidates')
    for digest, row in reviewed_by_hash.items():
        require(row['classification'] in ('complete_checker', 'supporting_utility'),
                'Unknown boundary classification for ' + digest)
        require(bool(row.get('reason', '').strip()), 'Missing review rationale for ' + digest)
        for key, value in computed[digest].items():
            require(row.get(key) == value, 'Boundary metric mismatch: ' + digest + '/' + key)
        require(row['locations'] == by_hash[digest]['locations'],
                'Boundary provenance mismatch: ' + digest)

    complete = [computed[digest] for digest, row in reviewed_by_hash.items()
                if row['classification'] == 'complete_checker']
    helpers = len(reviewed) - len(complete)
    require(bool(complete), 'No complete checker is classified on the boundary')
    attained = {key: min(row[key] for row in complete) for key in minima}
    require(attained == minima, 'Complete-checker frontier is not attained as recorded')
    require(len(reviewed) == frontier['all_boundary_sources_classified'],
            'Boundary source count disagrees with frontier summary')
    require(len(complete) == frontier['complete_boundary_sources'],
            'Boundary complete-checker count disagrees')
    require(helpers == frontier['boundary_helpers_excluded'],
            'Boundary helper count disagrees')

    print(json.dumps({
        'status': 'PASS', 'snapshot': census['snapshot'],
        'source_hashes_verified': len(rows),
        'source_measurements_verified': len(rows),
        'provenance_location_count': occurrence_count,
        'direct_archives_recorded': len(census['direct_archives']),
        'distinct_archives_recorded': census['distinct_archive_count'],
        'original_zip_bytes_rechecked': False,
        'boundary_records_verified': len(reviewed),
        'reviewed_complete_checkers': len(complete),
        'reviewed_supporting_utilities': helpers,
        'attained_coordinate_minima': attained,
        'python': platform.python_version(), 'zlib': zlib.ZLIB_RUNTIME_VERSION,
        'historical_source_executed': False, 'files_modified': False,
        'classification_scope': 'Review metadata coverage and consistency, not an automated soundness proof.',
    }, indent=2))


if __name__ == '__main__':
    try:
        main()
    except Exception as error:
        print('AUDIT FAILED: ' + str(error), file=sys.stderr)
        raise SystemExit(1)
