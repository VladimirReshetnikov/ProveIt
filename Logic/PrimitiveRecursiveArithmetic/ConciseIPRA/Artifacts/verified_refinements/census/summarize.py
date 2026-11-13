"""Produce the concise empirical-baseline receipt from the static censuses."""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
KEYS = ['significant_tokens', 'ast_nodes', 'normalized_bytes']


def main():
    r = json.loads((ROOT / 'census.json').read_text())
    i = json.loads((ROOT / 'incoming_census.json').read_text())
    exclusions = json.loads((ROOT / 'exclusions.json').read_text())
    envelope = {k: min(r['candidate_coordinate_minima'][k],
                       i['candidate_coordinate_minima'][k]) for k in KEYS}
    def compact(row):
        return {k: row[k] for k in ['canonical_path', 'git_blob_sha', 'sha256',
                'source_url', 'significant_tokens', 'ast_nodes', 'normalized_bytes']}
    def incoming(row):
        return {k: row[k] for k in ['occurrences', 'sha256', 'significant_tokens',
                'ast_nodes', 'normalized_bytes']}
    summary = {
        'pin': r['pin'], 'python': r['python'],
        'research_scope': r['scope'], 'research_tree_sha': r['tree_sha'],
        'research_tree_truncated': r['tree_truncated'],
        'research_python_paths_total': r['python_paths_total'],
        'research_python_unique_blobs_total': r['python_unique_blobs_total'],
        'research_selected_paths': r['selected_paths'],
        'research_selected_unique_blobs': r['selected_unique_blobs'],
        'research_all_selected_blobs_hash_verified': all(x.get('git_blob_verified') for x in r['rows']),
        'research_canonical_metrics_available': r['retrieved_and_measured'],
        'research_all_selected_blobs_verified_and_measured': (
            r['retrieved_and_measured'] == r['selected_unique_blobs'] and not r['errors']),
        'research_errors': r['errors'],
        'research_normalization_exceptions_accounted_for': exclusions['normalization_exceptions'],
        'research_sub_envelope_noncandidate_count': exclusions['sub_envelope_noncandidate_count'],
        'research_all_sub_envelope_exclusions_lack_direct_stdin_and_literal_accept': exclusions['all_exclusions_lack_direct_stdin_and_literal_accept'],
        'research_candidate_count': r['possible_complete_acceptance_modules'],
        'research_coordinate_minima': r['candidate_coordinate_minima'],
        'research_minimizers': {k: [compact(x) for x in r['candidates']
            if x[k] == r['candidate_coordinate_minima'][k]] for k in KEYS},
        'incoming_scope': i['scope'], 'incoming_archives': i['archives'],
        'incoming_python_member_paths': i['python_member_paths'],
        'incoming_unique_python_sources': i['unique_python_sources'],
        'incoming_errors': i['errors'],
        'incoming_candidate_count': i['possible_complete_acceptance_modules'],
        'incoming_coordinate_minima': i['candidate_coordinate_minima'],
        'incoming_minimizers': {k: [incoming(x) for x in i['candidates']
            if x[k] == i['candidate_coordinate_minima'][k]] for k in KEYS},
        'combined_observed_envelope': [envelope[k] for k in KEYS],
        'one_checker_attains_combined_envelope': any(all(x[k] == envelope[k]
            for k in KEYS) for x in r['candidates'] + i['candidates']),
        'manual_inspection': {
            'research_minimizers': 'The three coordinate-minimizing modules were inspected directly. Each contains its checking recursion, scoped substitution, JSON input and ACCEPT output, with json as its sole imported module.',
            'below_495_json_imports': 'Exactly four surveyed Research blobs importing json have fewer than 495 normalized bytes; all four are payload-manifest verifiers, and none is a proof checker.',
            'incoming_minimizers': 'All three coordinate minima come from code/checker_tokens.py, code/checker_ast.py and code/checker_bytes.py in ipra_three_field_2026-11-12.zip, respectively; they do not arise from a combined checker.'},
        'limits': [
            'No downloaded Python source was imported or executed; only parsing, docstring removal, AST normalization and static inspection were performed.',
            'Candidate discovery uses JSON import, print call and literal ACCEPT marker; it is not an independent correctness proof for the theories or checkers.',
            'Every Python blob in Research and every Python member of the incoming ZIPs was included, with no raw-source size cutoff.',
            'One archived readable checker has a docstring-only class, which the exact shared normalizer turns into an unparsable empty class suite. It is explicitly accounted for: 1844 unparse bytes and 367 tokens; a diagnostic pass repair gives 1853 bytes/368 tokens/414 AST nodes, so it cannot challenge the envelope. Diagnostic repair metrics are not mixed into the canonical minima.',
            'Compact guarded-public-language contracts are not equated with fully validating native checkers.',
            'This is an empirical envelope of the surveyed sources, not a lower-bound theorem over all possible checkers.']}
    (ROOT / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps({'research_sources': r['selected_unique_blobs'],
        'research_errors': len(r['errors']), 'incoming_sources': i['unique_python_sources'],
        'observed_envelope': summary['combined_observed_envelope']}))


if __name__ == '__main__':
    main()
