#!/usr/bin/env python3
"""Recompute the scoped research inventory from recorded raw outputs/logs."""
from pathlib import Path
import argparse
import hashlib
import json
import re


def summarize(base):
    base = Path(base)
    config = json.loads((base / 'search_profiles.json').read_text())
    audits = {r['file']: r for r in json.loads(
        (base / 'independent_grammar_audits.json').read_text())}
    campaigns = []
    for profile in config['profiles']:
        log = (base / profile['log']).read_text()
        done = re.findall(r'^DONE (\d+) best (\d+) accepted (\d+) '
                          r'uphill (\d+) restarts (\d+) sec ([\d.]+)$',
                          log, re.MULTILINE)
        assert len(done) == 1, profile['name']
        proposals, best, accepted, uphill, restarts, seconds = done[0]
        result = json.loads((base / profile['output']).read_text())
        audit = audits[profile['output']]
        assert result['rules_count'] == audit['rules'] == int(best)
        campaigns.append({
            'name': profile['name'], 'status': 'COMPLETED',
            'proposals': int(proposals), 'accepted': int(accepted),
            'uphill_count': int(uphill), 'restarts': int(restarts),
            'reported_best_rule_count': int(best), 'seed': profile['seed'],
            'seconds': float(seconds), 'properties': result['properties'],
            'six_zero_occurrences': audit['six_zero_chains'],
            'scope': profile['scope'], 'log': profile['log'],
            'output': profile['output'],
            'output_sha256': hashlib.sha256(
                (base / profile['output']).read_bytes()).hexdigest(),
        })
    models = []
    for profile in config['milp']:
        result = json.loads((base / profile['output']).read_text())
        inventory = json.loads((base / profile['log']).read_text().splitlines()[0])
        entry = {'file': profile['output'], 'model_inventory': inventory}
        entry.update({k: v for k, v in result.items()
                      if k not in ('rules', 'roots', 'routes', 'phrases')})
        entry['interpretation'] = (
            'UNKNOWN: time limit, with no incumbent.' if result['status'] == 1 else
            'Solver-reported infeasibility in this finite candidate pool; '
            'no independently checked proof log.' if result['status'] == 2 else
            'Solver-reported optimum in this finite candidate pool; '
            'no independently checked optimality proof log.')
        models.append(entry)
    parsing = []
    for name in ('adjacent-parse-search.json', 'ranked-parse-search.json'):
        result = json.loads((base / name).read_text())
        parsing.append({
            'file': name, 'weighted_parses': len(result['records']),
            'best_rule_count': result['best']['rules_count'],
            'free_closure': result['free_closure'], 'seconds': result['seconds'],
            'scope': 'Reuse-weighted parsing heuristic; no claim of optimality '
                     'or a new binary machine.',
        })
    return {
        'status': 'NO_SUB245_MACHINE_FOUND',
        'interpretation': 'These are bounded discovery campaigns. Proposal '
            'counts include rejected moves and repetitions. Reported grammars '
            'are not new certified binary machines. MILP conclusions are '
            'solver reports about finite candidate pools, without independent '
            'proof logs; timeout means UNKNOWN.',
        'total_annealing_proposals': sum(r['proposals'] for r in campaigns),
        'campaigns': campaigns, 'milp': models, 'reuse_parsing': parsing,
        'exact_obstruction': 'locked_zero5_obstruction_verified.json',
    }


if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('--base', type=Path, default=Path(__file__).resolve().parent)
    p.add_argument('--output', type=Path)
    a = p.parse_args()
    assert __debug__, 'Assertions must remain enabled.'
    result = summarize(a.base)
    output = a.output or a.base / 'grammar_search_results.json'
    output.write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps({'status': result['status'],
                      'campaigns': len(result['campaigns']),
                      'total_annealing_proposals': result['total_annealing_proposals'],
                      'output': str(output)}, indent=2))
