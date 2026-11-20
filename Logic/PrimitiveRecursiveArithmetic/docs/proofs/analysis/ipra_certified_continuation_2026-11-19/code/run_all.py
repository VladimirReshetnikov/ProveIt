#!/usr/bin/env python3
"""Run the exact reference checks and record their distinct evidence scopes."""
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
import json
import sys
import platform
import feedback
import polynomial_checks
import cluster_transport
import ode_exact_checks


def main():
    target = Path(__file__).resolve().parents[1] / 'verification'
    target.mkdir(exist_ok=True)
    reports = {
        'feedback_validation': feedback.check_examples(),
        'cluster_validation': cluster_transport.run_checks(),
        'ode_exact_checks': ode_exact_checks.run(),
    }
    with redirect_stdout(StringIO()):
        polynomial_checks.main()
    reports['polynomial_checks'] = json.loads((target / 'polynomial_checks.json').read_text())
    for name, report in reports.items():
        (target / (name + '.json')).write_text(json.dumps(report, indent=2) + '\n')
    summary = {
        'status': 'all reference checks passed',
        'python': sys.version.split()[0],
        'platform': platform.system(),
        'arithmetic': 'Exact fractions.Fraction for every asserted numerical inequality',
        'polynomial_assertions': reports['polynomial_checks']['assertions'],
        'ode_assertions': reports['ode_exact_checks']['assertions'],
        'bipartite_graphs_exhausted': reports['cluster_validation']['graphs_checked'],
        'graph_perfect_matchings': reports['cluster_validation']['perfect_matchings'],
        'graph_hall_defects': reports['cluster_validation']['hall_defects'],
        'feedback': reports['feedback_validation']['status'],
        'lean': 'Not compiled; no Lean compiler present in delivery environment',
        'object_ipra': 'New object-level derivations remain to be implemented',
        'meaning': 'Reproducible finite computational evidence, not a substitute for the mathematical proofs'
    }
    (target / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
