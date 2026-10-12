"""Build manuscript tables from executed results; never invent measurements."""
from pathlib import Path
import csv
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def main() -> None:
    results = ROOT / 'results'
    audit = json.loads((results / 'audit.json').read_text())
    if audit.get('status') != 'PASS':
        raise ValueError('The recorded finite audit did not pass')
    log = (results / 'unit_tests.txt').read_text()
    match = re.search(r'Ran (\d+) tests?', log)
    if not match or not re.search(r'^OK\s*$', log, flags=re.M):
        raise ValueError('No successful recorded unit suite')
    with (results / 'benchmark_summary.csv').open(newline='') as stream:
        rows = {row['case']: row for row in csv.DictReader(stream)}
    chain = rows['K33-chain-6']
    fan = rows['source-SCC-fan-6']
    macros = {
        'NewTests': match[1],
        'ExhaustiveCases': f"{audit['total_exhaustive']:,}",
        'ChainOld': f"{float(chain['old_ms']):.3f}",
        'ChainFactored': f"{float(chain['factored_ms']):.3f}",
        'ChainNew': f"{float(chain['new_ms']):.3f}",
        'ChainRatio': f"{float(chain['factored_speedup']):.2f}",
        'FanRatio': f"{float(fan['factored_speedup']):.2f}",
    }
    (results / 'summary_macros.tex').write_text(
        '% Generated from the recorded audit and benchmark, not estimates.\n' +
        ''.join('\\newcommand{\\' + key + '}{' + value + '}\n' for key, value in macros.items()))
    stress = json.loads((results / 'stress.json').read_text())
    table = ('\\begin{tabular}{rrrrrr}\n\\toprule\n'
             'Rows & Optimum & Width & Peak states & Work units & Time (ms)\\\\\n\\midrule\n')
    for row in stress:
        table += (f"{row['rows']} & {row['optimum']} & {row['width']} & "
                  f"{row['peak_states']} & {row['work']:,} & {row['milliseconds']:.3f}\\\\\n")
    table += '\\bottomrule\n\\end{tabular}\n'
    (results / 'stress_table.tex').write_text(table)
    print(json.dumps(macros, indent=2))

if __name__ == '__main__':
    main()
