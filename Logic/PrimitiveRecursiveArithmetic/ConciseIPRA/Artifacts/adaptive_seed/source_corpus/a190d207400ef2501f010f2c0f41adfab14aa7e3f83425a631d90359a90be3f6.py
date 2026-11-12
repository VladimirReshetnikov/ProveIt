"""Offline reproduction of certificates, source sizes, and comparison claims."""
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parent
FIELDS = ('normalized_tokens', 'ast_nodes', 'normalized_bytes')


def load_module(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    subprocess.run([sys.executable, str(ROOT / 'code/test_root_seed.py')],
                   cwd=ROOT, check=True)
    subprocess.run([sys.executable, str(ROOT / 'code/build_comparison.py')],
                   cwd=ROOT, check=True)
    measure = load_module('inherited_measure', ROOT / 'reference/source_measure.py').metrics
    rows = []
    manifest = json.loads((ROOT / 'evidence/frozen_comparators.json').read_text())
    for item in manifest:
        path = ROOT / item['local_file']
        if hashlib.sha256(path.read_bytes()).hexdigest() != item['sha256']:
            raise ValueError('Comparator identity changed: ' + item['local_file'])
        result = measure(path)
        for key in FIELDS:
            if result[key] != item['expected'][key]:
                raise ValueError('Comparator metric changed: ' + item['local_file'] + '/' + key)
        rows.append({'file': item['local_file'], **{k: result[k] for k in FIELDS},
                     'sha256': result['sha256']})
    minimum = {key: min(row[key] for row in rows) for key in FIELDS}
    candidates = []
    for name in ('root_seed_checker.py', 'matched_transport_checker.py'):
        result = measure(ROOT / 'code' / name)
        candidates.append({'file': 'code/' + name,
                           **{k: result[k] for k in FIELDS}, 'sha256': result['sha256']})
    validation = json.loads((ROOT / 'code/root_seed_validation.json').read_text())
    if not validation['all_passed'] or not all(x['passed'] for x in validation['api_checks'] + validation['cli_checks']):
        raise ValueError('Validation failure')
    receipt = {'python': platform.python_version(), 'implementation': platform.python_implementation(),
               'frozen_commit': 'aac8216be66b1a6f043fed87a8d515bc5b5d0790',
               'archives': 30, 'distinct_frozen_programs': len(rows),
               'envelope': minimum, 'candidates': candidates,
               'api_checks': len(validation['api_checks']),
               'cli_checks': len(validation['cli_checks']), 'all_passed': True,
               'strict_below_envelope': {key: candidates[0][key] < minimum[key] for key in FIELDS},
               'comparators': rows}
    (ROOT / 'evidence/reproduction.json').write_text(json.dumps(receipt, indent=2) + '\n')
    current, control = candidates
    report = r'''The focused suite records \textbf{%d API checks and %d command-line
executions, all passing}. Command-line packets run in both ordinary and
optimized Python. They include actual induction-hypothesis use, case
introduction using a false base, term contexts with repeated holes and
nested binders, Q/D formula transport through depth three, the exact
$N+8$ inference-node count, and recovery of ordinary IS when the counter
also occurs in initializer and update parameters.

Negative controls reject compound progress, incorrect computation,
invalid hypothesis references, malformed syntax, escaping eigenvariables,
and a closed witness-capture attack. The final measurements include its
correction. In paired introduction the named representation requires the
second binder to be absent from the witness's free variables; otherwise
the user of the certificate format must alpha-rename that binder first.
This preserves canonical completeness.

\begin{center}
\begin{tabular}{lrrr}
\toprule
Complete standalone program & Tokens & AST nodes & Bytes\\
\midrule
New fixed-position checker & %d & %d & %d\\
Matched ordinary-transport control & %d & %d & %d\\
Current compact coordinate envelope & %d & %d & %d\\
\bottomrule
\end{tabular}
\end{center}

The matched control uses the same parser, alpha-equivalence, scope checks,
Choice-DI, and command-line interface. It replaces Root/Seed with full
formula transport and restores ordinary I0/IS. The new source is larger
even in this matched comparison. Its structural restriction and constant
proof-node theorem therefore do \emph{not} establish the requested
checker-size improvement. The separate envelope row is not one program.
''' % (receipt['api_checks'], receipt['cli_checks'],
       *(current[k] for k in FIELDS), *(control[k] for k in FIELDS),
       *(minimum[k] for k in FIELDS))
    (ROOT / 'evidence/implementation_results.tex').write_text(report)
    print(json.dumps({key: value for key, value in receipt.items() if key != 'comparators'}, indent=2))


if __name__ == '__main__':
    main()
