"""Check the optional fuel bound and both complete bounded verifiers."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parents[1]


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def main():
    results = []
    cli = 0
    for label, relative, examples in [
        ('fusion', 'code/checker_fuel.py', 'validation/examples'),
        ('control', 'code/control_separate_fuel.py', 'validation/control_examples')]:
        kernel = load(label, ROOT / relative)
        maximum = 0
        count = 0
        for path in sorted((ROOT / examples).glob('*.json')):
            certificate = json.loads(path.read_text())
            certificate['fuel'] = 10000000
            kernel.check(certificate)
            used = certificate['fuel'] - kernel.remaining
            maximum = max(maximum, used)
            certificate['fuel'] = used
            kernel.check(certificate)
            if kernel.remaining != 0:
                raise AssertionError('exact budget not consumed')
            certificate['fuel'] = used - 1
            try:
                kernel.check(certificate)
            except Exception:
                pass
            else:
                raise AssertionError('one-short fuel accepted')
            for fuel, accepted in [(used, True), (0, False)]:
                certificate['fuel'] = fuel
                for optimized in [False, True]:
                    command = [sys.executable] + (['-O'] if optimized else []) + [str(ROOT / relative)]
                    result = subprocess.run(command, input=json.dumps(certificate),
                                            text=True, capture_output=True, timeout=30)
                    if (result.returncode == 0 and result.stdout.strip() == 'ACCEPT') != accepted:
                        raise AssertionError((label, path.name, fuel, result.stdout))
                    cli += 1
            count += 1
        bad = {'goal': [0, 0], 'proof': ['u', 0, 0, None]}
        for fuel in [True, False, -1, 1.5, '100', None]:
            try:
                kernel.check(dict(bad, fuel=fuel))
            except Exception:
                pass
            else:
                raise AssertionError('malformed fuel accepted')
        results.append(dict(checker=label, accepted=count,
                            exact_and_one_short_budgets=count,
                            malformed_fuel_rejections=6,
                            maximum_observed_budget=maximum))
    report = dict(status='PASS', checkers=results, cli_checks=cli)
    (ROOT / 'evidence' / 'fuel_verification.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
