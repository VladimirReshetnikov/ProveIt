"""Reproduce report 28's independent-cube audit against current production.

The delivered audit is executed with only its import paths, output destinations
and scope description changed. No delivered file is modified. The adapter's
source substitutions are explicit and fail if the delivered script changes.
"""
import argparse
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    args.output_dir.mkdir(parents=True, exist_ok=True)
    source = ROOT / 'reports/28/experiments/audit.py'
    text = source.read_text()
    replacements = {
        'ROOT=Path(__file__).resolve().parents[1]':
            'ROOT=Path('+repr(str(ROOT/'reports/28'))+')\nOUT=Path('+repr(str(args.output_dir.resolve()))+')',
        "str(ROOT/'reference_upstream')": repr(str(ROOT/'fast')),
        "(ROOT/'results'/'audit_cases.json')": "(OUT/'closure-reset-upstream-cases.json')",
        "(ROOT/'results'/'audit_summary.json')": "(OUT/'closure-reset-upstream-summary.json')",
        'independent cube vs source-derived FastScan fixture; no production-suite claim':
            'Independent report 28 cube vs current production FastScan; adapted import and output paths only',
    }
    for old, new in replacements.items():
        if text.count(old) != 1:
            raise ValueError('delivered audit changed: '+old)
        text = text.replace(old, new)
    exec(compile(text, str(source), 'exec'), {'__name__': '__main__', '__file__': str(source)})


if __name__ == '__main__':
    main()
