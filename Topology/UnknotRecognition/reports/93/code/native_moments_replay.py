"""Replay the delivered native moment examples without running discovery."""

import argparse
import json
from pathlib import Path

from native_moments_verify import verify_native_moment_words


def main():
    root = Path(__file__).resolve().parents[1]
    parser = argparse.ArgumentParser()
    parser.add_argument('certificates', type=Path, nargs='?',
                        default=root / 'results/native_moments_certificates.json')
    args = parser.parse_args()
    examples = json.loads(args.certificates.read_text())['fixtures']
    for example in examples:
        accepted = verify_native_moment_words(example['triangulation'], example['coordinates'],
                                              example['certificate'])
        print(json.dumps(dict(case=example['case'], verified=accepted)))
        if not accepted:
            raise SystemExit(1)


if __name__ == '__main__':
    main()
