#!/usr/bin/env python3
"""Regenerate the finite corpora with names understood by the independent audit."""
import argparse
import json
from pathlib import Path
from common import LAYOUTS
from admissible_guards import verify_transport
from make_merge_cases import generate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, required=True)
    parser.add_argument('--domains', nargs='+', default=['unrestricted', 'guards', 'product'],
                        choices=['unrestricted', 'guards', 'product'])
    args = parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    verify_transport()
    metadata = []
    for layout in LAYOUTS:
        name = 'baseline' if layout == 'baseline' else 'rotation' + layout
        for domain in args.domains:
            suffix = {'unrestricted': 'merges', 'guards': 'admissible', 'product': 'product'}[domain]
            destination = args.output_dir / (name + '_' + suffix) / 'merge-cases.txt'
            content, summary = generate(layout, domain)
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_text(content)
            destination.with_suffix('.json').write_text(json.dumps(summary, indent=2) + '\n')
            metadata.append(summary)
            print(layout, domain, summary['instruction_cases'], summary['fixture_sha256'], flush=True)
    (args.output_dir / 'fixture-manifest.json').write_text(json.dumps(metadata, indent=2) + '\n')


if __name__ == '__main__':
    main()
