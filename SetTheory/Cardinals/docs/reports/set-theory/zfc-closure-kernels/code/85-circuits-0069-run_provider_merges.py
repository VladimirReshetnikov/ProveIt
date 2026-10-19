#!/usr/bin/env python3
"""Reproduce the seventeen archived provider-row merger screens sequentially.

    Compiler outputs are created only in --work-dir. By default the generated
    fixture is streamed to the C++ screen through standard input, without a disk
    copy. --keep-fixtures additionally writes a reproducible local fixture file.
"""
import argparse
import json
from pathlib import Path
import subprocess
from common import LAYOUTS, OUTPUT
from admissible_guards import verify_transport
from make_merge_cases import generate


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--work-dir', type=Path, required=True)
    parser.add_argument('--layouts', nargs='+', choices=LAYOUTS, default=LAYOUTS)
    parser.add_argument('--domains', nargs='+', choices=('unrestricted', 'guards', 'product'),
                        default=('unrestricted', 'guards', 'product'))
    parser.add_argument('--include-prior-baseline-unrestricted', action='store_true')
    parser.add_argument('--keep-fixtures', action='store_true')
    parser.add_argument('--compiler', default='c++')
    parser.add_argument('--output', type=Path, default=OUTPUT / 'provider-merges.json')
    args = parser.parse_args()
    assert __debug__, 'Assertions required; do not use -O.'
    verify_transport(args.layouts)
    work = args.work_dir.resolve()
    work.mkdir(parents=True, exist_ok=True)
    executable = work / 'merge_search'
    subprocess.run([args.compiler, '-O3', '-std=c++17', str(Path(__file__).with_name('merge_search.cpp')),
                    '-o', str(executable)], check=True)
    rows = []
    for layout in args.layouts:
        for domain in args.domains:
            if layout == 'baseline' and domain == 'unrestricted' and not args.include_prior_baseline_unrestricted:
                continue
            directory = work / (layout + '_' + domain)
            directory.mkdir(exist_ok=True)
            fixture = directory / 'merge-cases.txt'
            text, metadata = generate(layout, domain)
            if args.keep_fixtures:
                fixture.write_text(text)
            with (directory / 'merge-search.log').open('w') as log:
                subprocess.run([str(executable), '-'], cwd=directory, input=text, text=True,
                               stdout=log, stderr=subprocess.STDOUT, check=True)
            del text
            row = json.loads((directory / 'merge-search-summary.json').read_text())
            row.pop('seconds', None)
            row.update(layout=str(layout), domain=domain, fixture_sha256=metadata['fixture_sha256'])
            assert row['candidate_count'] == 120540
            rows.append(row)
            print(json.dumps(row), flush=True)
    result = dict(status='COMPLETE',
        family='Each pair of states; independently choose one original provider per read row.',
        domain_screens=len(rows), recipes_per_screen=120540,
        recipes_over_all_domain_screens=sum(row['candidate_count'] for row in rows),
        repeated_tables_across_domains=True, runs=rows)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2) + '\n')


if __name__ == '__main__':
    main()
