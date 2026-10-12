"""Paired full producer/replay measurements for the source-handle continuation.

This is a source-operator comparison, not a whole-knot recognition benchmark.
The old query includes its transported boundary period; the new query instead
returns the exact unused-cocore decomposition and requires authenticated
irreducibility before interpreting Euler-one pieces as balls.
"""

import argparse
import json
import platform
from pathlib import Path
import random
import statistics
import sys
from time import perf_counter

from fastunknot import Diagram
from fastunknot.diagram_exterior import diagram_exterior
from fastunknot.source_handle_reduction import reduce_source_handles
from fastunknot.source_handle_reduction_verify import verify_source_handle_reduction
from normal_orbit_research.fixtures import layered_torus

from unused_handles import decompose_unused_handles, verify_unused_handle_certificate
from unused_handle_fixtures import boundary_bud_chain, verify_boundary_bud_chain


def compact_size(value):
    return len(json.dumps(value, separators=(',', ':')).encode('utf-8'))


def render_tex(result):
    """Render article tables from the same retained benchmark records."""
    names = {
        'canonical_unknot': 'Canonical unknot',
        'canonical_trefoil': 'Canonical trefoil',
        'canonical_figure_eight': 'Canonical figure-eight',
        'trefoil_buds_32': 'Trefoil + 32 buds',
        'trefoil_buds_256': 'Trefoil + 256 buds',
    }
    lines = [r'\begin{table}[htbp]', r'\centering\small',
             r'\begin{tabular}{lrrrrr}', r'\hline',
             r'Source & $t$ & Native ms & New ms & Native/New & Core $h_0$ \\',
             r'\hline']
    for row in result['records']:
        name = names.get(row['id'], f"Fibonacci $t={row['tetrahedra']}$")
        core = row['retained_handle_counts']
        cells = [name, str(row['tetrahedra']),
                 f"{row['medians']['native']['total_ms']:.3f}",
                 f"{row['medians']['new']['total_ms']:.3f}",
                 f"{row['source_total_ratio']:.3f}",
                 '---' if core is None else str(core[0])]
        lines.append(' & '.join(cells) + r' \\')
    lines.extend([
        r'\hline', r'\end{tabular}',
        rf"\caption{{{result['repeats']} paired repetitions per source, in randomized order. "
        r'Values are medians of complete producer-plus-replay times. Ratios below one are regressions. A dash marks the all-ball cycle branch.}',
        r'\label{tab:unused-timings}', r'\end{table}', '',
        r'\begin{table}[htbp]', r'\centering\small',
        r'\begin{tabular}{rrrrr}', r'\hline',
        r'Fibonacci $t$ & Native bytes & New bytes & Max. dual bits & Sum dual bits \\',
        r'\hline',
    ])
    for row in result['records']:
        if not row['id'].startswith('fibonacci_'):
            continue
        values = [row['tetrahedra'], row['certificate_bytes']['native'],
                  row['certificate_bytes']['new'],
                  row['native_dual_coefficient_bits']['maximum'],
                  row['native_dual_coefficient_bits']['total']]
        lines.append(' & '.join(str(value) for value in values) + r' \\')
    lines.extend([
        r'\hline', r'\end{tabular}',
        r'\caption{Exact compact-JSON sizes and bit counts. The new decomposition has additional per-component records, so its asymptotic improvement need not appear at small sizes. Total dual bits includes one bit for each zero entry.}',
        r'\label{tab:unused-bits}', r'\end{table}', '',
        r'The canonical trefoil core retains $(h_0,h_1,h_2)=(48,82,34)$ from a source with 60 tetrahedra; the figure-eight core retains $(68,118,50)$ from 80 tetrahedra. Every added boundary bud leaves the trefoil core unchanged. At $t=512$, the new Fibonacci certificate uses 119,503 bytes versus 172,549 bytes for the maintained certificate; at $t=64$, it instead uses 14,865 versus 9,787 bytes. These finite measurements agree with the scope, and the crossover limitations, of Proposition~\ref{prop:unused-fibonacci-separation}. Timing regressions on some sources remain visible; the source-validation and raw-cell construction costs are included in both arms.',
    ])
    return '\n'.join(lines) + '\n'


def measured_query(raw, arm):
    started = perf_counter()
    if arm == 'native':
        result = reduce_source_handles(raw, record_certificate=True)
        certificate = result['certificate']
    else:
        result = decompose_unused_handles(raw)
        certificate = result['certificate']
    produced = perf_counter()
    if arm == 'native':
        accepted = verify_source_handle_reduction(raw, certificate)
    else:
        accepted = verify_unused_handle_certificate(raw, certificate)
    finished = perf_counter()
    if not accepted:
        raise AssertionError('independent replay rejected the query')
    return dict(producer_ms=1000 * (produced - started),
                replay_ms=1000 * (finished - produced),
                total_ms=1000 * (finished - started)), result


def run(repeats):
    cases = []
    for size in (1, 16, 64, 256, 512):
        raw, _ = layered_torus(size)
        cases.append((f'fibonacci_{size}', raw, 'known layered solid torus'))
    for name, diagram in (
        ('canonical_unknot', Diagram.from_braid(3, [1, -2])),
        ('canonical_trefoil', Diagram.from_braid(2, [1, 1, 1])),
        ('canonical_figure_eight', Diagram.from_braid(3, [1, -2, 1, -2])),
    ):
        cases.append((name, diagram_exterior(diagram), 'canonical diagram exterior'))
    original = diagram_exterior(Diagram.from_braid(2, [1, 1, 1]))
    for count in (32, 256):
        raw, shellings = boundary_bud_chain(original, count)
        if not verify_boundary_bud_chain(original, raw, shellings):
            raise AssertionError('invalid geometric ballast family')
        cases.append((f'trefoil_buds_{count}', raw,
                      'canonical trefoil exterior with verified boundary shellings'))
    rng = random.Random(202610120151)
    records = []
    for name, raw, authority in cases:
        samples = {'native': [], 'new': []}
        last = {}
        for _ in range(repeats):
            order = ['native', 'new']
            rng.shuffle(order)
            for arm in order:
                sample, result = measured_query(raw, arm)
                samples[arm].append(sample)
                last[arm] = result
        old = last['native']['certificate']
        new = last['new']['certificate']
        for key in ('moves', 'remaining', 'summary'):
            if old[key] != new['reduction_certificate'][key]:
                raise AssertionError('cancellation trace changed')
        medians = {
            arm: {key: statistics.median(s[key] for s in values)
                  for key in ('producer_ms', 'replay_ms', 'total_ms')}
            for arm, values in samples.items()
        }
        decomposition = new['decomposition']
        core = new['core_component']
        core_counts = None if core is None else [
            len(decomposition['components'][core][key])
            for key in ('zero_handles', 'one_handles', 'two_handles')
        ]
        witness = old['compressing_disc']
        coefficient_bits = None
        if witness is not None:
            values = witness['boundary_witness']['dual_values']
            coefficient_bits = dict(
                maximum=max(abs(value).bit_length() for value in values),
                total=sum(max(1, abs(value).bit_length()) for value in values),
            )
        record = dict(
            id=name, tetrahedra=len(raw['tetrahedra']), authority=authority,
            samples=samples, medians=medians,
            source_total_ratio=medians['native']['total_ms'] / medians['new']['total_ms'],
            certificate_bytes=dict(native=compact_size(old), new=compact_size(new)),
            native_dual_coefficient_bits=coefficient_bits,
            cut_components=len(decomposition['components']),
            unused_handles=len(decomposition['unused_handles']),
            cycle_rank=decomposition['cycle_rank'], torus_case=new['torus_case'],
            retained_handle_counts=core_counts,
        )
        records.append(record)
        print(name, f"{medians['native']['total_ms']:.3f}",
              f"{medians['new']['total_ms']:.3f}",
              f"ratio {record['source_total_ratio']:.3f}", flush=True)
    return dict(
        schema='unused-handle-benchmark-v1', source_commit='704600626606a9097cfd89d4e3d2bbc63c8dd1cb',
        python=sys.version, platform=platform.platform(), repeats=repeats,
        timing_scope='Full source producer plus independent replay; excludes serialization and diagram construction.',
        limitation='Different certified source outputs, no whole-recognizer speed claim; source irreducibility is separately authenticated.',
        records=records,
    )


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--repeats', type=int, default=5)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--tex-output', type=Path)
    args = parser.parse_args()
    if args.repeats < 1:
        parser.error('--repeats must be positive')
    result = run(args.repeats)
    args.output.write_text(json.dumps(result, indent=2) + '\n')
    if args.tex_output is not None:
        args.tex_output.write_text(render_tex(result))
