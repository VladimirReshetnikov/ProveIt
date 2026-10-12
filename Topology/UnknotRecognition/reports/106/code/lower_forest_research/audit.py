"""Audit every refusal from an authenticated full-corpus baseline report.

Run from the native ``fast`` directory as ``python -m lower_forest_research.audit
--baseline /path/paired_native_benchmark.json --output /path/output``.
The baseline supplies selection and original coverage; the producer API itself
has no corpus-specific identifiers.  All newly successful packets undergo full
independent source-bound replay using the unmodified native verifier.
"""

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import time

from fastunknot.integer_codec import json_safe
from fastunknot.normal_cut_handlebodies import normal_cut_handlebodies
from fastunknot.normal_cut_handlebodies_verify import verify_normal_cut_handlebodies
from .producer import normal_cut_handlebodies_with_forests


def _digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--baseline', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--corpus', type=Path,
                        default=Path(__file__).resolve().parents[1] /
                        'marked_parallelity_research/corpus.json')
    parser.add_argument('--previous-packets', type=Path)
    args = parser.parse_args()
    corpus_bytes, baseline_bytes = args.corpus.read_bytes(), args.baseline.read_bytes()
    corpus, baseline = json.loads(corpus_bytes), json.loads(baseline_bytes)
    if _digest(corpus_bytes) != baseline['corpus_sha256']:
        raise ValueError('baseline evidence belongs to a different corpus')
    evidence = {c['id']: c for c in baseline['cases']}
    if set(evidence) != {c['id'] for c in corpus['cases']}:
        raise ValueError('baseline evidence does not cover exactly this corpus')
    if any(not c['exact_output_parity'] for c in evidence.values()):
        raise ValueError('baseline evidence lacks full native output parity')
    counts = Counter(c['status'] for c in evidence.values())
    targets = [c for c in corpus['cases'] if evidence[c['id']]['status'] != 'COMPLETE']
    report = dict(source_pin=baseline['source_pin'], corpus_sha256=_digest(corpus_bytes),
                  baseline_evidence_file=args.baseline.name,
                  baseline_evidence_sha256=_digest(baseline_bytes),
                  baseline_counts=dict(counts), policies=['exceptional_first', 'reverse'],
                  max_extra_forests=4, random_search=False,
                  note='Native COMPLETE inputs return unchanged; all baseline refusals are freshly audited.',
                  cases=[])
    args.output.mkdir(parents=True, exist_ok=True)
    for case in targets:
        before = deepcopy(case)
        native = normal_cut_handlebodies(case['triangulation'], case['coordinates'],
                                        record_certificate=True)
        if native['status'] != evidence[case['id']]['status']:
            raise AssertionError('baseline status changed')
        start = time.perf_counter()
        result = normal_cut_handlebodies_with_forests(
            case['triangulation'], case['coordinates'], record_certificate=True)
        entry = dict(id=case['id'], native_status=native['status'],
                     native_reason=native.get('reason'), status=result['status'],
                     reason=result.get('reason'), producer_seconds=time.perf_counter() - start,
                     portfolio=result['stats'].get('lower_forest_portfolio'),
                     input_sha256=_digest(json.dumps(json_safe(dict(
                         triangulation=case['triangulation'], coordinates=case['coordinates'])),
                         sort_keys=True, separators=(',', ':')).encode()))
        if result['status'] == 'COMPLETE':
            start = time.perf_counter()
            if not verify_normal_cut_handlebodies(
                    case['triangulation'], case['coordinates'], result['certificate']):
                raise AssertionError('new packet failed independent whole-cut replay')
            entry.update(independent_full_replay=True,
                         replay_seconds=time.perf_counter() - start, census=result['census'])
            name = case['id'].replace('/', '__') + '.json'
            packet = json_safe(dict(id=case['id'], triangulation=case['triangulation'],
                                    coordinates=case['coordinates'], certificate=result['certificate']))
            if args.previous_packets and (args.previous_packets / name).exists():
                previous = (args.previous_packets / name).read_bytes()
                if json.loads(previous) != packet:
                    raise AssertionError('deterministic packet differs from exploratory packet')
                packet_bytes = previous
                entry['same_packet_as_exploration'] = True
            else:
                packet_bytes = (json.dumps(packet, indent=2) + '\n').encode()
            (args.output / name).write_bytes(packet_bytes)
            entry.update(packet=name, packet_sha256=_digest(packet_bytes))
        if case != before:
            raise AssertionError('producer mutated source input')
        entry['source_inputs_unchanged'] = True
        report['cases'].append(entry)
        print(json.dumps(dict(id=entry['id'], status=entry['status'], reason=entry['reason'],
                              extra_forests=(entry['portfolio'] or {}).get('extra_forests', 0))), flush=True)
    new = sum(c['status'] == 'COMPLETE' for c in report['cases'])
    report.update(all_baseline_refusals_audited=len(report['cases']) == len(targets),
                  new_source_bound_complete=new,
                  portfolio_counts=dict(COMPLETE=counts['COMPLETE'] + new,
                                        INCONCLUSIVE=len(corpus['cases']) - counts['COMPLETE'] - new))
    (args.output / 'bounded_lower_forest_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('all_baseline_refusals_audited',
                                           'new_source_bound_complete', 'portfolio_counts')}), flush=True)


if __name__ == '__main__':
    main()
