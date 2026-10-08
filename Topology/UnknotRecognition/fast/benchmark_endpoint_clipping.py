"""Pinned current matcher versus endpoint-pattern clipping, with exact fallbacks.

All kernel/operation times include fresh grammar construction; query times
include fresh PD validation, whole recognition and certificate replay. Keep
old-shortcut controls and failed structural certificates. No claim about the
number of moves required to recognize arbitrary knots follows from this test.
"""
import argparse
from contextlib import contextmanager
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
from time import perf_counter
import types
from unittest.mock import patch

from benchmark_compressed_words import cases
from fastunknot import Diagram, recognize, compressed_lcs, compressed_overlap, compressed_search
from fastunknot.compressed_words import CompressedLimit, WordArena

ROOT = Path(__file__).resolve().parent
BASELINE = '8a9c08bcf8e0dd836182832f96c2a05f98290870'
SEED = 261008107


def digest(value):
    return sha256(json.dumps(value, sort_keys=True, separators=(',', ':')).encode()).hexdigest()


def source_hashes():
    paths = list((ROOT/'fastunknot').glob('*.py')) + [ROOT/'benchmark_endpoint_clipping.py',
        ROOT/'benchmark_compressed_words.py', ROOT/'hard_unknots.py',
        ROOT/'normal_research/gordian.json']
    return {str(p.relative_to(ROOT)): sha256(p.read_bytes()).hexdigest() for p in sorted(paths)}


def baseline_class():
    source = subprocess.check_output(['git','show',BASELINE+
        ':Topology/UnknotRecognition/fast/fastunknot/compressed_lcs.py'],cwd=ROOT)
    module = types.ModuleType('fastunknot._endpoint_clipping_baseline')
    exec(compile(source, '<'+BASELINE+':compressed_lcs>', 'exec'), module.__dict__)
    return module.CommonSubstring, sha256(source).hexdigest()


def validate_progressions(answer, first, step, count):
    """An independent containment/cardinality oracle for one expected AP.

    The tested implementations emit disjoint AP ranges on these families.
    Containment plus disjointness and equal cardinality proves full equality
    without enumerating any large occurrence count.
    """
    total, previous = 0, -1
    final = first+step*(count-1)
    for start, difference, size in sorted(answer):
        assert size > 0 and difference >= 0
        end = start+difference*(size-1)
        assert previous < start <= end <= final
        assert start >= first and (start-first) % step == 0
        assert size == 1 or (difference > 0 and difference % step == 0)
        total += size
        previous = end
    assert total == count


def kernel(arena, factory, family, bits):
    n = 1 << bits
    if family in ('full-overlap-control', 'phase-prefix'):
        if family == 'full-overlap-control':
            root = arena.power(arena.from_word([1, 2]), n)
            answer = factory(arena).overlaps(root, root)
            expected = (2, 2, n)
        else:
            prefix = arena.concat(arena.power(arena.from_word([3, 1, 2]), n-1), arena.letter(3))
            x = arena.concat(arena.from_word([8, 8]), prefix)
            y = arena.concat(prefix, arena.from_word([9, 9]))
            answer = factory(arena).overlaps(x, y)
            expected = (1, 3, n)
        return answer, expected, False
    core = [2, 1] if family == 'bigram-power' else [1, 2]
    tail = [1] if family == 'bigram-power' else [1, 1] if family == 'fourgram-power' else [3]
    block = arena.concat(arena.power(arena.from_word(core), n), arena.from_word(tail))
    period = arena.lengths[block]
    copies = 17 if family == 'sparse-17-control' else 65 if family == 'markers-65' else n
    x = y = arena.power(block, copies)
    expected = (period, period, copies)
    if family in ('nonperiodic-target', 'partial-half'):
        passed = copies-1 if family == 'nonperiodic-target' else copies//2
        x = arena.concat(arena.power(arena.letter(4), period*(copies-passed)), arena.power(block, passed))
        expected = period, period, passed
    elif family == 'period-reject':
        damaged = arena.concat(arena.concat(arena.power(arena.from_word([1, 2]), n//2),
                                            arena.from_word([4, 4])),
                               arena.concat(arena.power(arena.from_word([1, 2]), n//2-1),
                                            arena.letter(3)))
        pair = arena.concat(block, damaged)
        x = y = arena.power(pair, 65)
        expected = 2*period, 2*period, 65
    answer = factory(arena).overlaps(x, y)
    return answer, expected, family == 'fourgram-power'


def operation(arena, factory, family, bits):
    n = 1 << bits
    if family == 'quotient-control':
        roots = [arena.power(arena.letter(1), n), arena.power(arena.letter(1), n*n+1)]
        moves = []
        assert compressed_search._search(arena, roots, {1, 2}, moves,
                                         relator_moves=True, max_letters=0)
        assert len(moves) == 2
        return moves
    block = arena.concat(arena.power(arena.from_word([2, 1]), n), arena.letter(1))
    run = arena.power(block, n)
    length = arena.lengths[run]
    if family.endswith('phase'):
        p = arena.lengths[block]
        shifted = arena.concat(arena.slice(block, 1, p), arena.slice(block, 0, 1))
        other = arena.power(shifted, n)
        expected = length-1
    else:
        other, expected = run, length
    if family.startswith('lcs'):
        if family.endswith('phase'):
            answer = factory(arena).longest(run, other)
        else:
            x = arena.concat(arena.concat(arena.letter(4), run), arena.letter(5))
            y = arena.concat(arena.letter(5), arena.concat(other, arena.letter(4)))
            answer = factory(arena).longest(x, y)
        assert answer[0] == expected
        return answer
    roots = [arena.concat(arena.concat(arena.letter(4), run), arena.letter(5)),
             arena.concat(arena.letter(5), arena.concat(other, arena.letter(4)))]
    assert compressed_overlap.whole_donor_move(arena, roots) is None
    move = compressed_overlap.cyclic_overlap_move(arena, roots)
    assert move is not None and move['overlap'] == expected
    compressed_overlap.apply_cyclic_overlap(arena, roots, move)
    return move


def summarize(samples):
    medians, paired = {}, {}
    for arm in ('baseline','control','clipping'):
        good = [s['measurements'][arm]['seconds'] for s in samples
                if s['measurements'][arm]['status'] == 'COMPLETE']
        medians[arm] = dict(count=len(good),seconds=median(good) if good else None)
    for a,b in [('baseline','control'),('baseline','clipping')]:
        good = [s['measurements'][a]['seconds']/s['measurements'][b]['seconds']
                for s in samples if s['measurements'][a]['status'] == 'COMPLETE'
                and s['measurements'][b]['status'] == 'COMPLETE']
        paired[a+'/'+b] = dict(count=len(good),median=median(good) if good else None)
    return dict(completed_medians=medians,paired_ratios=paired)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--rounds',type=int,default=5)
    parser.add_argument('--bits',type=int,nargs='+',default=[8,64,500])
    parser.add_argument('--operation-bits',type=int,nargs='+',default=[8,32])
    parser.add_argument('--skip-knots',action='store_true')
    args=parser.parse_args()
    if args.rounds<1 or any(b<3 for b in args.bits+args.operation_bits):
        parser.error('positive rounds and bit parameters at least three required')
    old,old_hash=baseline_class()
    frozen,rng=source_hashes(),random.Random(SEED)
    factories=dict(baseline=old,control=old,clipping=compressed_lcs.CommonSubstring)
    @contextmanager
    def environment(arm):
        with patch.object(compressed_lcs,'CommonSubstring',factories[arm]):
            yield factories[arm]
    kernels,operations,rows=[],[],[]
    families=('marker-power','bigram-power','fourgram-power','nonperiodic-target',
              'partial-half','period-reject','full-overlap-control','sparse-17-control')
    for kind,names,bits_list,destination in (
        ('kernel',families,args.bits,kernels),
        ('operation',('lcs-phase','relator-phase','quotient-control'),args.operation_bits,operations)):
        for family in names:
            for bits in bits_list:
                samples,warmups=[],[]
                for repetition in range(args.rounds+1):
                    order=list(factories);rng.shuffle(order);measurements={}
                    for arm in order:
                        with environment(arm) as factory:
                            start=perf_counter()
                            arena=WordArena(max_work=2000000,max_nodes=100000)
                            try:
                                if kind=='kernel':
                                    answer,expected,short=kernel(arena,factory,family,bits)
                                    # Validate outside the timed region below.
                                else:
                                    answer=operation(arena,factory,family,bits)
                                status,reason='COMPLETE',None
                            except CompressedLimit as exc:
                                answer,status,reason=None,'LIMIT',str(exc)
                            elapsed=perf_counter()-start
                            if status=='COMPLETE' and kind=='kernel':
                                check=list(answer)
                                if short:
                                    assert (1,0,1) in check
                                    check.remove((1,0,1))
                                validate_progressions(check,*expected)
                            measurements[arm]=dict(seconds=elapsed,status=status,reason=reason,
                                answer=answer,nodes=len(arena.rules)-1,stats=dict(arena.stats))
                    (samples if repetition else warmups).append(dict(order=order,measurements=measurements))
                row=dict(family=family,bits=bits,samples=samples,warmups=warmups,**summarize(samples))
                destination.append(row)
                print(kind,family,bits,row['completed_medians'],flush=True)
    if not args.skip_knots:
        for name,diagram in cases():
            samples,warmups=[],[]
            for repetition in range(args.rounds+1):
                order=list(factories);rng.shuffle(order);measurements={}
                for arm in order:
                    with environment(arm):
                        start=perf_counter()
                        result=recognize(Diagram.from_pd(diagram.pd),use_group=True,
                            group_compressed_search=True,group_relators=True,
                            group_seconds=15,group_max_work=20000000,seconds=18,max_objects=50000)
                        elapsed=perf_counter()-start
                    completed=result.status in ('UNKNOT','KNOTTED')
                    if completed:assert result.status=='UNKNOT'
                    group=result.evidence.get('group',{})
                    measurements[arm]=dict(seconds=elapsed,status='COMPLETE' if completed else 'LIMIT',
                        verdict=result.status,method=result.method,reason=result.evidence.get('reason'),
                        certificate_sha256=digest(group.get('certificate')),search_stats=group.get('search_stats'))
                completed=[v for v in measurements.values() if v['status']=='COMPLETE']
                assert len({v['certificate_sha256'] for v in completed})<=1
                (samples if repetition else warmups).append(dict(order=order,measurements=measurements))
            row=dict(name=name,pd=diagram.pd,samples=samples,warmups=warmups,**summarize(samples))
            rows.append(row)
            print('query',name,row['completed_medians'],flush=True)
    assert frozen==source_hashes(),'source changed during benchmark'
    args.output.write_text(json.dumps(dict(baseline=BASELINE,baseline_lcs_sha256=old_hash,
        source_sha256=frozen,source_hashes_unchanged=True,seed=SEED,python=sys.version,
        platform=platform.platform(),rounds=args.rounds,excluded_warmups_per_case_arm=1,
        kernel_bits=args.bits,operation_bits=args.operation_bits,max_work=2000000,max_nodes=100000,
        query_options=dict(group_seconds=15,group_max_work=20000000,seconds=18,max_objects=50000),
        kernel_scope='fresh grammar construction and complete overlap query; independent answer containment/cardinality check outside timing',
        operation_scope='fresh dense-letter long-period grammar, full LCS or failed donor search plus cyclic relator search and checked application; quotient is a pure-power control',
        query_scope='fresh validated PD, complete optional compressed-group recognition and replay; all existing filters retained; new two-meridian stage disabled',
        censoring='LIMIT is inconclusive and excluded from completed-time denominators and paired ratios; no negative matching result inferred',
        kernels=kernels,operations=operations,rows=rows),indent=2)+'\n')


if __name__=='__main__':
    main()
