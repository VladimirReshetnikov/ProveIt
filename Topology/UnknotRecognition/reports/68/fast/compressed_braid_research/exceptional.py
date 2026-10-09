"""Reproducible source-bound exceptional-factor audit and paired measurements."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import platform
import random
from statistics import median
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.compressed_braid import recognize, verify, _Budget, _encoded_size, _source
from fastunknot.compressed_braid.cube import produce
from fastunknot.compressed_braid.cube_verify import verify as verify_cube
from fastunknot.compressed_braid.forest import summarize
from fastunknot.diagram import Diagram, DiagramError
from fastunknot.scan import khovanov_rank
from compressed_braid_research.families import sleeve


def grammar(strands, word):
    rules, root = [['e']], 0
    for letter in word:
        node = len(rules)
        rules.extend([['g', letter], ['c', root, node]])
        root = node + 1
    return dict(strands=strands, rules=rules, root=root)


def join(left, right):
    rules, roots = [['e']], []
    for data, offset in ((left, 0), (right, left['strands'])):
        mapped = [0]
        for rule in data['rules'][1:]:
            if rule[0] == 'g':
                g = rule[1]
                new = ['g', (1 if g > 0 else -1)*(abs(g)+offset)]
            else:
                new = ['c', mapped[rule[1]], mapped[rule[2]]]
            mapped.append(len(rules))
            rules.append(new)
        roots.append(mapped[data['root']])
    rules.append(['c', *roots])
    product = len(rules)-1
    rules.append(['g', left['strands']])
    rules.append(['c', product, product+1])
    return dict(strands=left['strands']+right['strands'], rules=rules, root=len(rules)-1)


def sources():
    files = list((ROOT/'fastunknot/compressed_braid').glob('*.py'))
    files += [Path(__file__).resolve(), ROOT/'compressed_braid_research/families.py',
              ROOT/'fastunknot/compressed_words.py', ROOT/'fastunknot/scan.py',
              ROOT/'fastunknot/diagram.py', ROOT.parent/'reports/34/braidkernel/cube.py']
    return {str(p.relative_to(ROOT.parent)): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in files}


def whole_cube(data):
    """Ablation: expand the whole supplied braid and produce/replay its cube.

    Same host transport and shared-work conventions, without singleton splitting.
    Explicit preflight is performed by the benchmark before this arm is added.
    """
    budget = _Budget(50000000, 100000, None, lambda: None, 2000000)
    _source(data, 100000, 16000000, budget)
    summary = summarize(data, check=budget.step)
    assert summary['knot']
    opts = dict(max_crossings=12, check=budget.step, reserve=budget.reserve_generators)
    proof = produce(data, summary, **opts)
    _encoded_size(proof, 64000000, budget)
    result = verify_cube(data, summary, proof, **opts)
    assert result == proof['status']
    return result


def measure(arms, expected, rng):
    samples = {key: [] for key in arms}
    orders = []
    for trial in range(-1, 5):
        order = list(arms)
        rng.shuffle(order)
        orders.append(order)
        for key in order:
            start = time.perf_counter_ns()
            value = arms[key]()
            elapsed = (time.perf_counter_ns()-start)/1e9
            assert value == expected, (key, value, expected)
            if trial >= 0:
                samples[key].append(elapsed)
    return dict(seconds=samples, medians={k: median(v) for k,v in samples.items()},
                orders=orders,
                paired_ratios={k: median(a/b for a,b in zip(samples[next(iter(arms))],v))
                               for k,v in samples.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode', choices=('audit', 'benchmark'))
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    before = sources()
    rng = random.Random(261008493)
    result = dict(seed=261008493, mode=args.mode, python=platform.python_version(),
                  platform=platform.platform(),
                  checkout=subprocess.check_output(['git', 'rev-parse', 'HEAD'], text=True).strip())
    start = time.perf_counter()
    if args.mode == 'audit':
        path = ROOT.parent/'reports/34/braidkernel/__init__.py'
        spec = importlib.util.spec_from_file_location('_report34_braid', path,
                                                     submodule_search_locations=[str(path.parent)])
        module = importlib.util.module_from_spec(spec)
        sys.modules[spec.name] = module
        spec.loader.exec_module(module)
        from _report34_braid.cube import reduced_khovanov
        cases = []
        while len(cases) < 160:
            strands = rng.choice((3,4,5,6))
            n = rng.randrange(strands-1,11)
            word = [rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(n)]
            try:
                diagram = Diagram.from_braid(strands,word)
            except DiagramError:
                continue
            data = grammar(strands,word)
            summary = summarize(data)
            proof = produce(data,summary,max_crossings=10,check=lambda: None,reserve=lambda n: None)
            status = verify_cube(data,summary,proof,max_crossings=10,check=lambda: None,reserve=lambda n: None)
            old = reduced_khovanov(module.Braid.checked(strands,word),check_d_squared=True)
            scan = khovanov_rank(diagram.pd, check_d_squared=True)
            rank = sum(proof['homology'])
            assert rank == old['reduced_rank'] == scan['reduced_rank']
            native = recognize(data)
            assert native['status'] == status and native['verified']
            assert verify(data,native['certificate']) == status
            cases.append(dict(strands=strands,word=word,rank=rank,status=status,
                              cube_used=native['resources']['cube_generators'] > 0))
            if len(cases) % 20 == 0:
                print(len(cases), flush=True)
        result['cases'] = cases
    else:
        unknot = grammar(4,[1,2,3,1,-1,2,-2,3,-3])
        knot = grammar(4,[1,2,-3]*3)
        cases = [('four_unknot',unknot,'UNKNOT'),('four_knot',knot,'KNOTTED'),
                 ('small_sum_unknot',join(grammar(3,[1,2]),unknot),'UNKNOT'),
                 ('small_sum_knot',join(grammar(3,[1,2]),knot),'KNOTTED')]
        for k in (8,64,512):
            cases.append((f'huge_sum_{k}',join(sleeve(k),unknot),'UNKNOT'))
        result.update(cases=[], rounds=5, warmups=1,
            scope='Whole-cube ablation versus source-bound singleton hybrid, both produce and replay proofs; scanner control on four-strand explicit inputs has no replay certificate. No arbitrary-diagram speedup claim.')
        for name,data,expected in cases:
            print(name,flush=True)
            summary = summarize(data)
            arms = {}
            if summary['length'] <= 12:
                arms.update(whole=lambda: whole_cube(data),whole_AA=lambda: whole_cube(data))
            def hybrid():
                return recognize(data)['status']
            arms.update(hybrid=hybrid,hybrid_AA=hybrid)
            if data['strands'] == 4:
                from fastunknot.compressed_braid.cube import expand_leaf
                word = expand_leaf(data,summary['length'],12,lambda: None)
                pd = Diagram.from_braid(4,word).pd
                def scan():
                    rank = khovanov_rank(pd)['reduced_rank']
                    return 'UNKNOT' if rank == 1 else 'KNOTTED'
                arms.update(scanner=scan,scanner_AA=scan)
            row = measure(arms,expected,rng)
            native = recognize(data)
            assert native['status'] == expected and native['verified']
            row.update(name=name,strands=data['strands'],rules=len(data['rules']),
                       length_hex=hex(summary['length']),status=expected,
                       resources=native['resources'],certificate_bytes=native['certificate_bytes'],
                       whole_omitted=summary['length'] > 12)
            result['cases'].append(row)
    assert before == sources(), 'source changed during experiment'
    result.update(source_sha256=before, elapsed_seconds=time.perf_counter()-start)
    args.output.parent.mkdir(parents=True,exist_ok=True)
    args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__ == '__main__':
    main()
