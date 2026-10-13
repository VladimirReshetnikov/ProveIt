"""Cross-replay and paired comparison against the prior maintained forest host."""
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
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from fastunknot.compressed_braid import recognize, verify
from compressed_braid_research.exceptional import grammar, join
from compressed_braid_research.families import sleeve, singleton_forest

BASE = '666a62f6a6ddedd04613ff0e0b43b8601e121f4a'
PREFIX = 'Topology/UnknotRecognition/fast/fastunknot/compressed_braid/'


def baseline(directory):
    names = subprocess.check_output(['git','ls-tree','--full-tree','-r','--name-only',BASE,'--',PREFIX], text=True).splitlines()
    hashes = {}
    for name in names:
        if name.endswith('.py'):
            source = subprocess.check_output(['git','show',BASE+':'+name])
            (directory/Path(name).name).write_bytes(source)
            hashes[name] = hashlib.sha256(source).hexdigest()
    name = 'fastunknot._adaptive_forest_baseline'
    spec = importlib.util.spec_from_file_location(name,directory/'__init__.py',submodule_search_locations=[str(directory)])
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    spec.loader.exec_module(module)
    return module, hashes


def sources():
    files = list((ROOT/'fastunknot/compressed_braid').glob('*.py'))
    files += [ROOT/'fastunknot/braid_reduction.py',ROOT/'fastunknot/braid_descent.py',
              ROOT/'fastunknot/compressed_words.py',ROOT/'compressed_braid_research/exceptional.py',
              ROOT/'compressed_braid_research/families.py',Path(__file__).resolve()]
    return {str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in files}


def measure(arms, expected, rng):
    samples = {a: [] for a in arms}
    orders = []
    for trial in range(-1,5):
        order = list(arms)
        rng.shuffle(order)
        orders.append(order)
        for arm in order:
            start = time.perf_counter_ns()
            result = arms[arm]()
            elapsed = (time.perf_counter_ns()-start)/1e9
            assert result == expected,(arm,result,expected)
            if trial >= 0:
                samples[arm].append(elapsed)
    return dict(seconds=samples, medians={a:median(v) for a,v in samples.items()},orders=orders,
                paired_ratios={a:median(x/y for x,y in zip(samples['old'],v)) for a,v in samples.items()})


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('mode',choices=('audit','benchmark'))
    parser.add_argument('--output',type=Path,required=True)
    args = parser.parse_args()
    before = sources()
    rng = random.Random(261008494)
    begin = time.perf_counter()
    with tempfile.TemporaryDirectory(prefix='adaptive-forest-baseline-') as tmp:
        old, hashes = baseline(Path(tmp))
        result = dict(schema='adaptive_forest_v1',mode=args.mode,seed=261008494,
                      python=platform.python_version(),platform=platform.platform(),baseline=BASE,
                      baseline_source_sha256=hashes,cases=[])
        if args.mode == 'audit':
            prior = json.loads((ROOT.parent/'synthesis/data/exceptional-cube-audit.json').read_text())
            for index,row in enumerate(prior['cases']):
                data = grammar(row['strands'],row['word'])
                previous, current = old.recognize(data), recognize(data)
                assert previous['status'] == current['status'] == row['status']
                assert verify(data,previous['certificate']) == current['status']
                assert verify(data,current['certificate']) == current['status']
                result['cases'].append(dict(index=index,status=current['status'],
                    old_cube_generators=previous['resources']['cube_generators'],
                    current_cube_generators=current['resources']['cube_generators'],
                    version=current['certificate']['version']))
            result['input_audit_sha256']=hashlib.sha256((ROOT.parent/'synthesis/data/exceptional-cube-audit.json').read_bytes()).hexdigest()
            # A complete finite obstruction now survives a zero cube allowance.
            data=join(grammar(4,[1,2,3,1,-1,2,-2,3,-3]),grammar(2,[1]*3))
            previous=old.recognize(data,fallback_max_generators=0)
            current=recognize(data,fallback_max_generators=0)
            assert previous['status']=='INCONCLUSIVE' and current['status']=='KNOTTED'
            result['bounded_progress']=dict(old=previous['status'],current=current['status'],
                factor_order=current['factor_order'],certificate=current['certificate'])
        else:
            positive=grammar(4,[1,2,3,1,-1,2,-2,3,-3])
            negative=grammar(4,[1,2,-3]*3)
            cases=[('reducible_four',positive),('irreducible_four',negative),
                   ('shorter_wider',grammar(4,[1,2,-3]*3+[1,-1])),
                   ('finite_late',join(positive,grammar(2,[1]*3))),
                   ('compressed_negative_late',join(positive,sleeve(16,negative=True))),
                   ('positive_sum',join(positive,sleeve(16))),
                   ('huge_positive_sum',join(sleeve(512),positive)),
                   ('positive_forest',singleton_forest(8,64)),
                   ('three_braid_control',sleeve(64))]
            result.update(rounds=5,warmups=1,scope='Supplied grammars; every arm includes production and independent replay. no_reduction disables only the new elementary-reduction stage, retaining priority and selected-factor proofs.')
            for name,data in cases:
                print(name,flush=True)
                previous,current=old.recognize(data),recognize(data)
                expected=previous['status']
                assert current['status']==expected and current['verified']
                arms=dict(old=lambda:old.recognize(data)['status'],
                          old_AA=lambda:old.recognize(data)['status'],
                          current=lambda:recognize(data)['status'],
                          current_AA=lambda:recognize(data)['status'],
                          no_reduction=lambda:recognize(data,use_fallback_reduction=False)['status'])
                row=measure(arms,expected,rng)
                row.update(name=name,strands=data['strands'],rules=len(data['rules']),status=expected,
                    old_resources=previous['resources'],current_resources=current['resources'],
                    old_certificate_bytes=previous['certificate_bytes'],
                    current_certificate_bytes=current['certificate_bytes'],
                    factor_order=current.get('factor_order'))
                result['cases'].append(row)
        assert before==sources(),'sources changed during experiment'
        result.update(source_sha256=before,elapsed_seconds=time.perf_counter()-begin)
        args.output.parent.mkdir(parents=True,exist_ok=True)
        args.output.write_text(json.dumps(result,indent=2)+'\n')


if __name__=='__main__':
    main()
