"""Source-pinned integration audits and complete weighted normal-query timings."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import platform
import random
import subprocess
import sys
import time
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT))
from fastunknot.integer_codec import json_safe
BASELINE='04a66388e25507922595eb68a3ec581b4df4fb6b'
CORPUS=ROOT.parent/'reports/53/results/normal_audit_20261009_corpus.json'


def sources():
    paths=list((ROOT/'fastunknot').rglob('*.py'))+list((ROOT/'weighted_research').glob('*.py'))
    paths += [ROOT/'tests'/name for name in ('test_weighted_orbits.py','test_normal_components.py','test_normal_components_integration.py')]
    paths += [ROOT/'normal_orbit_research/fixtures.py',ROOT/'normal_orbit_research/data/projective_plane_torus.json',CORPUS]
    return {str(p.relative_to(ROOT.parent)):sha256(p.read_bytes()).hexdigest() for p in paths}


def audit():
    from weighted_research import kernel_audit, checker_audit, normal_audit
    kernel=kernel_audit.audit(10000,73091)
    checker=checker_audit.run()
    normal=normal_audit.run_audit(json.loads(CORPUS.read_text()),ROOT)
    assert not normal['failures']
    return dict(kernel=kernel,checker=checker,normal=normal,
        scope='10,000 small abstract weighted systems, 2,500 independent checker cases and mutations, and the frozen 1,275-vector Regina corpus. Supplied surfaces only; no diagram provenance or vector search.')


def benchmark():
    from weighted_research import normal_benchmark as bench
    rng=random.Random(bench.SEED);records=[]
    for kind,values in (('dimension',(4,8,16,32,64,128)),('core',(64,512,4096,32768))):
        for parameter in values:records.append(bench.case(kind,parameter,5,rng))
    return dict(records=records,seed=bench.SEED,measured_calls=200,warmup_calls=40,completed_calls=200,
        scope='Complete validated normal-vector queries including proof construction and independent replay. Four shuffled arms with an A/A copy of each method, five rounds and one retained warm-up. Three-weight versus full-coordinate censuses; raw three-weight versus canonical-core disc counts. No whole-knot timing.')


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('mode',choices=('audit','benchmark'));p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    before=sources();pins={}
    for name in ('integer_codec.py','interval_orbits.py','interval_orbit_verify.py','normal_surface_geometry.py'):
        raw=subprocess.check_output(['git','show',f'{BASELINE}:Topology/UnknotRecognition/fast/fastunknot/{name}'],cwd=ROOT)
        assert raw==(ROOT/'fastunknot'/name).read_bytes();pins[name]=sha256(raw).hexdigest()
    start=time.perf_counter();result={'audit':audit,'benchmark':benchmark}[args.mode]()
    assert before==sources()
    result.update(mode=args.mode,seconds=time.perf_counter()-start,source_sha256=before,source_hashes_unchanged=True,baseline_commit=BASELINE,unchanged_dependencies=pins,python=platform.python_version(),platform=platform.platform())
    args.output.write_text(json.dumps(json_safe(result),indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('records','source_sha256','kernel','checker','normal')},indent=2))


if __name__=='__main__':main()
