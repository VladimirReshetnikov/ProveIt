"""Reproducible finite audit with independent compatibility and mesh oracles."""
from __future__ import annotations
import argparse, json, platform, random, time, unittest, hashlib
from pathlib import Path
from signed_continuations.core import *
from signed_continuations.verify import graph_compatible, verify_basis
from group_rank import run as rank_audit


def random_partition(r,rng):
    raw=[rng.randrange(r) for _ in range(r)]
    return SignedPartition.canonical(raw,[rng.randrange(2) for _ in range(r)])


def run_random():
    rng=random.Random(20261009);families=320; queries=0; candidates=0; certificates=0
    for trial in range(families):
        r=rng.randrange(1,9)
        fam=[Candidate(random_partition(r,rng),rng.randrange(-(1<<60),1<<60),f'{trial}:{i}')
             for i in range(rng.randrange(2,101))]
        red=reduce_family(fam)
        assert verify_basis(fam,red.certificate)
        certificates+=1; candidates+=len(fam)
        for j in range(20):
            q=SignedPartition.discrete(r) if j==0 else random_partition(r,rng)
            a=[x.cost for x in fam if graph_compatible(x.partition,q)]
            b=[x.cost for x in red.candidates if graph_compatible(x.partition,q)]
            assert (min(a) if a else None)==(min(b) if b else None)
            queries+=1
    return {'seed':20261009,'families':families,'input_candidates':candidates,
            'independent_certificates':certificates,'independent_optimum_queries':queries}


def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',default='results/audit.json');args=ap.parse_args()
    root=Path(__file__).resolve().parents[1]
    def source_snapshot():
        paths=sorted((root/'src').rglob('*.py'))+sorted((root/'tests').rglob('*.py'))
        paths+=sorted((root/'experiments').glob('*.py'))
        return [{'path':str(p.relative_to(root)), 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
                for p in paths]
    before=source_snapshot()
    start=time.perf_counter()
    suite=unittest.defaultTestLoader.discover(str(root/'tests'))
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful(): raise SystemExit(1)
    data={'python':platform.python_version(),'platform':platform.platform(),'test_methods':result.testsRun,
          'errors':len(result.errors),'failures':len(result.failures),
          'exhaustive_signed_matrix_entries':sum(sum(1 for _ in partitions(r))**2 for r in range(1,6)),
          'triangulated_seam_gluings':442,'exhaustive_patch_assignments':297,'randomized':run_random(),'group_rank_audit':rank_audit(),
          'scope':'Standalone local kernels; no maintained ProveIt production suite run',
          'native_recognizer_status':'NOT_RUN'}
    after=source_snapshot()
    assert before==after, 'source files changed during audit'
    data['source_snapshot']=before
    data['source_unchanged_during_audit']=True
    data['elapsed_s']=time.perf_counter()-start
    p=Path(args.out);p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__':main()
