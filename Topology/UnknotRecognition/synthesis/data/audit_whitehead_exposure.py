"""Replay the exposure adapter on maintained, independently classified PD inputs."""
import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
from tempfile import TemporaryDirectory
import zipfile

SYNTHESIS=Path(__file__).resolve().parents[1]
FAST=SYNTHESIS.parent/'fast'
REPO=SYNTHESIS.parents[2]
ARRIVAL='613bec60c3aa2d7bacba247732cf323adae08017'
ARCHIVE_PATH='docs/incoming/unknot_whitehead_exposure_20261008.zip'
ARCHIVE_SHA='52f91e8e3e1c50f334fedd42243c449b7ef7cd8e8044660887084c5b49102a17'
sys.path.insert(0,str(FAST))
from fastunknot import Diagram
from fastunknot.group_certificate import verify_group_certificate


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    blob=subprocess.check_output(['git','show',ARRIVAL+':'+ARCHIVE_PATH],cwd=REPO)
    assert sha256(blob).hexdigest()==ARCHIVE_SHA
    corpus_path=SYNTHESIS/'data/port-register-maintained-audit.json'
    cases={r['name']:r for r in json.loads(corpus_path.read_text())['rows']}
    gordian_path=FAST/'normal_research/gordian.json'
    cases['gordian']={'pd':json.loads(gordian_path.read_text())['pd'], 'expected_unreduced_rank':None}
    rows=[]
    with TemporaryDirectory(prefix='whitehead-exposure-audit-') as tmp:
        with zipfile.ZipFile(BytesIO(blob)) as archive:
            assert sum(i.file_size for i in archive.infolist())<100000000
            for i in archive.infolist():
                p=PurePosixPath(i.filename)
                assert not p.is_absolute() and '..' not in p.parts
                assert i.external_attr>>16 & 0o170000 != 0o120000
            archive.extractall(tmp)
        delivery=Path(tmp)/'unknot_whitehead_exposure_20261008'
        manifest=(delivery/'MANIFEST.sha256').read_text().splitlines()
        for line in manifest:
            h,n=line.split(None,1)
            assert sha256((delivery/n.lstrip('*')).read_bytes()).hexdigest()==h
        sys.path[:0]=[str(delivery/'src'),str(delivery/'integration')]
        from fastunknot_adapter import group_exposure_decide
        for name,case in cases.items():
            d=Diagram.from_pd(case['pd'])
            result=group_exposure_decide(d,seconds=5,max_work=10000000)
            record=result.get('exposure_result',{})
            exposures=sum(t['kind']=='exposure' for t in record.get('trace',[]))
            if result['status']=='UNKNOT':
                assert case['expected_unreduced_rank'] in (None,2)
                for compressed in (False,True):
                    assert verify_group_certificate(d,result['certificate'],compressed=compressed,
                        max_work=50000000,max_letters=600000,max_nodes=200000)
            else:assert result['status']=='INCONCLUSIVE'
            rows.append(dict(name=name,pd=case['pd'],expected_unreduced_rank=case['expected_unreduced_rank'],
                status=result['status'],reason=result.get('reason'),exposures=exposures,
                peak_letters=record.get('peak_stored_letters'),work=record.get('work'),
                moves=record.get('moves'),trace=record.get('trace')))
            if name=='gordian' and record:
                from fastunknot.group_certificate import _presentation, _Budget
                from whitehead_exposure.algebra import Budget,apply_whitehead,eliminate,word_graph
                from whitehead_exposure.selector import unit_bridges
                alive,words=_presentation(d,_Budget(lambda:None,600000,50000000))
                assert [list(w) for w in words]==record['initial_words']
                budget=Budget(50000000)
                for move in record['moves']:
                    if move['kind']=='whitehead':
                        words=apply_whitehead(words,move['multiplier'],set(move['subset']),budget,600000)
                    else:
                        words=eliminate(words,move['relation'],move['generator'],budget,600000)
                        alive.remove(move['generator'])
                vertices=tuple(sorted(alive|{-g for g in alive}))
                rows[-1]['residual_rank']=len(alive)
                rows[-1]['residual_letters']=sum(map(len,words))
                rows[-1]['residual_unit_bridges']=sum(len(unit_bridges(word_graph(w),vertices)) for w in words)
        def cancelled():raise TimeoutError('external audit cancellation')
        d=Diagram.from_braid(3,[1,-2])
        try:group_exposure_decide(d,check=cancelled)
        except TimeoutError:pass
        else:raise AssertionError('cancellation swallowed')
        assert group_exposure_decide(d,seconds=0)['status']=='INCONCLUSIVE'
    sources=[Path(__file__),corpus_path,gordian_path,*sorted((FAST/'fastunknot').glob('*.py'))]
    report=dict(arrival_commit=ARRIVAL,archive_sha256=ARCHIVE_SHA,manifest_entries=len(manifest),
        scope='Actual PD adapter; positive certificates independently replayed in both maintained modes and checked against the stored independent Khovanov rank oracle. No timing comparison or coverage gain is claimed.',
        diagrams=len(rows),positive=sum(r['status']=='UNKNOT' for r in rows),
        inconclusive=sum(r['status']=='INCONCLUSIVE' for r in rows),exposures=sum(r['exposures'] for r in rows),
        cancellation_propagates=True,zero_budget_inconclusive=True,rows=rows,
        source_sha256={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in sources})
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('rows','source_sha256')},indent=2))

if __name__=='__main__':main()
