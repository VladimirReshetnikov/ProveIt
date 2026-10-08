"""Audit the delivered shear adapter on actual maintained PD presentations.

This is an offline experiment. It installs legacy moves only, keeps every
relator slot and alive generator, and independently replays complete traces.
No production dispatch or timing conclusion is implied.
"""
import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import perf_counter
from unittest.mock import patch
import zipfile

SYNTHESIS = Path(__file__).resolve().parents[1]
FAST = SYNTHESIS.parent/'fast'
REPO = SYNTHESIS.parents[2]
ARRIVAL = '2b6068c60470b9f67e1f9c652c4701b567aff0bf'
ARCHIVE_PATH = 'docs/incoming/unknot_integral_shears_20261008.zip'
ARCHIVE_SHA = 'd4e801c087157dff239cd6db45e13386ce6275b30ad877fed021e5d9f2e8a326'
sys.path.insert(0,str(FAST))
from fastunknot import Diagram
from fastunknot.compressed_words import WordArena, CompressedLimit
from fastunknot.compressed_search import _search
from fastunknot.group_certificate import (
    _Budget, _presentation, _whitehead_cut, _certificate_version,
    verify_group_certificate, GroupLimit)
from fastunknot.whitehead_power import power_profile

class AfterSingletons(Exception):
    pass

def stop_at_whitehead(*args):
    raise AfterSingletons


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    blob=subprocess.check_output(['git','show',ARRIVAL+':'+ARCHIVE_PATH],cwd=REPO)
    assert sha256(blob).hexdigest()==ARCHIVE_SHA
    started=perf_counter()
    corpus_path=SYNTHESIS/'data/port-register-maintained-audit.json'
    corpus=json.loads(corpus_path.read_text())
    cases={r['name']:r['pd'] for r in corpus['rows']}
    rows=[]
    with TemporaryDirectory(prefix='integral-shears-audit-') as tmp:
        with zipfile.ZipFile(BytesIO(blob)) as archive:
            assert sum(i.file_size for i in archive.infolist())<100000000
            for i in archive.infolist():
                p=PurePosixPath(i.filename)
                assert not p.is_absolute() and '..' not in p.parts
                assert i.external_attr>>16 & 0o170000 != 0o120000
            archive.extractall(tmp)
        delivery=Path(tmp)/'unknot_integral_shears_20261008'
        manifest=(delivery/'SHA256SUMS').read_text().splitlines()
        for line in manifest:
            expected,name=line.split(None,1)
            assert sha256((delivery/name.lstrip('*')).read_bytes()).hexdigest()==expected
        sys.path.insert(0,str(delivery))
        from shear_kernel.adapter import prepare_step,replay_in_arena
        from shear_kernel.reference import canonical,literal_shear
        for name,pd in cases.items():
            d=Diagram.from_json({'pd':pd})
            for stage in ('raw','after_native_singletons'):
                budget=_Budget(lambda:None,200000,50000000)
                alive,words=_presentation(d,budget)
                arena=WordArena(max_nodes=200000,max_work=50000000)
                roots=[arena.cyclic_reduce(arena.from_word(w)) for w in words]
                moves=[]
                if stage=='after_native_singletons':
                    with patch('fastunknot.compressed_search._whitehead_cut',stop_at_whitehead):
                        try:_search(arena,roots,alive,moves)
                        except AfterSingletons:pass
                before=sum(arena.lengths[r] for r in roots)
                _,graph=arena.summarize(roots,whitehead=True)
                change,a,subset=_whitehead_cut(graph,arena)
                baseline=before
                if change<0:
                    _,gain,unit=power_profile(arena,roots,a,subset)
                    assert unit==change
                    baseline+=gain
                result,macros=prepare_step(arena,roots,alive)
                optimum=result.certificate['optimal_length']
                assert optimum<=baseline
                literal=[arena.expand(r,limit=200000) for r in roots]
                new,legacy=replay_in_arena(arena,roots,alive,result)
                assert legacy==macros
                selected=result.certificate['selected_multiplier']
                z=next((dict(r['potentials']) for r in result.certificate['solutions']
                        if r['multiplier']==selected),{})
                rotations=0
                for old,r,fresh in zip(literal,new,result.roots):
                    host=arena.expand(r,limit=200000)
                    direct=result.grammar.expand(fresh,200000)
                    expected=old if selected is None else literal_shear(old,selected,z)
                    assert canonical(host)==canonical(direct)==canonical(expected)
                    rotations+=host!=direct
                row=dict(name=name,pd=pd,stage=stage,alive=sorted(alive),
                    singleton_eliminations=len(moves),initial_length=before,
                    selected_power_length=baseline,shear_length=optimum,
                    strict_advantage=optimum<baseline,macro_count=len(macros),
                    literal_rotation_differences=rotations,relator_images=len(roots))
                # Continue only the legacy representatives recorded by these moves.
                # A complete verdict still needs independently reconstructed replay.
                moves.extend(legacy)
                roots[:]=new
                arena.left=min(arena.left,2000000)
                try:
                    success=_search(arena,roots,alive,moves,relator_moves=True)
                    row['continuation']='complete' if success else 'stalled'
                    if success:
                        cert=dict(version=_certificate_version(moves),
                            method='wirtinger-cyclic-group',status='UNKNOT',
                            input_pd=[list(r) for r in d.pd],moves=moves,
                            remaining_generator=next(iter(alive)))
                        for compressed in (False,True):
                            assert verify_group_certificate(d,cert,compressed=compressed,
                                max_work=50000000,max_nodes=200000,max_letters=200000)
                        row['independent_replay_modes']=['explicit','compressed']
                        row['certificate_sha256']=sha256(json.dumps(cert,sort_keys=True).encode()).hexdigest()
                except (CompressedLimit,GroupLimit):
                    row['continuation']='resource_limit'
                rows.append(row)
    sources=[Path(__file__),corpus_path,*sorted((FAST/'fastunknot').glob('*.py'))]
    report=dict(arrival_commit=ARRIVAL,archive_sha256=ARCHIVE_SHA,
        verified_manifest_entries=len(manifest),diagrams=len(cases),stages=len(rows),
        scope='Actual native Wirtinger extraction and singleton elimination, delivered legacy macro replay, then optional maintained search and independent full-source verification. This is not a performance benchmark.',
        relator_image_checks=sum(r['relator_images'] for r in rows),
        literal_rotation_differences=sum(r['literal_rotation_differences'] for r in rows),
        strict_advantages={s:sum(r['strict_advantage'] for r in rows if r['stage']==s)
            for s in ('raw','after_native_singletons')},
        continuation_counts={s:sum(r['continuation']==s for r in rows)
            for s in ('complete','stalled','resource_limit')},
        elapsed_seconds=perf_counter()-started,rows=rows,
        source_sha256={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in sources})
    args.output.write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('rows','source_sha256')},indent=2))

if __name__=='__main__':main()
