"""Replay the port-register delivery against actual maintained closed scans.

The adapter consumes an already allocated scalar complex. This is a provenance
and compatibility audit, not a native succinct producer or performance claim.
"""
import argparse
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path, PurePosixPath
import random
import subprocess
import sys
from tempfile import TemporaryDirectory
from time import perf_counter
import zipfile

SYNTHESIS = Path(__file__).resolve().parents[1]
FAST = SYNTHESIS.parent/'fast'
REPO = SYNTHESIS.parents[2]
ARCHIVE_SHA = '7abdc1adabfe0f1a0c3a2204db1a1f026a4f2be27aca536ce7774f47799e831f'
ARRIVAL = '820c8b3f48e8f576d41205e012f2db7a575a84b3'
ARCHIVE_PATH = 'docs/incoming/unknot_port_register_20261008.zip'
sys.path.insert(0,str(FAST))
sys.path.insert(0,str(FAST/'tests'))
from fastunknot import Diagram
from fastunknot.scan_fast import FastScan
from test_fastunknot import reference_reduced_rank, one_component


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--archive',type=Path)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    if args.archive is not None:
        archive_bytes = args.archive.read_bytes()
    elif (REPO/ARCHIVE_PATH).is_file():
        archive_bytes = (REPO/ARCHIVE_PATH).read_bytes()
    else:
        # Intake retires ZIPs after placement and omits checksum manifests.
        # Recover the immutable original rather than trust a modified package.
        archive_bytes = subprocess.check_output(['git','show',ARRIVAL+':'+ARCHIVE_PATH],cwd=REPO)
    assert sha256(archive_bytes).hexdigest()==ARCHIVE_SHA
    started=perf_counter()
    with TemporaryDirectory(prefix='port-register-audit-') as tmp:
        with zipfile.ZipFile(BytesIO(archive_bytes)) as archive:
            assert sum(i.file_size for i in archive.infolist())<100000000
            for info in archive.infolist():
                p=PurePosixPath(info.filename)
                assert not p.is_absolute() and '..' not in p.parts
                assert info.external_attr>>16 & 0o170000 != 0o120000
            archive.extractall(tmp)
        delivery=Path(tmp)/'unknot_port_register_20261008'
        manifest=(delivery/'MANIFEST.sha256').read_text().splitlines()
        for line in manifest:
            expected,name=line.split(None,1)
            assert sha256((delivery/name.lstrip('*')).read_bytes()).hexdigest()==expected
        sys.path.insert(0,str(delivery/'src'))
        from portkh.explicit import from_closed_fastscan
        from portkh.complexes import analyze
        from portkh.minimize import minimize_ports
        rng=random.Random(261008109)
        cases=[]
        for name in ('trefoil','figure_eight','hard_unknot_8'):
            d=Diagram.from_json(json.loads((FAST/'examples'/(name+'.json')).read_text()))
            cases.extend([(name,d),(name+'-mirror',d.mirror())])
        while len(cases)<30:
            strands=rng.randrange(2,5)
            word=[rng.choice((-1,1))*rng.randrange(1,strands) for _ in range(rng.randrange(1,8))]
            if not one_component(strands,word):continue
            cases.append(('seeded-'+str(len(cases)),Diagram.from_braid(strands,word)))
        rows=[];open_rejections=0
        for name,d in cases:
            expected=2*reference_reduced_rank(d)
            shuffled=list(range(d.crossings));rng.shuffle(shuffled)
            orders=[list(range(d.crossings)),list(reversed(range(d.crossings))),shuffled]
            for order in orders:
                for tail in (0,2):
                    scan=FastScan(max_objects=30000,shape_cache=False)
                    for step,index in enumerate(order):
                        scan.add_crossing(d.pd[index],reduce_now=step<d.crossings-tail)
                        if step==0 and scan.points:
                            try:from_closed_fastscan(scan)
                            except ValueError:open_rejections+=1
                            else:raise AssertionError('open frontier admitted')
                    scan.check_d_squared()
                    presentation=from_closed_fastscan(scan)
                    result=analyze(presentation)
                    smaller,report=minimize_ports(presentation)
                    replay=analyze(smaller)
                    assert result['topological_verdict'] is None and replay['topological_verdict'] is None
                    assert result['homology_dimension']==replay['homology_dimension']==expected
                    scan.eliminate()
                    assert scan.total_rank()==expected
                    rows.append(dict(name=name,pd=d.pd,order=order,tail=tail,
                        expected_unreduced_rank=expected,allocated_bridge_dimension=presentation.dimension,
                        ports=presentation.ports,minimized_ports=smaller.ports,
                        core_shape=result['core_shape'],base_homology=result['base_homology_dimension'],
                        register_length=max(b.register.length for b in presentation.blocks),
                        topological_verdict=result['topological_verdict']))
    data=dict(archive_sha256=ARCHIVE_SHA,verified_manifest_entries=len(manifest),seed=261008109,
        scope='actual maintained FastScan closures, original/reversed/shuffled orders, full cancellation or last two crossings uncancelled; independent dense reduced cube times two is the oracle',
        nonempty_one_component_diagrams=len(cases),closed_comparisons=len(rows),open_frontier_rejections=open_rejections,
        maximum_ports=max(r['ports'] for r in rows),maximum_bridge_dimension=max(r['allocated_bridge_dimension'] for r in rows),
        maximum_register_length=max(r['register_length'] for r in rows),
        elapsed_seconds=perf_counter()-started,rows=rows,
        limitation='The adapter first allocates the whole scalar input. All registers have length zero; this does not establish compression or a recognition speedup.',
        source_sha256={str(p.relative_to(REPO)):sha256(p.read_bytes()).hexdigest() for p in
            (FAST/'fastunknot/scan_fast.py',FAST/'fastunknot/planar.py',FAST/'fastunknot/diagram.py',
             FAST/'tests/test_fastunknot.py',Path(__file__))})
    args.output.write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps({k:v for k,v in data.items() if k not in ('rows','source_sha256')},indent=2))


if __name__=='__main__':main()
