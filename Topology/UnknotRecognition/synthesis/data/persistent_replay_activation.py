"""Deterministic replay counters for the activating native pipeline proof."""
from hashlib import sha256
import json
from pathlib import Path
import sys
import tempfile
ROOT=Path(__file__).resolve().parents[2]/'fast';sys.path.insert(0,str(ROOT))
from compressed_word_research import persistent_replay as native
from fastunknot import Diagram
from fastunknot.group_certificate import verify_group_certificate


def main():
    data=Path(__file__).parent
    source=data/'persistent-replay-pipeline.json';pipeline=json.loads(source.read_text())
    row=next(r for r in pipeline['cases'] if r['source']['name']=='survivor-10')
    key=row['samples'][0]['measurements']['current']['groups'][0]['certificate_sha256']
    certificate=pipeline['certificates'][key]
    before=native.sources()
    for p in (Path(__file__),source):before['synthesis/data/'+p.name]=sha256(p.read_bytes()).hexdigest()
    native.prior.harness.BASELINE=native.BASELINE;records={}
    with tempfile.TemporaryDirectory(prefix='unknot-persistent-activation-') as directory:
        old,search,group,hashes=native.prior.harness.baseline(directory)
        for label,diagram,verify in (('old',old.Diagram,group.verify_group_certificate),('current',Diagram,verify_group_certificate)):
            stats={};assert verify(diagram.from_pd(certificate['input_pd']),certificate,compressed=True,max_work=20000000,stats=stats)
            records[label]=stats
        assert verify_group_certificate(Diagram.from_pd(certificate['input_pd']),certificate,compressed=False,max_work=20000000)
    after=native.sources()
    for p in (Path(__file__),source):after['synthesis/data/'+p.name]=sha256(p.read_bytes()).hexdigest()
    assert before==after
    result=dict(source=row['source'],certificate_sha256=key,certificate=certificate,stats=records,source_sha256=before,
                source_hashes_unchanged=True,baseline_commit=native.BASELINE,baseline_source_sha256=hashes,
                scope='One deterministic old/current compressed replay plus literal source replay of the activating native proof. Counters describe the replay arena and exclude preceding PD reconstruction. No timing sample.')
    (data/'persistent-replay-activation.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(records,indent=2))


if __name__=='__main__':main()
