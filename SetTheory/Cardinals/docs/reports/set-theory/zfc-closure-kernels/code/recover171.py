#!/usr/bin/env python3
"""Recover original batch171 layouts from committed deliveries; execute no code."""
import argparse
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import zipfile

HOST=Path('SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels')

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    p.add_argument('--source',type=int,action='append',help='Local source number,81 through100; default all.')
    a=p.parse_args()
    repo=a.repo.resolve(); out=a.output.resolve()
    assert not out.exists() and not out.is_relative_to(repo)
    mapping=json.loads((repo/HOST/'data/intake171-placement.json').read_text())
    selected=set(a.source or range(81,101))
    assert selected and selected<=set(range(81,101))
    out.mkdir(parents=True)
    records=[]
    for package in mapping['sources']:
        source=80+package['manuscript_number']
        if source not in selected:
            continue
        archive=subprocess.check_output(['git','-C',str(repo),'show',package['arrival_commit']+':'+package['archive']])
        rows={r['archive_member']:r for r in mapping['files'] if r['source']==source}
        seen=set(); placed=0
        with zipfile.ZipFile(io.BytesIO(archive)) as z:
            for member in z.infolist():
                if member.is_dir():
                    continue
                rel=PurePosixPath(member.filename)
                assert not rel.is_absolute() and '..' not in rel.parts
                assert (member.external_attr>>16)&0o170000 !=0o120000
                assert member.filename not in seen
                seen.add(member.filename)
                raw=z.read(member)
                row=rows[member.filename]
                if 'target' in row:
                    assert (repo/row['target']).read_bytes()==raw, row['target']
                    placed+=1
                dest=out/f'source{source}'/rel
                dest.parent.mkdir(exist_ok=True,parents=True)
                dest.write_bytes(raw)
        assert seen==set(rows)
        records.append({'source':source,'members':len(seen),'ancillary_aliases_checked':placed})
    result={'status':'PASS','packages':records,'members':sum(r['members'] for r in records),
            'ancillary_aliases_checked':sum(r['ancillary_aliases_checked'] for r in records)}
    (out/'recovery.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':
    main()
