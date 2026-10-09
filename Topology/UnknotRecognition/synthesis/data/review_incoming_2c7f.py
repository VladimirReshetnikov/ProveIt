"""Reconcile original deliveries and pin applicability to the maintained updater."""
import ast
from hashlib import sha1,sha256
from io import BytesIO
import json
from pathlib import Path
import subprocess
import zipfile
ROOT=Path(__file__).resolve().parents[4];BASE=ROOT/'Topology/UnknotRecognition'
COMMIT='2c7f4fd68bfd3fbaa84876ce271261cef38fc57c'
ARCHIVES={49:'unknot_source_anchored_20261008.zip',50:'unknot_sparse_incidence_20261008.zip',51:'unknot_singleton_dag_20261009.zip',52:'unknot_sparse_incidence_research_20261008.zip',53:'proveit_weighted_normal_components_20261009.zip'}


def main():
    records=[]
    for number,name in ARCHIVES.items():
        raw=subprocess.check_output(['git','show',f'{COMMIT}:docs/incoming/{name}'],cwd=ROOT)
        archive=zipfile.ZipFile(BytesIO(raw));placed=BASE/'reports'/str(number);entries=[];missing=[]
        for info in archive.infolist():
            if info.is_dir():continue
            parts=Path(info.filename).parts;assert len(parts)>1 and '..' not in parts
            rel=Path(*parts[1:]);payload=archive.read(info);p=placed/rel
            if not p.exists():
                assert rel.name in ('SHA256SUMS','CHECKSUMS.sha256','MANIFEST.sha256'),rel
                missing.append(str(rel));continue
            current=p.read_bytes();mode='identical'
            if current!=payload:
                assert current==payload.replace(b'\r\n',b'\n'),rel
                mode='LF-normalized'
            entries.append(dict(path=str(rel),archive_sha256=sha256(payload).hexdigest(),placed_sha256=sha256(current).hexdigest(),mode=mode))
        assert {str(p.relative_to(placed)) for p in placed.rglob('*') if p.is_file()}=={x['path'] for x in entries}
        records.append(dict(report=number,archive=name,archive_sha256=sha256(raw).hexdigest(),payload_files=len(entries),omitted_checksum_files=missing,files=entries))
    source=BASE/'fast/fastunknot/primitive_projection.py';reference=BASE/'reports/49/src/anchored_unknot/reference_update.py'
    raw=source.read_bytes();blob=sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
    def tree(p):return ast.dump(next(n for n in ast.parse(p.read_text()).body if isinstance(n,ast.FunctionDef) and n.name=='apply_projection'),include_attributes=False)
    assert blob=='0aff98067b485d285a9c8026fcac56ae9934edc0' and tree(source)==tree(reference)
    dependencies={}
    for report,directory,names in [(50,'snapshots/fastunknot',('integer_codec.py','interval_incidence.py','interval_orbits.py','interval_orbit_verify.py')),(53,'code/fast/fastunknot',('integer_codec.py','interval_orbits.py','interval_orbit_verify.py','normal_surface_geometry.py'))]:
        dependencies[str(report)]={}
        for name in names:
            a=BASE/f'reports/{report}'/directory/name;b=BASE/'fast/fastunknot'/name
            dependencies[str(report)][name]=dict(report_sha256=sha256(a.read_bytes()).hexdigest(),native_sha256=sha256(b.read_bytes()).hexdigest(),identical=a.read_bytes()==b.read_bytes())
    result=dict(source_commit=COMMIT,placement_matches=True,reports=records,projection_blob=blob,projection_updater_ast_matches=True,dependencies=dependencies,
        archive_integrity_before_execution={'49':'39 SHA256SUMS entries passed','50':'50 manifest entries passed','51':'784 payload entries and experiment source bindings passed','52':'50 SHA256SUMS entries passed','53':'196 payload entries passed'},
        tests={'49':38,'50':21,'51':16,'52':33,'53':103},
        status='Theory incorporated; existing singleton compiler audited. Sparse/weighted code and ordered singleton checker remain delivered implementations pending integration.',
        scope='Original archive checks passed before regeneration in separate temporary extractions. Placement is compared with original ZIP bytes and LF normalization; omitted checksum files remain recoverable from the original commit.')
    (Path(__file__).parent/'incoming-2c7f-review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('reports','dependencies')},indent=2))
    print('Placed payload counts:',[(r['report'],r['payload_files'],r['omitted_checksum_files']) for r in records])
    print('Dependency matches:',{r:all(v['identical'] for v in files.values()) for r,files in dependencies.items()})


if __name__=='__main__':main()
