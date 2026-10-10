"""Replay adaptive discovery evidence independently of its producers."""
from contextlib import ExitStack
from hashlib import sha256
from io import BytesIO
import json
from pathlib import Path
import re
import subprocess
import sys
import tarfile
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_sector_verify import verify_sector_exhaustion,verify_sector_witness
from fastunknot.sector_planar_verify import verify_planar_sector_certificate

def read(name):return json.loads((DATA/name).read_text())

audit=read('planar-adaptive-audit.json');bench=read('planar-adaptive-benchmark.json')
repeat=read('planar-adaptive-repeat.json');pins=audit['native_source_sha256']
assert len(pins)==589 and pins==bench['native_source_sha256']==repeat['native_source_sha256']
prefix='Topology/UnknotRecognition/'
archive=subprocess.check_output(['git','archive','f25dd323e']+[prefix+p for p in pins],cwd=ROOT.parents[1])
with tarfile.open(fileobj=BytesIO(archive))as frozen:
    for p,h in pins.items():
        assert sha256(frozen.extractfile(prefix+p).read()).hexdigest()==h,p
        assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
for name,h in audit['native_baseline_source_sha256'].items():
    code=subprocess.check_output(['git','show',audit['native_baseline']+':'+prefix+'fast/fastunknot/'+name+'.py'],cwd=ROOT)
    assert sha256(code).hexdigest()==h==bench['native_baseline_source_sha256'][name]==repeat['native_baseline_source_sha256'][name]
changed=subprocess.check_output(['git','diff','--name-only',audit['native_baseline'],'f25dd323e','--',prefix+'fast'],cwd=ROOT.parents[1]).decode().splitlines()
assert set(changed)=={prefix+p for p in ('fast/fastunknot/normal_sector.py','fast/fastunknot/sector_planar.py',
    'fast/normal_orbit_research/planar_adaptive.py','fast/tests/test_sector_planar_adaptive.py')},changed
assert audit['adaptive_counts']==dict(exact_canonical_sequences=9807,adaptive_complete_sets=9807,
    discovery_queries=463,early_positive_queries=44,refined_discovery_queries=415,complete_negative_replays=419)
assert len(audit['fresh_regina'])==8 and all(r['full_list_matches_frozen']for r in audit['fresh_regina'])
disabled=['fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.normal_sector._discover_in_kernel','fastunknot.normal_sector.discover_in_sector',
    'fastunknot.sector_planar._section_plan','fastunknot.sector_planar._minimum_overlay',
    'fastunknot.sector_planar._projected_lift','fastunknot.sector_planar.sector_planar_rays',
    'fastunknot.sector_planar.sector_planar_discovery_rays','fastunknot.sector_planar.certify_planar_sector',
    'fastunknot.normal_disk_kernel.normal_compressing_disk_count',
    'fastunknot.normal_disk_kernel.canonical_disk_core','fastunknot.interval_orbits.count_orbits',
    'fastunknot.interval_orbits._count_orbits']
new=old=coverage=0
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during replay')))
    for record in audit['discovery_records']:
        raw=audit['discovery_sources'][record['source_id']]
        verify=verify_sector_witness if record['new_status']=='DISC_FOUND'else verify_sector_exhaustion
        assert verify(raw,record['certificate']);new+=1
        if record['old_positive_certificate']is not None:
            assert verify_sector_witness(raw,record['old_positive_certificate']);old+=1
    for r in read('planar-adaptive-audit-certificates.json')['records']:
        assert verify_planar_sector_certificate(r['triangulation'],r['certificate']);coverage+=1
assert (new,old,coverage)==(463,44,13)
for data,calls,warm in ((bench,280,56),(repeat,120,8)):
    assert data['completed_calls']==data['measured_calls']==calls and data['warmup_calls']==warm
    for row in data['cases']:
        values=[v for s in row['samples']+row['warmups']for v in s['measurements'].values()]
        assert all(v['completed']and v['output_sha256']==values[0]['output_sha256']for v in values)
assert 'Ran 1396 tests in 227.198s\n\nOK' in (DATA/'planar-adaptive-tests.txt').read_text()
assert 'Ran 48 tests in 1.719s\n\nOK' in (DATA/'planar-adaptive-focused.txt').read_text()
result=dict(runtime_revision='f25dd323e',source_pins=589,maintained_tests=1396,focused_tests=48,
    complete_canonical_comparisons=9807,complete_adaptive_comparisons=9807,
    producer_disabled_discovery_replays=new,producer_disabled_incumbent_positives=old,
    producer_disabled_coverage_replays=coverage,fresh_regina_full_lists=8,
    main_measured_calls=280,main_warmups=56,sparse_repeat_measured_calls=120,sparse_repeat_warmups=8)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    start=int(re.search(r'\\newlabel\{sec:planar-adaptive\}\{\{137\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{138\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('planar-adaptive-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+2))
    result.update(pdf_pages=pages,new_section_start=start,assessment_page=end,
        preexisting_overfull_warnings=warnings,visual_review=visual)
    (DATA/'planar-adaptive-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/planar_adaptive.tex',
        'synthesis/planar_adaptive_results.tex','synthesis/data/planar_adaptive_review.py',
        'synthesis/data/planar_adaptive_tables.py','synthesis/data/planar_adaptive_repeat.py',
        'fast/README.md','synthesis/README.md']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
(DATA/('planar-adaptive-review.json'if '--publication'in sys.argv else 'planar-adaptive-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
