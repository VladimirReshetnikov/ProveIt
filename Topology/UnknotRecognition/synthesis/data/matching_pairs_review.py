"""Review actual paired matching reductions and complete query evidence."""
from contextlib import ExitStack
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot.normal_sector_verify import verify_sector_exhaustion,_matching_support_indices,_digest
from fastunknot.normal_surface_geometry import _prepare

def read(name):return json.loads((DATA/name).read_text())
audit=read('matching-pairs-audit.json');bench=read('matching-pairs-benchmark.json');pilot=read('matching-pair-pilot.json')
assert pilot['sector_cases']==3412 and pilot['source_cases']==48 and pilot['strict_pair_improvements']==50
assert pilot['remaining_incomplete_cases']==0
assert pilot['driver_sha256']==sha256((DATA/'matching_pair_pilot.py').read_bytes()).hexdigest()
assert pilot['corpus_sha256']==sha256((ROOT/'reports/57/results/discovery_corpus.json').read_bytes()).hexdigest()
assert audit['native_source_sha256']==bench['native_source_sha256']
assert audit['pilot_sha256']==bench['pilot_sha256']==sha256((DATA/'matching-pair-pilot.json').read_bytes()).hexdigest()
assert audit['corpus_sha256']==bench['corpus_sha256']==pilot['corpus_sha256']
for p,h in audit['native_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert len(audit['source_reductions'])==len(audit['source_implication_proofs'])==50
assert audit['previous_source_cases_unchanged']==188
assert len(audit['complete_queries'])==4 and len(audit['fresh_regina_sources'])==2
assert re.search(r'Ran 1540 tests in [0-9.]+s\n\nOK',(DATA/'matching-pairs-tests.txt').read_text())
assert re.search(r'Ran 22 tests in [0-9.]+s\n\nOK',(DATA/'matching-pairs-focused.txt').read_text())
disabled=('fastunknot.sector_matching_support._source_constraints','fastunknot.sector_matching_support._pair_step',
    'fastunknot.sector_matching_support.matching_support','fastunknot.normal_sector.build_sector_kernel',
    'fastunknot.normal_sector.sector_rays','fastunknot.sector_planar.sector_planar_rays')
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer used in replay')))
    for row,source in zip(audit['source_reductions'],audit['source_implication_proofs']):
        support=[tuple(x)for x in row['support']]
        retained=_matching_support_indices(_prepare(source['triangulation'],lambda:None),support,
            source['certificate'],_digest(source['triangulation']),lambda:None)
        assert retained==[i for i in range(len(support))if i not in row['new_forced']]
    for q in audit['complete_queries']:
        assert q['old']['status']==q['new']['status']
        assert verify_sector_exhaustion(q['triangulation'],q['certificate'])
        if q['name'].startswith('figure-eight-pair'):
            assert q['new']['stats']['matching_nullity']==3
            assert 'q_screen_stats'not in q['new']['stats']
            assert q['new']['stats']['bases_attempted']==7
            assert 'q_screen_stats'in q['old']['stats']
assert bench['measured_calls']==bench['completed_calls']==80 and bench['warmup_calls']==16
for row in bench['cases']:
    samples=row['samples']+row['warmups']
    assert len({v['status']for sample in samples for v in sample['measurements'].values()})==1
    for arm in ('old','old_AA','new','new_AA'):
        assert all(s['measurements'][arm]['completed']for s in samples)
        assert len({s['measurements'][arm]['certificate_sha256']for s in samples})==1
result=dict(source_pins=len(audit['native_source_sha256']),maintained_tests=1540,focused_tests=22,
    pilot_sectors=3412,pilot_sources=48,additional_source_reductions=50,previous_cases_unchanged=188,
    producer_disabled_implication_proofs=50,complete_query_certificates=4,fresh_regina_sources=2,
    measured_calls=80,warmups=16)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    start=int(re.search(r'\\newlabel\{sec:matching-pairs\}\{\{154\}\{(\d+)\}',(ROOT/'synthesis/report.aux').read_text()).group(1))
    end=int(re.search(r'\\numberline \{155\}Assessment and recommendations\}\{(\d+)\}',(ROOT/'synthesis/report.toc').read_text()).group(1))
    visual=read('matching-pairs-visual-review.json')
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,end+3))
    result.update(pdf_pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1)),
        section_start=start,assessment_page=end,visual_review=visual,preexisting_overfull_warnings=warnings)
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/matching_support.tex','synthesis/matching_pairs.tex',
        'synthesis/matching_pairs_results.tex','synthesis/make_tables.py',
        'synthesis/data/matching_pairs_tables.py','synthesis/tables/matching_pairs_queries.tex','fast/README.md','synthesis/README.md','synthesis/data/matching_pairs_review.py']
    result['publication_sha256']={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths}
    (DATA/'matching-pairs-latex.txt').write_text(log)
(DATA/('matching-pairs-publication-review.json'if '--publication'in sys.argv else 'matching-pairs-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('publication_sha256','visual_review')}))
