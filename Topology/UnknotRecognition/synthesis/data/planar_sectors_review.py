"""Replay frozen runtime evidence and independently check publication claims."""
import ast
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

ROOT=Path(__file__).resolve().parents[2]
DATA=ROOT/'synthesis/data'
sys.path.insert(0,str(ROOT/'fast'))
from fastunknot import Diagram
from fastunknot.cocycle_lex_verify import verify_cocycle_edge_span,inspect_lex_cocycle_certificate
from fastunknot.normal_seed_verify import verify_normal_seed_certificate
from fastunknot.normal_component_verify import verify_normal_component_certificate
from fastunknot.sector_planar_verify import verify_planar_sector_certificate


def read(name):return json.loads((DATA/name).read_text())


def frozen_pins(revision,pins):
    prefix='Topology/UnknotRecognition/'
    data=subprocess.check_output(['git','archive',revision]+[prefix+p for p in pins],cwd=ROOT.parents[1])
    with tarfile.open(fileobj=BytesIO(data))as archive:
        for p,h in pins.items():
            assert sha256(archive.extractfile(prefix+p).read()).hexdigest()==h,(revision,p)


class StripDocs(ast.NodeTransformer):
    def visit(self,node):
        node=super().visit(node)
        if isinstance(node,(ast.Module,ast.ClassDef,ast.FunctionDef,ast.AsyncFunctionDef)):
            if node.body and isinstance(node.body[0],ast.Expr)and isinstance(node.body[0].value,ast.Constant)and isinstance(node.body[0].value.value,str):
                node.body=node.body[1:]
        return node


audit=read('planar-sectors-audit.json');bench=read('planar-sectors-benchmark.json')
repeat=read('planar-sectors-benchmark-repeat.json');family=read('planar-sectors-family.json')
pins=audit['native_source_sha256']
assert len(pins)==587 and bench['native_source_sha256']==pins==repeat['native_source_sha256']
frozen_pins('cc44aae87',pins)
changed=[]
for p,h in pins.items():
    if sha256((ROOT/p).read_bytes()).hexdigest()!=h:changed.append(p)
assert changed==['fast/fastunknot/normal_sector.py'],changed
old=subprocess.check_output(['git','show','cc44aae87:Topology/UnknotRecognition/'+changed[0]],cwd=ROOT)
assert ast.dump(StripDocs().visit(ast.parse(old)))==ast.dump(StripDocs().visit(ast.parse((ROOT/changed[0]).read_text())))
for name in ('sector_planar.py','sector_planar_verify.py','sector_sparse.py'):
    assert (ROOT/'fast/fastunknot'/name).read_bytes()==(ROOT/'reports/80/code/fastunknot'/name).read_bytes()
for label in ('native_baseline_source_sha256',):
    source=subprocess.check_output(['git','show',audit['native_baseline']+':Topology/UnknotRecognition/fast/fastunknot/normal_sector.py'],cwd=ROOT)
    assert sha256(source).hexdigest()==audit[label]==bench[label]==repeat[label]
assert audit['counts']['audited_sectors']==9807 and audit['counts']['d3_new_sectors']==463
assert audit['native_dispatch']==dict(auto_comparisons=9807,low_dimension_legacy_exact=9344,new_nullity_three=463)
assert len(audit['fresh_regina'])==8 and all(r['full_list_matches_frozen']for r in audit['fresh_regina'])
assert family['native_component_queries']==40 and family['regina_surface_classifications']==28
assert family['regina_complete_standard_enumerations']==4 and family['canonical_formula_grid_cases']==300

coverage=[]
for filename in ('planar-sectors-audit-certificates.json','planar-sectors-family-certificates.json'):
    coverage += [(r['triangulation'],r['certificate'])for r in read(filename)['records']]
for filename in ('planar_coverage_certificates.json','double_cap_coverage_certificates.json'):
    bundle=json.loads((ROOT/'reports/80/evidence'/filename).read_text())
    coverage += [(r['triangulation'],r['certificate'])for r in bundle['records']]
coverage += [(r['source']['triangulation'],r['certificate'])for r in bench['coverage_capacity']]
assert len(coverage)==38
lex=read('lex-audit.json');lexbench=read('lex-benchmark.json');lexinitial=read('lex-benchmark-initial.json')
assert len(lex['source_sha256'])==572
assert lex['source_sha256']==lexbench['source_sha256']==lexinitial['source_sha256']
frozen_pins('a99270fa0',lex['source_sha256'])
assert len(lex['source_cases'])==85 and lex['legacy_exact_comparisons']==85
assert lex['old_positives']==lex['new_positives']==24 and lex['regina_checks']==75
assert len(lex['arithmetic_records'])==84 and len(lex['source_proofs'])==19
assert sum(r['certificate']['secondary']['kind']=='minimum-span'for r in lex['arithmetic_records'])==81
disabled=['fastunknot.normal_sector.build_sector_kernel','fastunknot.normal_sector.sector_rays',
    'fastunknot.sector_planar.sector_planar_plan','fastunknot.sector_planar._clip_polygon',
    'fastunknot.sector_planar._projected_lift','fastunknot.sector_sparse.PreparedSectorSource.build',
    'fastunknot.cocycle_lex.minimize_cocycle_edge_span','fastunknot.cocycle_lex._prepared_minimize_edge_span',
    'fastunknot.cocycle_lex._minimize_difference','fastunknot.cocycle_euler_flow._minimize_difference',
    'fastunknot.cocycle_span.minimize_cocycle_span','fastunknot.normal_cocycle.rank_one_cocycle_seed',
    'fastunknot.normal_cocycle.local_coordinates','fastunknot.interval_orbits.count_orbits',
    'fastunknot.interval_orbits._count_orbits']
component_replays=0
with ExitStack()as stack:
    for name in disabled:stack.enter_context(patch(name,side_effect=AssertionError('producer called during independent replay')))
    for raw,certificate in coverage:assert verify_planar_sector_certificate(raw,certificate)
    for r in lex['arithmetic_records']:
        assert verify_cocycle_edge_span(r['triangulation'],r['heights'],r['certificate'])
        proof=r['outer_certificate'];summary=inspect_lex_cocycle_certificate(Diagram.from_pd(proof['input_pd']),proof)
        assert summary is not None and summary['components']==summary['orientable_components']==1
    for proof in lex['source_proofs']:assert verify_normal_seed_certificate(Diagram.from_pd(proof['input_pd']),proof)
    for source in family['records']:
        for r in source['rays']+source['mixed_directions']:
            assert verify_normal_component_certificate(source['source']['triangulation'],r['coordinates'],r['native_census']['certificate'])
            component_replays+=1
assert component_replays==40
for record,calls,warmups in [(bench,220,44),(repeat,60,4),(lexbench,220,44),(lexinitial,220,44)]:
    assert record['completed_calls']==record['measured_calls']==calls and record['warmup_calls']==warmups
for number,count in ((76,52),(77,47),(78,66),(79,36)):
    assert re.search(r'Ran '+str(count)+r' tests in [\d.]+s\n\nOK', (DATA/f'incoming-eaad-{number}-tests.txt').read_text())
assert read('incoming-eaad-76-audit.json')['status']=='PASS'
assert read('incoming-eaad-77-audit.json')['bank_criterion']['all_banks_checked']==32768
assert read('incoming-eaad-78-audit.json')['geometry']['lexicographic_connected_outputs']==100
assert read('incoming-eaad-79-exhaustion-replay.json')['covered_endpoint_replays']==124
assert sum(read(f'incoming-eaad-79-{name}-replay.json')['strict_descent_replays']for name in ('exhaustion','descent'))==18
assert read('incoming-eaad-81-summary.json')['status']=='PASS'
for name,count in [('new_tests',22),('baseline_integration',8)]:
    assert re.search(r'Ran '+str(count)+r' tests in [\d.]+s\n\nOK',(DATA/f'incoming-eaad-81-{name}.txt').read_text())
assert re.search(r'Ran 39 tests in [\d.]+s\n\nOK',(DATA/'incoming-eaad-80-regression_tests.txt').read_text())
assert read('incoming-eaad-81-abstract_audit.json')['trials']==304
assert read('incoming-eaad-81-certificate_audit.json')['assertions']==96
assert read('incoming-eaad-81-euler_corner_audit.json')['counts']['cases']==607
assert 'Ran 1391 tests in 250.052s\n\nOK' in (DATA/'planar-sectors-full-tests.txt').read_text()
assert 'Ran 72 tests in 2.205s\n\nOK' in (DATA/'planar-sectors-focused.txt').read_text()

result=dict(planar_runtime_revision='cc44aae87',edge_first_runtime_revision='a99270fa0',
    preserved_reports=list(range(76,82)),historical_planar_pins=587,historical_edge_first_pins=572,
    current_docstring_only_changes=changed,maintained_tests=1391,eligible_sectors=9807,
    new_nullity_three_sectors=463,exact_legacy_queries=9344,fresh_regina_full_enumerations=12,
    producer_disabled_coverage_replays=38,producer_disabled_lex_arithmetic_replays=84,
    producer_disabled_lex_source_replays=19,producer_disabled_family_component_replays=40,
    fresh_standalone_tests=dict(report76=52,report77=47,report78=66,report79=36,report80=39,report81=30),
    normalized_Euler_queries=607)
if '--publication' in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    aux=(ROOT/'synthesis/report.aux').read_text()
    starts={label:int(re.search(r'\\newlabel\{'+label+r'\}\{\{'+str(n)+r'\}\{(\d+)\}',aux).group(1))
        for label,n in [('sec:incoming-eaad',133),('sec:cocycle-lex-native',134),('sec:planar-sectors-native',135),('sec:planar-overlay-refinements',136)]}
    result.update(pdf_pages=pages,section_starts=starts,preexisting_overfull_warnings=warnings,
        pdf_sha256=sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest())
    visual=read('planar-sectors-visual-review.json')
    assert visual['pdf_sha256']==result['pdf_sha256'] and visual['inspected_pages'][0]==min(starts.values())
    result['visual_review']=visual
    (DATA/'planar-sectors-latex.txt').write_text('\n'.join(line.rstrip()for line in log.splitlines()).rstrip()+'\n')
    result['publication_sha256']={str(p.relative_to(ROOT)):sha256(p.read_bytes()).hexdigest()
        for p in [ROOT/'synthesis/report.tex',ROOT/'synthesis/report.pdf',ROOT/'synthesis/incoming_eaad.tex',
                  ROOT/'synthesis/cocycle_lex.tex',ROOT/'synthesis/planar_sectors.tex',
                  ROOT/'synthesis/planar_sectors_results.tex',ROOT/'synthesis/planar_overlay_refinements.tex',
                  ROOT/'fast/README.md',ROOT/'reports/README.md',ROOT/'synthesis/README.md',
                  DATA/'planar_sectors_review.py',DATA/'planar_sectors_tables.py',
                  DATA/'planar_sectors_repeat.py']}
(DATA/('planar-sectors-review.json'if '--publication'in sys.argv else 'planar-sectors-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
