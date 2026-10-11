"""Validate exact transported-sector evidence and current manuscript artifacts."""
from hashlib import sha256
import json
from pathlib import Path
import re
import sys
ROOT=Path(__file__).resolve().parents[2];DATA=ROOT/'synthesis/data'
audit=json.loads((DATA/'sector-integer-audit.json').read_text())
assert audit['retained_proofs']==len(audit['records'])==134
assert audit['producer_disabled']
assert audit['changed_existing_sources']==['fast/fastunknot/normal_sector_verify.py']
for p,h in audit['new_source_sha256'].items():assert sha256((ROOT/p).read_bytes()).hexdigest()==h,p
assert audit['driver_sha256']==sha256((DATA/'sector_integer_audit.py').read_bytes()).hexdigest()
for row in audit['records']:
    assert row['literal_accepted'] and not row['frozen_hex_accepted']
    assert row['hex_accepted']and row['signed_zero_accepted']
    assert row['large_changed_euler_rejected']and row['large_changed_coordinate_rejected']
assert re.search(r'Ran 1534 tests in [0-9.]+s\n\nOK',(DATA/'sector-integer-tests.txt').read_text())
assert re.search(r'Ran 24 tests in [0-9.]+s\n\nOK',(DATA/'sector-integer-focused.txt').read_text())
result=dict(source_pins=len(audit['new_source_sha256']),maintained_tests=1534,focused_tests=24,
    retained_source_proofs=134,hex_transport_accepted=134,signed_zero_support_accepted=134,
    frozen_hex_transport_rejected=134,large_number_mutations_rejected=268,producer_disabled=True)
if '--publication'in sys.argv:
    log=(ROOT/'synthesis/report.log').read_text()
    assert not re.search(r'undefined|Label\(s\) may have changed|Fatal error',log)
    warnings=re.findall(r'Overfull \\hbox \(([^)]*)\)',log)
    assert warnings==[f'{x}pt too wide'for x in ('12.64871','13.49065','9.04614','35.14671')],warnings
    aux=(ROOT/'synthesis/report.aux').read_text();toc=(ROOT/'synthesis/report.toc').read_text()
    start=int(re.search(r'\\newlabel\{sec:sector-integer-transport\}\{\{153\}\{(\d+)\}',aux).group(1))
    assessment=int(re.search(r'\\numberline \{154\}Assessment and recommendations\}\{(\d+)\}',toc).group(1))
    pages=int(re.search(r'Output written on report.pdf \((\d+) pages,',log).group(1))
    visual=json.loads((DATA/'sector-integer-visual-review.json').read_text())
    assert visual['pdf_sha256']==sha256((ROOT/'synthesis/report.pdf').read_bytes()).hexdigest()
    assert visual['inspected_pages']==list(range(start,assessment+3))
    paths=['synthesis/report.tex','synthesis/report.pdf','synthesis/sector_integer_transport.tex',
           'synthesis/sector_integer_results.tex','synthesis/data/sector_integer_review.py',
           'synthesis/README.md','fast/README.md']
    result.update(pdf_pages=pages,section_start=start,assessment_page=assessment,
        preexisting_overfull_warnings=warnings,visual_review=visual,
        publication_sha256={p:sha256((ROOT/p).read_bytes()).hexdigest()for p in paths})
    (DATA/'sector-integer-latex.txt').write_text(log)
(DATA/('sector-integer-publication-review.json'if '--publication'in sys.argv else 'sector-integer-runtime-review.json')).write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items()if k not in ('visual_review','publication_sha256')}))
