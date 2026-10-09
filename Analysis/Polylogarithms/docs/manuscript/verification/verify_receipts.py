"""Check that the published source and PDF still match the recorded checks."""
from pathlib import Path
import hashlib, json
B=Path(__file__).resolve().parents[1]
hashes=json.loads((B/'verification/source-sha256.json').read_text(encoding='utf-8'))
changed=[name for name,expected in hashes.items()
         if hashlib.sha256((B/name).read_bytes().replace(b'\r\n',b'\n')).hexdigest()!=expected]
pdfhash=hashlib.sha256((B/'polylogarithms.pdf').read_bytes()).hexdigest()
build=json.loads((B/'verification/build-results.json').read_text(encoding='utf-8'))
render=json.loads((B/'verification/pdf-inspection.json').read_text(encoding='utf-8'))
wl=json.loads((B/'verification/wolfram-results.json').read_text(encoding='utf-8'))
mp=json.loads((B/'verification/mpmath-results.json').read_text(encoding='utf-8'))
result=dict(changed_sources=changed,pdf_sha256=pdfhash,
            pdf_matches_build=pdfhash==build['pdf_sha256'],
            pdf_matches_render=pdfhash==render['pdf_sha256'],
            converged_build=build['passed'],pdf_static_checks=render['static_passed'],
            wolfram_checks=len(wl['checks']),wolfram_passed=wl['all_pass'],
            mpmath_checks=len(mp['checks']),mpmath_passed=mp['all_pass'])
result['passed']=not changed and all(result[k] for k in
('pdf_matches_build','pdf_matches_render','converged_build','pdf_static_checks','wolfram_passed','mpmath_passed'))
(B/'verification/receipt-integrity.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
print(json.dumps(result,indent=2))
raise SystemExit(0 if result['passed'] else 1)
