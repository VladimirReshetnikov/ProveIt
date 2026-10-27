#!/usr/bin/env python3
"""Build a compact deterministic bundle from explicit allowlisted evidence paths."""
import argparse, hashlib, json, pathlib, zipfile
ROOT=pathlib.Path(__file__).resolve().parent.parent
INCLUDE=[
 'README.md',
 'report/report.tex','report/research_routes.tex','report/degree_route.tex','report/report.pdf',
 'source/README.md','source/REPOSITORY_README.md','source/REPOSITORY_LICENSE',
 'source/manifest.json','source/paper.pdf','source/paper.txt',
 'source/build/main_full_version.tex','source/build/quantitative-circuits.tex',
 'source/build/quantitative-contraction.tex','source/build/quantitative-reduction.tex',
 'audit/INDEPENDENT_PAPER_AUDIT.md','audit/TAPER_AND_NEWTON_LEMMAS.tex',
 'audit/CONDITIONAL_KERNEL_REVIEW.md','audit/check_taper_newton.py',
 'audit/taper_newton_test_normal.json','audit/taper_newton_test_optimized.json',
 'audit/lean_selected/manifest.json','audit/lean_selected/SqrtLog_StatementCanonical.lean',
 'audit/lean_selected/SqrtLog_ExecutionNativeFinal.lean','audit/lean_selected/SqrtLogSpace_Final.lean',
 'research_decision/findings.md','research_runtime/CONDITIONAL_DEGREE_KERNEL.tex',
 'research_runtime/METHOD_BARRIERS.md','research_runtime/validate_toy_claims.py',
 'research_runtime/toy_validation_results.json','research_runtime/SHA256SUMS.txt',
 'research_runtime/CONTRACTION_SOURCE_ANCHORS.txt','research_runtime/REDUCTION_SOURCE_ANCHORS.txt',
 'scripts/build_bundle.py','scripts/build_report.sh','scripts/verify_bundle.py',
 'scripts/replay_archive.py','scripts/negative_integrity_controls.py','scripts/check_report_lemmas.py',
 'qa/report_lemmas_normal.json','qa/report_lemmas_optimized.json',
]

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('output',type=pathlib.Path)
    p.add_argument('--validation-summary',action='store_true'); a=p.parse_args()
    names=INCLUDE+(['qa/RELEASE_VALIDATION.json','qa/VISUAL_REVIEW.md'] if a.validation_summary else [])
    data={name:(ROOT/name).read_bytes() for name in sorted(names)}
    manifest={'format':1,'source_pin':'7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a',
              'scope':'Research report, conditional interfaces and finite checks; no new unrestricted SAT bound.',
              'files':{n:{'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()} for n,b in data.items()}}
    data['MANIFEST.sha256.json']=(json.dumps(manifest,indent=2,sort_keys=True)+'\n').encode()
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with zipfile.ZipFile(a.output,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
      for n,b in sorted(data.items()):
        i=zipfile.ZipInfo(n,(2026,10,27,0,0,0)); i.compress_type=zipfile.ZIP_DEFLATED
        i.external_attr=(0o100644<<16); z.writestr(i,b)
    size=a.output.stat().st_size
    if size>=4_000_000: raise ValueError('archive is not below 4 MB')
    print(json.dumps({'archive':str(a.output),'bytes':size,'entries':len(data),
       'sha256':hashlib.sha256(a.output.read_bytes()).hexdigest()},indent=2))
if __name__=='__main__': main()
