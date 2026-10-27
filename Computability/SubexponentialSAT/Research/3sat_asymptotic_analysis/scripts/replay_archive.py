#!/usr/bin/env python3
"""Validate, safely unpack and rebuild only this report; compare text and all page pixels.
Requires Python 3, pdfLaTeX with amsmath/amsthm/hyperref/geometry/microtype,
Poppler pdftotext/pdftoppm/pdfinfo and system TeX font files. No network used.
The source paper and Lean excerpts are data, never executed or compiled.
"""
import argparse, hashlib, json, pathlib, subprocess, sys, tempfile, zipfile
from verify_bundle import verify

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args, **kw): return subprocess.run(args, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, **kw)
def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('archive'); p.add_argument('--keep', type=pathlib.Path)
    a=p.parse_args(); archive=pathlib.Path(a.archive).resolve()
    integrity=verify(archive)
    temp=None
    if a.keep: root=a.keep.resolve(); root.mkdir(parents=True,exist_ok=False)
    else: temp=tempfile.TemporaryDirectory(prefix='eth-report-replay-'); root=pathlib.Path(temp.name)
    with zipfile.ZipFile(archive) as z: z.extractall(root)
    out=root/'rebuild'; run(['bash',str(root/'scripts/build_report.sh'),str(out)])
    original=root/'report/report.pdf'; rebuilt=out/'report.pdf'
    texts=[]; pixels=[]
    for tag,pdf in [('original',original),('rebuilt',rebuilt)]:
        text=out/(tag+'.txt'); run(['pdftotext','-layout',str(pdf),str(text)]); texts.append(sha(text))
        page_dir=out/tag; page_dir.mkdir()
        run(['pdftoppm','-r','96',str(pdf),str(page_dir/'page')])
        pages=sorted(page_dir.glob('page-*.ppm')); pixels.append([sha(x) for x in pages])
    if not pixels[0] or texts[0] != texts[1] or pixels[0] != pixels[1]:
        raise RuntimeError('report text or page pixels differ from sealed PDF')
    checks={}
    for script in ['audit/check_taper_newton.py','scripts/check_report_lemmas.py','research_runtime/validate_toy_claims.py']:
        variants=[]
        for flags in [[],['-O']]:
            result_check=json.loads(run([sys.executable]+flags+[str(root/script)]).stdout)
            if str(result_check.get('status','')).lower() not in ['pass','passed','all exact toy checks passed']:
                raise RuntimeError('finite check did not pass: '+script)
            result_check.pop('python_optimization_level',None); variants.append(result_check)
        if variants[0]!=variants[1]: raise RuntimeError('normal and optimized checks differ')
        checks[script]=variants[0]
    result={'integrity':integrity,'finite_checks':checks,'rebuild':'PASS','page_count':len(pixels[0]),
            'pdf_bytes_identical':sha(original)==sha(rebuilt),'text_sha256':texts[0],
            'page_pixel_sha256':pixels[0], 'upstream_programs_executed':False,
            'scope':'Report rebuild and finite checks, not a Lean or theorem verification.'}
    print(json.dumps(result,indent=2))
    if temp: temp.cleanup()
if __name__=='__main__': main()
