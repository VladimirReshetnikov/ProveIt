#!/usr/bin/env python3
"""Unpack, run authored checks normal/-O, rebuild authored PDF and compare text/pixels.
No incoming source code is run. Requires standard-library Python, pdfLaTeX and Poppler.
"""
import argparse,hashlib,json,pathlib,subprocess,sys,tempfile,zipfile
from verify_bundle import verify

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(args,**kw):return subprocess.run(args,check=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,**kw)
def stable(value):
    if isinstance(value,dict):return {k:stable(v) for k,v in value.items() if k not in ['elapsed_seconds','python_optimization_level']}
    if isinstance(value,list):return [stable(v) for v in value]
    return value

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('archive');p.add_argument('--keep',type=pathlib.Path);a=p.parse_args()
    archive=pathlib.Path(a.archive).resolve();integrity=verify(archive);temp=None
    if a.keep:root=a.keep.resolve();root.mkdir(parents=True,exist_ok=False)
    else:temp=tempfile.TemporaryDirectory(prefix='sat-round3-replay-');root=pathlib.Path(temp.name)
    with zipfile.ZipFile(archive) as z:z.extractall(root)
    checks={}
    for script in json.loads((root/'scripts/check_allowlist.json').read_text()):
        variants=[]
        for flags in [[],['-O']]:
            result=json.loads(run([sys.executable]+flags+[str(root/script)],cwd=root).stdout)
            if str(result.get('status','')).lower() not in ['pass','passed']:raise RuntimeError('check not PASS: '+script)
            variants.append(stable(result))
        if variants[0]!=variants[1]:raise RuntimeError('normal/-O mismatch: '+script)
        checks[script]=variants[0]
    out=root/'rebuild';run(['bash',str(root/'scripts/build_report.sh'),str(out)])
    original=root/'report/report.pdf';rebuilt=out/'report.pdf';texts=[];pixels=[]
    for tag,pdf in [('original',original),('rebuilt',rebuilt)]:
        txt=out/(tag+'.txt');run(['pdftotext','-layout',str(pdf),str(txt)]);texts.append(sha(txt))
        pages=out/tag;pages.mkdir();run(['pdftoppm','-r','96',str(pdf),str(pages/'page')])
        pixels.append([sha(p) for p in sorted(pages.glob('page-*.ppm'))])
    if not pixels[0] or texts[0]!=texts[1] or pixels[0]!=pixels[1]:raise RuntimeError('sealed PDF text or page pixels differ')
    print(json.dumps({'status':'PASS','integrity':integrity,'authored_checks':checks,'pdf_rebuild':'PASS',
      'page_count':len(pixels[0]),'pdf_bytes_identical':sha(original)==sha(rebuilt),'text_sha256':texts[0],
      'page_pixel_sha256':pixels[0],'upstream_programs_executed':False,
      'scope':'Reproducibility and finite component checks, not formal theorem verification.'},indent=2))
    if temp:temp.cleanup()
if __name__=='__main__':main()
