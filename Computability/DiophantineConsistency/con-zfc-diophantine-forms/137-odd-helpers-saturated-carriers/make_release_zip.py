#!/usr/bin/env python3
"""Build two byte-identical fixed-metadata ZIPs from the sealed release."""
import argparse,json,os,tempfile,zipfile
from pathlib import Path
import reproduce as R
ROOT=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
    out=a.output.resolve();R.need(not out.is_relative_to(ROOT),'output must be outside release');out.parent.mkdir(parents=True,exist_ok=True)
    R.verify_manifest(ROOT);summary=json.loads((ROOT/'REPLAY_SUMMARY.json').read_text());R.need(summary['status']=='PASS','replay not passed')
    for rel,expected in summary['exact_byte_comparison_sha256'].items():R.need(R.digest((ROOT/rel).read_bytes())==expected,'replay bytes changed: '+rel)
    for rel,expected in summary['execution_source_sha256'].items():R.need(R.digest((ROOT/rel).read_bytes())==expected,'executed source changed: '+rel)
    R.need(R.digest((ROOT/'REPRODUCE_PLAN.json').read_bytes())==summary['replay_plan_sha256'],'replay plan changed')
    R.need(R.digest((ROOT/'CODE_REVIEW.json').read_bytes())==summary['code_review_sha256'],'code-review binding changed')
    files=R.inventory(ROOT);files['MANIFEST.json']=ROOT/'MANIFEST.json'
    def build(path):
        with zipfile.ZipFile(path,'w',zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for rel,p in sorted(files.items()):
                info=zipfile.ZipInfo(ROOT.name+'/'+rel,(2026,10,25,0,0,0));info.create_system=3;info.external_attr=0o100644<<16;info.compress_type=zipfile.ZIP_DEFLATED
                z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
    with tempfile.TemporaryDirectory(prefix='conzfc-zip-',dir=out.parent) as td:
        one=Path(td)/'one.zip';two=Path(td)/'two.zip';build(one);build(two)
        R.need(one.read_bytes()==two.read_bytes(),'ZIP builds differ');os.replace(one,out)
    receipt=R.verify_zip(ROOT,out);receipt['independent_archive_builds_byte_identical']=True
    out.with_suffix(out.suffix+'.check.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
