#!/usr/bin/env python3
"""Deterministic ZIP creation; writes only outside the immutable release tree."""
from pathlib import Path
import argparse,hashlib,json,os,tempfile,zipfile
import reproduce as R
ROOT=Path(__file__).resolve().parent

def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',required=True,type=Path);a=ap.parse_args()
    out=a.output.resolve();R.need(not out.is_relative_to(ROOT),'ZIP must be outside release');out.parent.mkdir(parents=True,exist_ok=True)
    manifest=R.verify_manifest(ROOT)
    summary=json.loads((ROOT/'REPLAY_SUMMARY.json').read_text());R.need(summary['status']=='PASS','frozen replay summary is not PASS')
    for rel,expected in summary['exact_byte_comparison_sha256'].items():
        R.need(hashlib.sha256((ROOT/rel).read_bytes()).hexdigest()==expected,'frozen replay no longer matches '+rel)
    files=sorted(p for p in ROOT.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p.suffix!='.pyc')
    def build(path):
        with zipfile.ZipFile(path,'w',compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
            for p in files:
                info=zipfile.ZipInfo(ROOT.name+'/'+p.relative_to(ROOT).as_posix(),(2026,10,24,0,0,0))
                info.create_system=3;info.external_attr=(0o100644<<16);info.compress_type=zipfile.ZIP_DEFLATED
                z.writestr(info,p.read_bytes(),compress_type=zipfile.ZIP_DEFLATED,compresslevel=9)
        with zipfile.ZipFile(path) as z:R.need(z.testzip() is None,'created ZIP CRC failure')
    with tempfile.TemporaryDirectory(prefix='conzfc-zip-',dir=out.parent) as td:
        first,second=Path(td)/'first.zip',Path(td)/'second.zip';build(first);build(second)
        R.need(first.read_bytes()==second.read_bytes(),'independent ZIP builds are not byte-identical')
        raw=first.read_bytes();os.replace(first,out)
    result={'status':'PASS','archive':str(out),'bytes':len(raw),'sha256':hashlib.sha256(raw).hexdigest(),'members':len(files),'zip_crc':'PASS','independent_archive_builds_byte_identical':True,'manifest':manifest}
    receipt=out.with_suffix(out.suffix+'.check.json');receipt.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
