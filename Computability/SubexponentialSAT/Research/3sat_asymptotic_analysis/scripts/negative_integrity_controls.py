#!/usr/bin/env python3
"""Check rejection of corruption, missing/extra entries, duplicate paths and traversal."""
import argparse, json, pathlib, tempfile, warnings, zipfile
from verify_bundle import verify

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument('archive'); a=p.parse_args()
    with zipfile.ZipFile(a.archive) as z: original=[(i.filename,z.read(i.filename)) for i in z.infolist()]
    cases={
      'changed_report':[(n,b+b'\n% tamper\n' if n=='report/report.tex' else b) for n,b in original],
      'missing_report':[(n,b) for n,b in original if n!='report/report.tex'],
      'unexpected_file':original+[('unexpected.txt',b'extra')],
      'duplicate_path':original+[('report/report.tex',b'duplicate')],
      'path_traversal':original+[('../escape.txt',b'not extracted')],
    }
    results={}
    with tempfile.TemporaryDirectory(prefix='eth-negative-') as d:
      for label,entries in cases.items():
        target=pathlib.Path(d)/(label+'.zip')
        with warnings.catch_warnings():
          warnings.simplefilter('ignore',UserWarning)
          with zipfile.ZipFile(target,'w',zipfile.ZIP_DEFLATED) as z:
            for name,content in entries: z.writestr(name,content)
        try: verify(target)
        except (ValueError, KeyError, zipfile.BadZipFile) as e: results[label]={'rejected':True,'reason':str(e)}
        else: raise RuntimeError('failed to reject '+label)
    print(json.dumps({'status':'PASS','controls':results},indent=2))
if __name__=='__main__': main()
