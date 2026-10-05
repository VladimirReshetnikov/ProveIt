#!/usr/bin/env python3
"""Reject corruption in disposable manifested payloads; preserve all originals."""
from hashlib import sha256
from pathlib import Path
import json
import shutil
import subprocess
import sys
import tempfile
ROOT=Path(__file__).resolve().parent

def need(ok,message):
    if not ok: raise RuntimeError(message)

def digest(p): return sha256(p.read_bytes()).hexdigest()

def main():
    manifest=json.loads((ROOT/'manifest.json').read_text())
    names=sorted(manifest['files'])+['manifest.json']
    before={n:digest(ROOT/n) for n in names}
    for opt in (False,True):
        cp=subprocess.run([sys.executable]+(['-O'] if opt else [])+['integrity.py'],cwd=ROOT,capture_output=True,text=True)
        need(cp.returncode==0,'pristine integrity preflight failed '+cp.stderr)
    cases=['changed tex','changed pdf','changed checker','changed fixture','missing pdf',
           'extra file','duplicate manifest key','boolean schema','boolean size','unsafe path',
           'nested ignored-name directory','symbolic link']
    results=[]
    with tempfile.TemporaryDirectory(prefix='report111-integrity-') as tmp:
        for index,label in enumerate(cases):
            root=Path(tmp)/str(index);root.mkdir()
            for n in names:
                dst=root/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/n,dst)
            if label.startswith('changed '):
                name={'changed tex':'report111.tex','changed pdf':'report111.pdf',
                      'changed checker':'checks/verify_report111.py','changed fixture':'checks/report111_fixture.json'}[label]
                p=root/name;p.write_bytes(p.read_bytes()+b'\nCORRUPTED\n')
            elif label=='missing pdf': (root/'report111.pdf').unlink()
            elif label=='extra file': (root/'unexpected.txt').write_text('unexpected')
            elif label=='nested ignored-name directory':
                p=root/'validation/build/extra.txt';p.parent.mkdir();p.write_text('unexpected')
            elif label=='symbolic link': (root/'forbidden-link').symlink_to('report111.tex')
            else:
                p=root/'manifest.json';obj=json.loads(p.read_text())
                if label=='duplicate manifest key': p.write_text(p.read_text().replace('{','{"schema":1,',1))
                else:
                    if label=='boolean schema':obj['schema']=True
                    elif label=='boolean size':obj['files']['report111.tex']['size_bytes']=True
                    elif label=='unsafe path':obj['files']['../escape']=obj['files'].pop('report111.tex')
                    p.write_text(json.dumps(obj))
            for opt in (False,True):
                cp=subprocess.run([sys.executable]+(['-O'] if opt else [])+['integrity.py'],cwd=root,capture_output=True,text=True)
                need(cp.returncode!=0,'CORRUPTION ESCAPED: '+label)
                need('RuntimeError:' in cp.stderr,'not rejected by explicit integrity guard: '+label)
                results.append({'case':label,'optimized':opt,'rejected':True})
    need(before=={n:digest(ROOT/n) for n in names},'originals changed during disposable corruption campaign')
    print(json.dumps({'status':'PASS','cases':len(cases),'rejections':len(results),
                      'originals_unchanged':True,'results':results},indent=2,sort_keys=True))
if __name__=='__main__':main()
