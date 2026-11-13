#!/usr/bin/env python3
"""Compare the captured direct-model ancestors with the live rebuild root."""
from hashlib import sha256
import json
import os
from pathlib import Path
import sys
import time

if sys.flags.optimize:raise SystemExit('optimized Python refused')
HERE=Path(__file__).resolve().parent
SCAN=HERE/'observations/attempt01/result.json'
SCAN_PIN='01c68aaea9e3548f25589694cbb0c4582f66c0fce7b072ba0d3a3765fec950a1'
OVERLAY=Path('/tmp/compact12-ipra-expanded-coherent-20261102/lib')
OUT=HERE/'observations/overlay01'
def need(x,m):
    if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def rec(p):
    p=Path(p)
    if not os.path.lexists(p):return None
    need(p.is_file(),'dangling/non-file '+str(p))
    return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def main():
    need(not OUT.exists(),'refusing to overwrite observation')
    need(sha(SCAN)==SCAN_PIN and OVERLAY.is_dir(),'missing or changed input')
    s=json.loads(SCAN.read_text());root=s['roots']['DirectMainHalt']
    need(len(root['selected_ancestors'])==765 and not root['cone_ancestors'],'unexpected captured root')
    items=root['resolved'];need(set(items)==set(root['selected_ancestors']),'incomplete ancestor records')
    def collect():
        result={}
        for module,item in items.items():
            original=rec(item['path']);need(original==item['record'],'model object drift: '+module)
            stem=item['path'][:-len('.olean')]
            need({suffix:rec(stem+suffix) for suffix in item['companions']}==item['companions'],
                 'model companion drift: '+module)
            path=OVERLAY/(module.replace('.','/')+'.olean')
            selected=rec(path)
            result[module]={'model':original,'overlay_path':str(path),'overlay':selected,
                            'same_hash':selected is not None and selected['sha256']==original['sha256']}
        return result
    source_hash=sha(__file__);started=time.time_ns();before=collect();after=collect()
    need(before==after and sha(SCAN)==SCAN_PIN and sha(__file__)==source_hash,'inputs changed during overlay comparison')
    matched=sorted(k for k,v in before.items() if v['same_hash'])
    missing=sorted(k for k,v in before.items() if v['overlay'] is None)
    mismatched=sorted(k for k,v in before.items() if v['overlay'] is not None and not v['same_hash'])
    result={'scan_sha256':SCAN_PIN,'script_sha256':source_hash,'started_ns':started,'ended_ns':time.time_ns(),
            'overlay_root':str(OVERLAY),'matched':matched,'missing':missing,'mismatched':mismatched,
            'records':before,'inputs_unchanged':True,
            'scope':'point-in-time selected-project objects; no package/dynamic/source-origin audit'}
    OUT.mkdir(parents=True)
    (OUT/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'matched':len(matched),'missing':len(missing),'mismatched':len(mismatched)},sort_keys=True))
    need(not mismatched,'differing overlapping model ancestors')
if __name__=='__main__':main()
