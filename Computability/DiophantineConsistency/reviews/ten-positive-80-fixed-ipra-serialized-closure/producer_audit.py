#!/usr/bin/env python3
"""Check retained producer receipts for newly read selected project headers."""
from hashlib import sha256
from pathlib import Path
import json

H = Path(__file__).resolve().parent
D = H.parents[1]
SCAN = H/'observations/attempt01/result.json'
RESEARCH = D/'research'
SYSROOT = Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')

def sha(p):
    return sha256(Path(p).read_bytes()).hexdigest()

def need(ok,msg):
    if not ok:
        raise RuntimeError(msg)

x = json.loads(SCAN.read_text())
need(x['status']=='PASS', 'scan failed')
index = {}
for path in RESEARCH.glob('**/observations/*/terminal.json'):
    try:
        t = json.loads(path.read_text())
        root = Path(t['output_root'])
        command = t['command']
        out = Path(command[command.index('-o')+1])
        if t.get('exit') != 0 or t.get('reason') is not None or not out.is_file():
            continue
        if t.get('object_sha256') != sha(out):
            continue
        index.setdefault(str(out.resolve()), []).append((path,t))
    except (OSError,ValueError,KeyError,TypeError,IndexError):
        continue

matched, unmatched, explicit, observed = {}, [], {}, {}
for name, imports in x['fresh_headers'].items():
    sel = x['project'][name]['selected']
    options = index.get(sel['real_path'], [])
    if not options:
        unmatched.append(name)
        continue
    path, receipt = options[-1]
    matched[name] = {'receipt':str(path), 'receipt_sha256':sha(path), 'output_sha256':sel['sha256']}
    pins = receipt.get('pins',{}).get('direct_imports',{})
    if pins:
        need(set(pins) == set(i for i in imports if i != 'Init'), 'direct pin list differs '+name)
        for dep, depinfo in pins.items():
            actual = x['project'].get(dep,{}).get('selected',x['outside'].get(dep))
            need(actual is not None and actual['sha256']==depinfo['sha256'], 'pinned dependency differs '+name+' '+dep)
        explicit[name] = sorted(pins)
    pathstr = receipt.get('lean_path')
    if isinstance(pathstr,str):
        roots = [Path(p) for p in pathstr.split(':')] + [SYSROOT]
        checked = []
        for dep in set(imports):
            rel=dep.replace('.','/')+'.olean'
            choices=[r/rel for r in roots if (r/rel).is_file()]
            need(choices, 'unresolved producer path '+name+' '+dep)
            final = x['project'].get(dep,{}).get('selected',x['outside'].get(dep))
            need(final is not None and sha(choices[0])==final['sha256'], 'current producer resolution differs '+name+' '+dep)
            checked.append(dep)
        observed[name] = sorted(checked)
result = {'status':'PASS','scan_sha256':sha(SCAN), 'matched':matched, 'unmatched':sorted(unmatched),
          'receipt_direct_pins':explicit, 'current_producer_path_resolutions':observed,
          'scope':'current re-resolution of retained producer paths and their explicitly pinned direct imports; unpinned producer-time dependencies and unmatched receipts are not authenticated'}
out=H/'observations/producer-audit01.json'
need(not out.exists(),'observation exists')
out.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({'status':'PASS','fresh':len(x['fresh_headers']),'matched':len(matched),
                  'unmatched':len(unmatched),'receipt_direct_pins':len(explicit),
                  'current_producer_paths':len(observed),'output_sha256':sha(out)},sort_keys=True))
