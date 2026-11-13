#!/usr/bin/env python3
"""Compare the historical and fresh source-declared fixed-port closures."""
import sys
if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B without optimization')
import hashlib,json
from pathlib import Path

HERE=Path(__file__).resolve().parent
TASK=HERE.parents[1]
OLD=Path('/tmp/ha87-full-transitive-p3xt6wra')
FRESH=Path('/tmp/current14-standard-fresh-build-20261104')
SNAP=Path('/tmp/current14-standard-fresh-source-20261104')
STAGE=TASK/'reviews/nine-variable-ipra-equal-length-stages-77-81-overlap/observations/stages-077-081'
PINS={
    OLD/'state.json':'84c3bc6f6c34c47e67278c43df8580444d32e2946844a4c40c31cfd747f33a90',
    SNAP/'manifest.json':'1e8b03cac1b2db995091dff13c749faf955fc524bf2da42a637743e9d7a53749',
    FRESH/'state.json':'f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014',
    STAGE/'author/079/receipt.json':'33f040272cf2bc0203e21521ba20d5499bb6c39adc8de02e817a2e41b334318d',
    STAGE/'terminal.json':'6caef4771720124c2fd6612df8f76758ae68eef97211c129fde431f53ace84d8',
}
def need(v,msg):
    if not v:raise RuntimeError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    for p,h in PINS.items():need(sha(p)==h,'pin mismatch '+str(p))
    old=json.loads((OLD/'state.json').read_bytes())
    fresh=json.loads((FRESH/'state.json').read_bytes())
    manifest=json.loads((SNAP/'manifest.json').read_bytes())
    stage=json.loads((STAGE/'author/079/receipt.json').read_bytes())
    terminal=json.loads((STAGE/'terminal.json').read_bytes())
    need(old['status']=='PASS' and fresh['status']=='PASS' and stage['status']=='PASS' and terminal['exit_code']==0,'producer status')
    need(stage['output']['sha256']=='79bf09c3051ad06f55abdd511c7310ccd795856f1275b6b23836f8b535e74122','stage object')
    need(sha(Path(stage['output']['resolved']))==stage['output']['sha256'],'stage object drift')
    graph=old['graph'];records={r['module']:r for r in old['records']}
    queue=['DiophantineConsistency.CurrentKernelData2011'];seen=set();external=set()
    while queue:
        n=queue.pop()
        if n in seen or n in external:continue
        if n not in graph['sources']:external.add(n);continue
        seen.add(n);queue.extend(graph['edges'].get(n,[]))
    need(len(seen)==12 and len(external)==8,'unexpected closure size')
    rows=[]
    for n in sorted(seen):
        need(n in manifest['sources'] and n in records,'missing module '+n)
        oldsource=OLD/'source-snapshots'/(n.replace('.','_')+'.lean')
        newspec=manifest['sources'][n];newsource=SNAP/newspec['snapshot_path']
        expected=graph['source_hashes'][n]
        need(sha(oldsource)==expected==sha(newsource)==newspec['sha256'],'source mismatch '+n)
        need(set(graph['edges'][n])==set(newspec['imports']),'source import mismatch '+n)
        oldobj=OLD/'lib'/(n.replace('.','/')+'.olean')
        freshobj=FRESH/'lib'/(n.replace('.','/')+'.olean')
        oldhash=records[n]['object_sha256']
        need(records[n]['exit']==0 and sha(oldobj)==oldhash,'old object mismatch '+n)
        entry=fresh['outputs'][n][str(freshobj)]
        need(entry is not None and sha(freshobj)==entry['sha256'],'fresh object mismatch '+n)
        rows.append({'module':n,'source_sha256':expected,'old_object_sha256':oldhash,
                     'fresh_object_sha256':entry['sha256'],'objects_equal':oldhash==entry['sha256']})
    # The historical overlay resolves the two key port modules to these old objects.
    overlay=Path('/tmp/nine-ipra-guarded-author-20261102-h/lib')
    for n in ('DiophantineConsistency.CurrentKernelData2011','DiophantineConsistency.CurrentMaskData2011'):
        path=overlay/(n.replace('.','/')+'.olean');oldobj=OLD/'lib'/(n.replace('.','/')+'.olean')
        need(path.resolve()==oldobj.resolve() and sha(path)==sha(oldobj),'historical overlay route '+n)
    for p,h in PINS.items():need(sha(p)==h,'post-read pin mismatch '+str(p))
    print(json.dumps({'status':'PASS','checker_sha256':sha(Path(__file__)),
        'root':'DiophantineConsistency.CurrentKernelData2011','source_modules':rows,
        'source_module_count':len(rows),'external_imports':sorted(external),
        'external_count':len(external),'old_overlay_root':str(overlay),
        'scope':'source-declared fixed-port closure and observed object hashes; no object interchange or formal numeric byte binding'},indent=2,sort_keys=True))
if __name__=='__main__':main()
