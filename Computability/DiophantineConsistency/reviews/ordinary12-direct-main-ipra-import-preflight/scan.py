#!/usr/bin/env python3
"""Scan direct-graph proof headers against the compact iPRA rebuild cone."""
from hashlib import sha256
import json
import os
from pathlib import Path
import subprocess
import sys
import time

if sys.flags.optimize: raise SystemExit('optimized Python refused')
HERE=Path(__file__).resolve().parent;D=HERE.parents[1]
B=D/'research/ordinary12-ipra-bridge'
INPUTS={
 'inventory':(B/'compact12-ipra-all-project-import-inventory/observations/attempt01/result.json','bf812db57d68117d47d3df792e4a0d6879019d442c4f0f2b0fbef8b861f363f2'),
 'cone':(B/'compact12-ipra-expanded-cone-preflight/result-v2.json','35fce2dd6720ca1f2db8c39e42ad099f5653bf6b12939fcb77db3fd0fa252ed4'),
 'square':(D/'research/ordinary12-sum-squares-endpoint-import-preflight/observations/attempt02/result.json','b15febdf3f77edc4ecdabddb3da2d9bf8735549d28869c4ec18d0669096a45ce'),
 'qcube':(D/'reviews/ordinary12-qcube92-serialized-import-independent/observations/attempt01/result.json','af847f4a3903770fd50bf7b7f09d597f748fa83ab0c3f4c0b7ae79dff192a615'),
 'collision':(D/'reviews/ordinary12-qcube92-module-collision-independent/observations/attempt01/result.json','d3f68298e20708297524c0e0e540091e184d451972fdb801ab9081c227779934'),
 'xq91':(D/'reviews/ordinary12-xq91-serialized-import-independent/observations/attempt01/result.json','87f7fad28524346b6921bda2f180f763417e98a0209063a7fae7fb579aea3787'),
 'halt':(D/'research/ordinary12-direct-main-probe/observations/haltv2-attempt01/terminal.json','67fc1a846731aab86e408e198475e2cae6a21820575a3a21a21accf8a3f15e4d'),
 'direct_base':(D/'research/ordinary12-qcube92-candidate/observations/halt2-attempt01/terminal.json','8d2d63d824e117c795566756f60c2b3de4b7bff891cdfe85e8eae728bc38556f'),
 'halt_base':(D/'research/ordinary12-xq91-candidate/observations/halt-attempt04/terminal.json','c803da72a3e41dd422dc697425bf20ccf1bb4624be67ac0138a0ce42e39310c5'),
}
HELPER=B/'compact12-ipra-all-project-import-inventory/ReadObjectImports.lean'
HELPER_PIN='886d46d27a94d512e47c4fe571654e4a432ab536f995b52bd1300324678fc10f'
LEAN=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean')
OUT=HERE/'observations/attempt01'
SUFFIXES=('.olean','.olean.private','.olean.server','.ilean','.ir','.olean.hash',
          '.olean.private.hash','.olean.server.hash','.ilean.hash','.ir.hash')
MODULES={
 'comparison':'DirectMainComparison','early':'DirectMainEarly','equivalence':'DirectMainEquivalence',
 'first':'DirectMainFirst','forward':'DirectMainForward','gap':'DirectMainGap',
 'gapbalance':'DirectMainGapBalance','graph':'DirectMainGraph','growth':'DirectMainGrowthAlgebra',
 'indices':'DirectMainIndices','main':'DirectMainMain','norm':'DirectMainNorm',
 'oriented':'DirectMainOriented','pell':'DirectMainPell','pellgrowth':'DirectMainPellGrowth',
 'portbounds':'DirectPortBounds','projection':'DirectMainProjection','quotient':'DirectMainFirstQuotient',
 'rank':'DirectMainRank','restricted':'DirectMainRestricted','transport':'DirectMainTransport',
 'window':'DirectMainWindow','xq91_halt':'XQ91Halt','xq91':'XQ91',
}
def need(x,m):
    if not x:raise RuntimeError(m)
def sha(p):return sha256(Path(p).read_bytes()).hexdigest()
def record(p):
    p=Path(p)
    if not os.path.lexists(p):return None
    need(p.is_file(),'dangling/non-file '+str(p))
    return {'sha256':sha(p),'resolved':str(p.resolve(strict=True)),
            'link':os.readlink(p) if p.is_symlink() else None}
def resource():
    procs=[]
    for p in Path('/proc').iterdir():
        if not p.name.isdigit():continue
        try:exe=(p/'exe').resolve(strict=True)
        except (OSError,RuntimeError):continue
        if exe==LEAN.resolve(strict=True):procs.append(int(p.name))
    row=next(x for x in Path('/proc/meminfo').read_text().splitlines() if x.startswith('MemAvailable:'))
    return {'time_ns':time.time_ns(),'mem_available_kib':int(row.split()[1]),'lean_pids':sorted(procs)}
def verify_inputs():
    for name,(path,digest) in INPUTS.items():need(sha(path)==digest,'input pin '+name)
    need(sha(HELPER)==HELPER_PIN,'header helper pin')
def verify_union(root,expected,count):
    actual={p.relative_to(root).as_posix():record(p) for p in root.rglob('*') if p.is_file()}
    need(len(actual)==count and actual==expected,'selected union drift '+str(root))
    return actual
def main():
    need(not OUT.exists(),'refusing to overwrite observation')
    verify_inputs();data={name:json.loads(path.read_text()) for name,(path,_) in INPUTS.items()}
    h=data['halt'];need(h['exit']==0 and h['reason'] is None and h['union_unchanged'] and h['halt_union_unchanged'],'halt receipt')
    paths=[Path(x) for x in h['lean_path'].split(':')]; package=paths[-1];direct=paths[-2];halt=paths[-3]
    base=verify_union(direct,data['direct_base']['union'],1291)
    haltbase=verify_union(halt,data['halt_base']['union'],1294)
    need(all(n in haltbase and haltbase[n]['sha256']==r['sha256'] for n,r in base.items()),'shared provider mismatch')
    root=Path(h['output_root'])/'DirectMainHalt.olean'
    need(root.is_file() and sha(root)==h['object_sha256'],'halt object mismatch')
    project_paths=[root.parent]+paths[:-1]
    def resolve(module):
        rel=Path(module.replace('.','/')+'.olean')
        found=[base/rel for base in project_paths if (base/rel).is_file()]
        return found[0] if found else None
    objects={}
    for key,module in MODULES.items():
        p=resolve(module);need(p is not None and sha(p)==h[key+'_producer_sha256'],'producer pin '+module)
        objects[module]={'path':str(p),'record':record(p)}
    need(len(objects)==24,'unexpected producer count')
    objects['DirectMainHalt']={'path':str(root),'record':record(root)}
    # Retained header sources may overlap. Each override below is paired with
    # the object hash whose header was read in that earlier observation.
    inv=data['inventory'];need(inv['complete'] and inv['overlay_unchanged'] and inv['omitted_unchanged'],'prior inventory incomplete')
    graph={m:{'imports':xs,'sha256':inv['objects'][m]['sha256'],'origin':'inventory'} for m,xs in inv['imports'].items()}
    sq=data['square']
    for m,xs in sq['added_imports'].items():graph[m]={'imports':xs,'sha256':sq['added_objects'][m]['sha256'],'origin':'square-preflight'}
    q=data['qcube']
    for m in ('QCube92','QCube92Model'):
        graph[m]={'imports':q['headers'][m],'sha256':q['objects'][m]['sha256'],'origin':'qcube-scan'}
    c=data['collision']
    graph['QCube92NamespacedExistence']={'imports':c['headers']['QCube92NamespacedExistence'],'sha256':c['object']['sha256'],'origin':'namespaced-scan'}
    graph['DiophantineConsistency.FreeJRootBinding']={'imports':c['headers']['DiophantineConsistency.FreeJRootBinding'],'sha256':c['binding']['sha256'],'origin':'namespaced-scan'}
    x=data['xq91']
    for m,xs in x['headers'].items():graph[m]={'imports':xs,'sha256':x['objects'][m]['sha256'],'origin':'xq91-scan'}
    pins={'inputs':{k:v[1] for k,v in INPUTS.items()},'helper':sha(HELPER),'lean':sha(LEAN),'scanner':sha(__file__)}
    OUT.mkdir(parents=True)
    names=sorted(objects);batches=[];new_headers={}
    for offset in range(0,len(names),16):
        nameset=names[offset:offset+16];before=resource()
        need(before['mem_available_kib']>=8*1024**2 and len(before['lean_pids'])<2,'resource guard')
        command=[str(LEAN),'-M3000','-j1','-DElab.async=false','--run',str(HELPER)]
        command += [objects[n]['path'] for n in nameset]
        start=time.monotonic();proc=subprocess.run(command,capture_output=True,text=True,timeout=60);after=resource()
        i=offset//16;(OUT/f'batch-{i:02d}.stdout').write_text(proc.stdout);(OUT/f'batch-{i:02d}.stderr').write_text(proc.stderr)
        batches.append({'command':command,'names':nameset,'exit':proc.returncode,'elapsed':time.monotonic()-start,
                        'preflight':before,'postflight':after})
        need(proc.returncode==0 and not proc.stderr,'header reader failure')
        bypath={objects[n]['path']:n for n in nameset};current=None;seen=set()
        for line in proc.stdout.splitlines():
            if line.startswith('BEGIN '):
                need(current is None and line[6:] in bypath,'unexpected BEGIN')
                current=bypath[line[6:]];need(current not in seen,'duplicate BEGIN');seen.add(current);new_headers[current]=[]
            elif line.startswith('IMPORT ') and current is not None:new_headers[current].append(line[7:])
            elif line=='END' and current is not None:current=None
            else:raise RuntimeError('unexpected header output: '+line)
        need(current is None and seen==set(nameset),'incomplete header batch')
    for n,xs in new_headers.items():
        graph[n]={'imports':xs,'sha256':objects[n]['record']['sha256'],'origin':'new-header'}
    candidate=set(data['cone']['topological_candidate']);need(len(candidate)==425,'candidate cone changed')
    def closure(module):
        seen=set();outside=set();todo=[module];observed={}
        while todo:
            m=todo.pop()
            if m in seen or m in outside:continue
            if m not in graph:
                outside.add(m)
                # A missing module in the selected project path is not an
                # external package merely because it wasn't inventoried.
                need(resolve(m) is None,'unrecorded selected project module: '+m)
                continue
            p=resolve(m);need(p is not None,'recorded project module not resolved: '+m)
            rec=record(p);need(rec['sha256']==graph[m]['sha256'],'first-resolved recorded-header mismatch: '+m)
            stem=str(p)[:-len('.olean')]
            companions={s:record(stem+s) for s in SUFFIXES}
            observed[m]={'path':str(p),'record':rec,'header_origin':graph[m]['origin'],'companions':companions}
            seen.add(m);todo.extend(graph[m]['imports'])
        return {'selected_ancestors':sorted(seen),'outside_selected_graph':sorted(outside),
                'cone_ancestors':sorted(seen&candidate),'resolved':observed}
    roots={n:closure(n) for n in ('DirectMainHalt','DirectMainEquivalence','DirectMainGap','XQ91Halt')}
    for n,info in objects.items():need(record(info['path'])==info['record'],'scanned object changed: '+n)
    for row in roots.values():
        for item in row['resolved'].values():
            stem=item['path'][:-len('.olean')]
            need(item['record']==record(item['path']) and item['companions']=={s:record(stem+s) for s in SUFFIXES},'resolved input changed')
    verify_union(direct,data['direct_base']['union'],1291);verify_union(halt,data['halt_base']['union'],1294)
    verify_inputs();need(pins['lean']==sha(LEAN) and pins['scanner']==sha(__file__),'tool changed')
    result={'pins':pins,'objects':objects,'new_headers':new_headers,'batches':batches,'roots':roots,
            'scope':'selected-project serialized headers; outside/package/dynamic and source-object ancestry inherited'}
    (OUT/'result.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({n:{'selected':len(v['selected_ancestors']),'outside':len(v['outside_selected_graph']),
                         'cone':len(v['cone_ancestors'])} for n,v in roots.items()},sort_keys=True))
if __name__=='__main__':main()
