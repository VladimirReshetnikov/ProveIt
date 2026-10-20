#!/usr/bin/env python3
"""Reviewer-owned direct-leaf preparation; never invokes supplied code."""
import argparse, hashlib, io, json, shutil, stat, sys, zipfile
from pathlib import Path, PurePosixPath

def sha(b): return hashlib.sha256(b).hexdigest()
def desc(p): return {'path': str(p), 'sha256': sha(p.read_bytes()), 'size': p.stat().st_size}
def dump(p,v): p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def archive(raw, expected):
    assert sha(raw)==expected
    z=zipfile.ZipFile(io.BytesIO(raw)); names=set(); total=0
    for i in z.infolist():
        p=PurePosixPath(i.filename); n=i.filename.rstrip('/')
        assert n and not p.is_absolute() and '\\' not in n and ':' not in n and '\0' not in n
        assert all(x not in ('','.','..') for x in n.split('/')) and n not in names
        assert stat.S_IFMT(i.external_attr>>16) in (0,stat.S_IFREG,stat.S_IFDIR) and not i.flag_bits&1
        names.add(n);total+=i.file_size
        assert i.file_size<100_000_000 and total<500_000_000 and len(names)<10000
    return z
def write(p,b): p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b)
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--packet',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True)
    args=ap.parse_args();SRC=args.packet.resolve();OUT=args.output.resolve()
    assert SRC.is_dir() and SRC!=OUT and SRC not in OUT.parents
    assert not OUT.exists()
    OUT.mkdir(); copy=OUT/'packet';shutil.copytree(SRC,copy)
    raw219=(copy/'portable/vendor/K219_Construction_2026-10-20.zip').read_bytes()
    z219=archive(raw219,'04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b')
    parent=OUT/'baseline/K219_Construction_2026-10-20'
    for name in ('machine/k219.native.tm','machine/sites219.json'):
        write(parent/name,z219.read('K219_Construction_2026-10-20/'+name))
    raw220=z219.read('K219_Construction_2026-10-20/portable/vendor/K220_Construction_2026-10-20.zip')
    z220=archive(raw220,'132cbb326fcbf6e54957a03095c5f790e207f4ed8ebfb6ceb6e272f329e4ee00')
    raw221=z220.read('K220_Construction_2026-10-20/portable/vendor/K221_Construction_2026-10-20.zip')
    z221=archive(raw221,'a06c99b775193d9642a2734b7dd5fe7b72736fbdf9d9d8be438321d5e5d57ba4')
    pins={
      'portable/build221.py':'3359e8b40fefb162ca4aa1d5c5a99a368a937ec61f761c3ac6f26d573766acba',
      'portable/source_language.py':'4b355b81373a06ce2d8d99f56ac88afee8bbbd934d21f4f2729d864d9807683f',
      'portable/runtime/vendor/symbolic_runtime.py':'c22f1709a39277c59d163c613e250f27a9e239004a83f643f3bd7d44ad57f145',
      'portable/runtime/vendor/independent_runtime.py':'0d1dae10b921cc302a2211d9251ca7ec131aa63ecb040ce66720894877700346',
      'portable/runtime/reference_results/legacy_mapping.json':'26a4bff859adcc510f1faf4364a597681fec014a136bc1d00dc9ce1904ad6bbf'}
    runtime=OUT/'runtime-inputs/K221_Construction_2026-10-20'
    for n,h in pins.items():
        b=z221.read('K221_Construction_2026-10-20/'+n);assert sha(b)==h;write(runtime/n,b)
    code=copy/'portable';out=OUT/'output';out.mkdir();con=out/'construction'
    source=out/'source';source.mkdir()
    for name in ('reconstruct_source.py','dag_recipe.json'):
        shutil.copy2(code/'source'/name,source/name)
    shutil.copy2(parent/'machine/sites219.json',source/'baseline_sites219.json')
    shutil.copy2(copy/'machine/sites218.json',source/'candidate_sites218.json')
    def job(name,script,args,limit=60):
        return {'name':name,'argv':[sys.executable,'-B',str(script),*map(str,args)],'timeout_seconds':limit}
    common=['--variant','candidate218','--table',con/'candidate.tm','--source',con/'candidate.sites.json',
            '--vendor',runtime/'portable/runtime/vendor','--mapping',runtime/'portable/runtime/reference_results/legacy_mapping.json']
    jobs=[
      job('01_source_bisimulation',source/'reconstruct_source.py',[]),
      job('02_lineage_construction',code/'lineage/build_lineage.py',['--upstream-table',parent/'machine/k219.native.tm','--upstream-source',parent/'machine/sites219.json','--out',con]),
      job('03_canonical_startup',code/'canonicalize.py',['--table',con/'candidate.tm','--source',con/'candidate.sites.json','--output',out/'canonical']),
      job('04_independent_startup',code/'check_runtime.py',common+['--out',out/'startup-only','--preflight-only']),
      job('05_full_runtime',code/'check_runtime.py',common+['--out',out/'runtime'],240),
      job('06_independent_runtime_audit',code/'check_runtime.py',common+['--out',out/'runtime','--audit-only'])]
    files=[code/n for n in ['source/reconstruct_source.py','source/dag_recipe.json','lineage/build_lineage.py','lineage/build218.py','lineage/source_equivalence.py','lineage/lineage_recipe.json','lineage/basis/direct188.tm','lineage/basis/direct188.sites.json','canonicalize.py','check_runtime.py']]
    files += [runtime/n for n in pins]+[parent/'machine/k219.native.tm',parent/'machine/sites219.json']
    files += sorted(p for p in source.iterdir() if p.is_file())
    files += sorted(p for d in ('machine','certificates/source','portable/reference_results') for p in (copy/d).rglob('*') if p.is_file())
    dump(OUT/'plan.json',{'status':'SOURCE_REVIEWED_DIRECT_LEAVES_READY','reviewer':'opening_encoder','jobs':jobs,'cwd':str(copy),'inputs':[desc(p) for p in sorted(set(files))],
      'ancestry_extraction_only':{'K219':sha(raw219),'K220':sha(raw220),'K221':sha(raw221)},
      'exclusions':['No wrapper/reproduce execution','No manifest/checksum-suite execution','No ancestor verification replay','No Rocq/Coq/Lean execution','No delivered negative-control wrapper invocation'],
      'scope':'Six direct source bisimulation, deterministic lineage, canonicalization/startup, independent startup, full symbolic-runtime and independent audit leaves. Full source closure reviewed; exact inherited engines selected only. The full-runtime leaf also performs its independent audit internally; leaf six explicitly repeats only that finite audit.'})
    print(OUT/'plan.json')
if __name__=='__main__':main()
