#!/usr/bin/env python3
"""Reviewer-owned direct-leaf preparation; never invokes supplied code."""
import hashlib, io, json, shutil, stat, sys, zipfile
from pathlib import Path, PurePosixPath

BASE = Path('/tmp/zfc-intake188-opening')
SRC = BASE/'pristine/K218_Construction_2026-10-20'
OUT = BASE/'execution'
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
    assert not OUT.exists()
    OUT.mkdir(); copy=OUT/'packet';shutil.copytree(SRC,copy)
    raw219=(copy/'portable/vendor/K219_Construction_2026-10-20.zip').read_bytes()
    z219=archive(raw219,'04813567f393b6c4015a96aba092159e9021703b4b662c7be69bd2a86497e31b')
    parent=OUT/'baseline/K219_Construction_2026-10-20'
    for i in z219.infolist():
        assert PurePosixPath(i.filename).parts[0]=='K219_Construction_2026-10-20'
        if not i.is_dir(): write(OUT/'baseline'/i.filename,z219.read(i))
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
    def job(name,script,args,limit=60):return {'name':name,'argv':[sys.executable,'-B',str(code/script),*map(str,args)],'timeout_seconds':limit}
    jobs=[
      job('01_construct','build218.py',['--parent',parent,'--output',con]),
      job('02_independent_source_fold','check_classical218.py',['--parent-sites',parent/'machine/sites219.json','--old-sites',con/'intermediate_sites205.json','--new-sites',con/'sites.json','--old-table',con/'intermediate219.tm','--unfolded-table',con/'unfolded219.tm','--new-table',con/'candidate.tm','--out',out/'independent_source_and_alias.json']),
      job('03_canonical_startup','canonicalize218.py',['--table',con/'candidate.tm','--sites',con/'sites.json','--output',out/'canonical']),
      job('04_independent_blank_startup','check_blank_startup.py',[con/'candidate.tm','--output',out/'independent_blank_startup.json']),
      job('05_full_runtime','check_runtime218.py',['--baseline',runtime,'--table',con/'candidate.tm','--sites',con/'sites.json','--output',out/'runtime'],180),
      job('06_independent_runtime_audit','audit_runtime218.py',['--baseline',runtime,'--table',con/'candidate.tm','--sites',con/'sites.json','--runtime',out/'runtime','--driver',code/'check_runtime218.py','--canonical',out/'canonical/canonicalization.json','--output',out/'runtime_audit.json'])]
    files=[code/n for n in ['common.py','source_language.py','check_source218.py','build218.py','check_classical218.py','canonicalize218.py','check_blank_startup.py','check_runtime218.py','audit_runtime218.py','data/source205.dag.json','data/rotation_paths.json','data/stage219_patch.json']]
    files += [runtime/n for n in pins]+[parent/'machine/k219.native.tm',parent/'machine/sites219.json']
    dump(OUT/'plan.json',{'status':'SOURCE_REVIEWED_DIRECT_LEAVES_READY','reviewer':'opening_encoder','jobs':jobs,'cwd':str(copy),'inputs':[desc(p) for p in files],
      'ancestry_extraction_only':{'K219':sha(raw219),'K220':sha(raw220),'K221':sha(raw221)},
      'exclusions':['No wrapper/reproduce execution','No manifest/checksum-suite execution','No ancestor verification replay','No Rocq/Coq/Lean execution'],
      'scope':'Six direct construction, source/fold, startup, full symbolic-runtime and independent audit leaves. Full source closure reviewed; exact inherited engines selected only.'})
    print(OUT/'plan.json')
if __name__=='__main__':main()
