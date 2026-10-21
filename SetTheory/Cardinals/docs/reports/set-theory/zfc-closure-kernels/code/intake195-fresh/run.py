"""Own selected replay; supplied wrappers, manifests and parent suites are not run."""
from pathlib import Path, PurePosixPath
import argparse, json, shutil, stat, subprocess, sys, time, zipfile

ap=argparse.ArgumentParser()
ap.add_argument('--packet',type=Path,required=True)
ap.add_argument('--output',type=Path,required=True)
a=ap.parse_args(); out=a.output.resolve(); out.mkdir(exist_ok=False)
p=out/'packet'; shutil.copytree(a.packet.resolve(),p)
parent=out/'parent'
with zipfile.ZipFile(p/'parent/K217_Dominated_Continuation_2026-10-20.zip') as z:
    names=set()
    for info in z.infolist():
        n=PurePosixPath(info.filename)
        assert not n.is_absolute() and '..' not in n.parts and not stat.S_ISLNK(info.external_attr>>16)
        assert info.filename not in names; names.add(info.filename)
    z.extractall(parent)
parent=parent/'K217_Dominated_Continuation_2026-10-20'
(out/'logs').mkdir()
jobs=[
 ('reconstruct',[p/'code/reconstruct216.py','--parent',parent,'--out',out/'rebuilt'],60,None,'EXACT_SOURCE_AND_TABLE_RECONSTRUCTION_PASS'),
 ('source',[p/'code/source_equivalence.py','--baseline',parent/'machine/sites217.json','--candidate',p/'source/sites216.json','--out',out/'source'],60,out/'source/verification.json','ALL_NATURAL_SOURCE_BISIMULATION_PASS'),
 ('blank-marker',[p/'code/audit216.py','--out',out/'blank-marker.json'],60,out/'blank-marker.json','MARKER_LEMMA_CANONICAL_ISOMORPHISM_AND_WHOLE_BLANK_PASS'),
 ('local-fold',[p/'code/check_joint_fold.py','--old',p/'machine/prefold217.native.tm','--new',p/'machine/k216.native.tm','--keep','164','--drop','183','--radius','4','--fuel','20','--output',out/'fold-window.json'],90,out/'fold-window.json','INDEPENDENT_ALL_TAPE_JOINT_DIAGRAM_PASS'),
 ('runtime',[p/'code/validate_native.py',p/'machine/k216.native.tm',p/'source/sites216.json',out/'runtime'],360,out/'runtime/runtime.json','UNIVERSAL_MATHEMATICAL_PASS'),
]
result={'status':'RUNNING','scope':'Five fresh direct leaves on a disposable copy. No wrapper, checksum-manifest validation, parent suite, broad search, or proof assistant. Ordinary Source149/152 calibration is inherited.','jobs':[]}
for name,args,cap,receipt,expected in jobs:
    cmd=[sys.executable,'-B',*map(str,args)]; start=time.monotonic()
    stdout=out/'logs'/(name+'.stdout'); stderr=out/'logs'/(name+'.stderr')
    with stdout.open('w') as o,stderr.open('w') as e:
        try:
            proc=subprocess.run(cmd,cwd=p,stdout=o,stderr=e,timeout=cap); rc=proc.returncode; timed=False
        except subprocess.TimeoutExpired:
            rc=None; timed=True
    data=json.loads(receipt.read_text()) if receipt and receipt.exists() else None
    status=data.get('status') if data else (expected if expected in stdout.read_text() else None)
    ok=rc==0 and status==expected
    if name=='reconstruct' and ok:
        for q,r in [('sites216.json','source/sites216.json'),('sites216.compact.json','source/sites216.compact.json'),('prefold217.native.tm','machine/prefold217.native.tm'),('k216.native.tm','machine/k216.native.tm'),('k216.tm','machine/k216.tm')]:
            ok &= (out/'rebuilt'/q).read_bytes()==(p/r).read_bytes()
    if name=='runtime' and ok:
        ok &= data['proved_cases']==data['expected_cases']==6176 and data['working_states']==216 and not data['failures']
    result['jobs'].append(dict(name=name,argv=cmd,cwd=str(p),timeout_seconds=cap,exit_code=rc,timed_out=timed,seconds=time.monotonic()-start,receipt=str(receipt) if receipt else None,status=status,accepted=bool(ok)))
    result['status']='RUNNING' if ok else 'FAIL'
    (out/'actual.json').write_text(json.dumps(result,indent=2)+'\n')
    print(name,ok,status,flush=True)
    if not ok: break
else:
    result['status']='FIVE_SELECTED_LEAVES_PASS'
(out/'actual.json').write_text(json.dumps(result,indent=2)+'\n')
print(result['status'],flush=True)
if result['status']!='FIVE_SELECTED_LEAVES_PASS': sys.exit(1)
