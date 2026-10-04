#!/usr/bin/env python3
"""Fresh independent release QA. Executes inspected adapter and fixed owned checker only."""
from pathlib import Path
import hashlib,json,os,shutil,stat,subprocess,sys
BASE=Path('/workspace/shared/review-replay-projective62-20261004')
ADAPTER=Path('/workspace/shared/replay-projective-signal-shears62-20261004/replay.py')
PINS=ADAPTER.with_name('PINNED_INPUTS.json')
SCIENCE=Path('/workspace/shared/projective-signal-shears62-20261004')
AUDIT=Path('/workspace/shared/audit-projective-signal-shears62-20261004')
CASES=BASE/'test_cases_final'
CASES.mkdir(exist_ok=False)
RESULTS=[]

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot(root):
    rows=[]
    for p in [root]+sorted(root.rglob('*')):
        s=p.lstat();r={'path':'.' if p==root else p.relative_to(root).as_posix(),'mode':s.st_mode,'mtime_ns':s.st_mtime_ns,'size':s.st_size,'dev':s.st_dev,'ino':s.st_ino,'nlink':s.st_nlink}
        if stat.S_ISREG(s.st_mode):r['sha256']=digest(p)
        elif stat.S_ISLNK(s.st_mode):r['target']=os.readlink(p)
        rows.append(r)
    return rows

def flip(p):
    b=bytearray(p.read_bytes()); b[len(b)//2]^=1; p.write_bytes(b)

def prepare(name):
    root=CASES/name;root.mkdir();s=root/'relocated science λ';a=root/'relocated audit λ'
    shutil.copytree(SCIENCE,s);shutil.copytree(AUDIT,a)
    return root,s,a

def run_case(name,mutate=None,options=(),want=True,reason=None):
    root,s,a=prepare(name);o=root/'fresh output λ';p=PINS;cwd=root
    if mutate:
        changed=mutate(root,s,a,o)
        if changed:
            s,a,o,p,cwd=changed
    sb,ab=snapshot(s),snapshot(a)
    command=[sys.executable,'-I','-B',*options,str(ADAPTER),'--science-root',str(s),'--audit-root',str(a),'--pins',str(p),'--output-root',str(o)]
    process=subprocess.run(command,cwd=cwd,text=True,capture_output=True,timeout=90)
    (root/'process_stdout.txt').write_text(process.stdout);(root/'process_stderr.txt').write_text(process.stderr)
    preserved=sb==snapshot(s) and ab==snapshot(a)
    passed=(process.returncode==0)==want and preserved
    row={'case':name,'expected_success':want,'exit_code':process.returncode,'inputs_exactly_preserved':preserved,'stdout':process.stdout,'stderr':process.stderr,'passed':passed}
    if not want:
        row['no_output_created']=not o.exists()
        row['passed']=passed and not o.exists() and (reason is None or reason in process.stderr)
    else:
        receipt=json.loads((o/'replay_receipt.json').read_text())
        row['receipt']=receipt
        for name2 in ['independent_checks.json','rule44_static_review.json']:
            row['passed'] &= (o/'evidence'/name2).read_bytes()==(a/'evidence'/name2).read_bytes()
        row['passed'] &= (o/'execution_stdout.json').read_bytes()==(a/'evidence/run_stdout.json').read_bytes()
        fresh=(o/'evidence/frozen_before.json').read_bytes()
        row['passed'] &= fresh==(o/'evidence/frozen_after.json').read_bytes()
        row['historical_snapshot_differs_from_fresh']=fresh!=(a/'evidence/frozen_before.json').read_bytes()
    RESULTS.append(row)
    print(name, 'PASS' if row['passed'] else 'FAIL', flush=True)

# Relocation changes ordinary mode/mtime metadata while keeping immutable bytes.
def readonly_relocation(root,s,a,o):
    for tree in [s,a]:
        for p in [tree]+list(tree.rglob('*')):
            os.chmod(p,0o555 if p.is_dir() else 0o444)
            os.utime(p,ns=(1700000000123456789,1700000000123456789))
    trap=root/'launch cwd';trap.mkdir()
    # These inert trap sources must never be imported by isolated Python.
    for module in ['sympy','pathlib','hashlib']:
        (trap/(module+'.py')).write_text("raise RuntimeError('untrusted cwd module imported')\n")
    return s,a,o,PINS,trap
run_case('01_readonly_unicode_relocation_optimized',readonly_relocation,options=('-OO',))
run_case('02_plain_relocation')
for number,relative in [(3,'dependencies/positive_planar_PROOF.md'),(4,'dependencies/invertibility_GL2_PROOF.md'),(5,'MANIFEST.json'),(6,'SHA256SUMS.txt'),(7,'static_algebra.py')]:
    run_case(f'{number:02d}_tamper_science_'+Path(relative).name,lambda root,s,a,o,rel=relative:flip(s/rel),want=False,reason='input byte/hash mismatch')
for number,relative in [(8,'independent_static_audit.py'),(9,'AUDIT_MANIFEST.json'),(10,'SHA256SUMS.txt'),(11,'evidence/frozen_before.json'),(12,'evidence/frozen_after.json'),(13,'evidence/independent_checks.json'),(14,'evidence/rule44_static_review.json'),(15,'evidence/run_stdout.json')]:
    run_case(f'{number:02d}_tamper_audit_'+Path(relative).name,lambda root,s,a,o,rel=relative:flip(a/rel),want=False,reason='input byte/hash mismatch')
def extra_dir(root,s,a,o):(a/'unexpected').mkdir()
run_case('16_extra_empty_directory',extra_dir,want=False,reason='extra inventory entry')
def extra_file(root,s,a,o):(s/'sympy.py').write_text("raise RuntimeError('packet code executed')\n")
run_case('17_extra_python_file',extra_file,want=False,reason='extra inventory entry')
def symlink_file(root,s,a,o):
    target=root/'outside-proof.md';shutil.copy2(s/'PROOF.md',target);(s/'PROOF.md').unlink();(s/'PROOF.md').symlink_to(target)
run_case('18_science_symlink_file',symlink_file,want=False,reason='symbolic-link inventory entry')
def hardlink_file(root,s,a,o):os.link(a/'independent_static_audit.py',root/'checker-alias.py')
run_case('19_checker_hardlink',hardlink_file,want=False,reason='regular single-link')
def fifo_file(root,s,a,o):
    p=s/'RULES44.json';p.unlink();os.mkfifo(p)
run_case('20_fifo_replacement',fifo_file,want=False,reason='regular single-link')
def symlink_parent(root,s,a,o):
    alias=root/'alias';alias.symlink_to(s,target_is_directory=True)
    return s,a,alias/'output',PINS,root
run_case('21_output_symlink_parent',symlink_parent,want=False,reason='symbolic-link component')
def inside_audit(root,s,a,o):return s,a,a/'new-output',PINS,root
run_case('22_output_within_audit',inside_audit,want=False,reason='output overlaps protected')
def badpins(root,s,a,o):
    p=root/'pins.json';shutil.copy2(PINS,p);flip(p);return s,a,o,p,root
run_case('23_altered_pins',badpins,want=False,reason='pins file authentication failed')
def missing_file(root,s,a,o):(s/'dependencies/invertibility_GL2_PROOF.md').unlink()
run_case('24_missing_dependency',missing_file,want=False,reason='missing inventory entries')

summary={'adapter_sha256':digest(ADAPTER),'pins_sha256':digest(PINS),'case_count':len(RESULTS),'passed':all(r['passed'] for r in RESULTS),'results':RESULTS}
(BASE/'supplemental_results.json').write_text(json.dumps(summary,indent=2,ensure_ascii=False)+'\n')
raise SystemExit(0 if summary['passed'] else 1)
