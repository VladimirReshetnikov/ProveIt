#!/usr/bin/env python3
"""Replay the complete immutable package in temporary output directories."""
import sys
if not __debug__: raise SystemExit('Assertions must be enabled; do not use -O.')
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tempfile,time
ROOT=Path(__file__).resolve().parent

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def load(p): return json.loads(p.read_text())
def pin(name,digest):
    candidates=[ROOT/name] if (ROOT/name).is_file() else []
    candidates+=list(ROOT.rglob(Path(name).name))
    assert any(p.is_file() and sha(p)==digest for p in candidates),(name,digest)
def strip_time(v):
    if isinstance(v,dict):return {k:strip_time(x) for k,x in v.items() if k not in ('seconds','elapsed_seconds')}
    if isinstance(v,list):return [strip_time(x) for x in v]
    return v

def main():
    start=time.time(); manifest=ROOT/'SHA256SUMS'; assert manifest.is_file()
    entries={}
    for line in manifest.read_text().splitlines():
        digest,name=line.split('  ',1);assert name not in entries;entries[name]=digest
        assert not Path(name).is_absolute() and '..' not in Path(name).parts
        assert sha(ROOT/name)==digest,name
    actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob('*') if p.is_file() and p.name!='SHA256SUMS'}
    assert actual==set(entries),(actual-set(entries),set(entries)-actual)
    before={name:sha(ROOT/name) for name in entries}; approvals=0;pins=0
    for fname in ['approval.json','family_approval.json','log_hierarchy_approval.json']:
        d=load(ROOT/'audits/independent'/fname);s=d['source_sha256']
        if isinstance(s,dict):
            for n,h in s.items():pin(n,h);pins+=1
        else: pin(Path(d['source_path']).name,s);pins+=1
        for group in ('audit_files','files'):
            for n,h in d.get(group,{}).items():pin(n,h);pins+=1
        if 'earlier_audit_receipt_sha256' in d:pin('audits/independent/approval.json',d['earlier_audit_receipt_sha256']);pins+=1
        approvals+=1
    d=load(ROOT/'audits/independent/source_check.json')
    pin('SOURCE_CHECK.md',d['source_check_sha256']);pin('family_approval.json',d['family_approval_sha256']);pins+=2
    d=load(ROOT/'audits/root-integrated-approval.json')
    pin('article/fixed-power-partition-asymptotics.tex',d['source_sha256'])
    pin('article/fixed-power-partition-asymptotics.pdf',d['pdf_sha256']);pins+=2;approvals+=1
    integrated=ROOT/'audits/integrated-approval.json'
    if integrated.is_file():
        d=load(integrated)
        for group in ('files','artifacts'):
            for n,h in d.get(group,{}).items():pin(n,h);pins+=1
        approvals+=1
    jobs=[
        ('checks/producer/check.py','checks/producer/verification.json','verification.json'),
        ('checks/producer/generate_log_series.py','checks/producer/log_series_verification.json','log_series_verification.json'),
        ('audits/independent/check.py','audits/independent/verification.json','verification.json'),
        ('audits/independent/check_family.py','audits/independent/family_verification.json','family_verification.json'),
        ('audits/independent/check_log_hierarchy.py','audits/independent/log_hierarchy_verification.json','log_hierarchy_verification.json')]
    with tempfile.TemporaryDirectory(prefix='oeis-fixed-power-replay-') as tmp:
        for i,(script,expected,outname) in enumerate(jobs):
            work=Path(tmp)/str(i);work.mkdir();local=work/Path(script).name;shutil.copy2(ROOT/script,local)
            env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
            r=subprocess.run([sys.executable,str(local),'--output-dir',str(work)],capture_output=True,text=True,env=env)
            assert r.returncode==0,(script,r.stdout,r.stderr)
            assert strip_time(load(work/outname))==strip_time(load(ROOT/expected)),script
            neg=subprocess.run([sys.executable,'-O',str(local),'--output-dir',str(work)],capture_output=True,text=True,env=env)
            assert neg.returncode!=0,('optimization accepted',script)
            print('PASS',script,flush=True)
    # Cross-compare the two separately implemented formal generators.
    import sympy as sp
    P=sp.symbols('P');a=load(ROOT/'checks/producer/log_series_verification.json');b=load(ROOT/'audits/independent/log_hierarchy_verification.json')
    comparisons=0
    for group in ('log_coefficients','saddle_ratio_coefficients','inverse_squared_ratio_coefficients'):
        assert set(a[group])==set(b[group])
        for j,expr in a[group].items():
            exact=sum(sp.Rational(v)*P**int(e) for e,v in b[group][j].items())
            assert sp.expand(sp.sympify(expr)-exact)==0,(group,j)
            comparisons+=1
    assert before=={name:sha(ROOT/name) for name in entries},'package mutated'
    print(json.dumps({'status':'PASS','manifest_files':len(entries),'approval_receipts':approvals,'pinned_identities':pins,'checkers':len(jobs),'formal_cross_comparisons':comparisons,'immutable':True,'seconds':round(time.time()-start,3)},indent=2))
if __name__=='__main__':main()
