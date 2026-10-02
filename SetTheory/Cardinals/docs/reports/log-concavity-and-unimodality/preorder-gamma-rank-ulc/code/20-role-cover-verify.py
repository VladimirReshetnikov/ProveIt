#!/usr/bin/env python3
"""Portable exact supplementary checks. Does not formalize the ordinary proof."""
import sys
if not __debug__ or sys.flags.optimize:
    raise SystemExit('ERROR: disabled assertions are not allowed; run python3 verify.py without -O')
import hashlib,json,os,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
OLD='/workspace/shared/balanced-core-gamma-research/'
def digest(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def require(condition,message):
    if not condition:raise RuntimeError(message)
def check_hash(path,expected):require(digest(path)==expected,'Hash mismatch: '+str(path.relative_to(ROOT)))
def audit_hashes():
    base=ROOT/'proofs';folder=base/'incomplete-core/independent-audit';count=0
    full=json.loads((base/'independent-audit/balanced_real_rootedness_audit_receipt.json').read_text())
    require(full['verdict']=='approved','Complete-core audit not approved')
    for old,h in full['sha256'].items():
        check_hash(base/old.removeprefix(OLD),h);count+=1
    entries=[('star_core','STAR_CORE_REAL_ROOTEDNESS.md','STAR_CORE_INDEPENDENT_AUDIT.md'),('one_missing_edge','ONE_MISSING_EDGE_REAL_ROOTEDNESS.md','ONE_MISSING_EDGE_INDEPENDENT_AUDIT.md'),('disjoint_core_edges','DISJOINT_CORE_EDGES_REAL_ROOTEDNESS.md','DISJOINT_CORE_EDGES_INDEPENDENT_AUDIT.md'),('two_by_two_role_cover','TWO_BY_TWO_ROLE_COVER_THEOREM.md','TWO_BY_TWO_ROLE_COVER_INDEPENDENT_AUDIT.md')]
    for name,proof,audit in entries:
        r=json.loads((folder/(name+'_audit_receipt.json')).read_text());require(r['verdict']=='approved','Audit not approved: '+name)
        check_hash(base/'incomplete-core'/proof,r['proof_sha256']);check_hash(folder/audit,r['audit_sha256']);count+=2
        for key in ['code_sha256','independent_code_sha256']:
            if isinstance(r.get(key),dict):
                for old,h in r[key].items():check_hash(base/old.removeprefix(OLD),h);count+=1
        if name=='star_core':
            check_hash(base/'independent-audit/check_star_monomer.cpp',r['independent_code_sha256']);check_hash(base/'independent-audit/check_star_monomer.log',r['independent_log_sha256']);count+=2
    return count
start=time.time();records=[]
count=audit_hashes();print('PASS pinned proof/audit/checker hashes:',count,flush=True)
manifest=ROOT/'SHA256SUMS'
if manifest.exists():
    rows=manifest.read_text().splitlines()
    for line in rows:
        h,name=line.split('  ',1);p=ROOT/name;require(p.is_file(),'Missing manifest file '+name);check_hash(p,h)
    print('PASS archive SHA256SUMS:',len(rows),'files',flush=True)
for name in ['check_rayleigh_aggregate.py','check_disjoint_rayleigh_aggregate.py']:
    p=ROOT/'proofs/incomplete-core/independent-audit'/name
    r=subprocess.run([sys.executable,str(p)],cwd=ROOT,check=True,capture_output=True,text=True)
    print(r.stdout,end='',flush=True);records.append({'check':name,'exit_code':r.returncode,'stdout':r.stdout})
with tempfile.TemporaryDirectory(prefix='role-cover-check-') as temp:
    for name in ['full','star','missing_edge','disjoint']:
        p=ROOT/'proofs/independent-audit'/('check_'+name+'_monomer.cpp');out=Path(temp)/('check_'+name)
        subprocess.run([os.environ.get('CXX','g++'),'-std=c++17','-O2','-UNDEBUG',str(p),'-o',str(out)],check=True)
        r=subprocess.run([str(out)],cwd=ROOT,check=True,capture_output=True,text=True)
        require('cases=4845 weighted_multivariate_identities=14535' in r.stdout,'Unexpected Hall check coverage: '+name)
        print(name+': '+r.stdout,end='',flush=True);records.append({'check':p.name,'exit_code':r.returncode,'stdout':r.stdout})
result={'status':'passed','proof_audit_hashes':count,'exact_aggregate_identities':12,'core_patterns':4,'type_multisets_per_pattern':4845,'weighted_monomer_identities_per_pattern':14535,'weighted_monomer_identities_total':58140,'elapsed_seconds':round(time.time()-start,3),'checks':records,'scope':'Supplementary exact identities and finite support checks; ordinary proof remains the theorem dependency'}
(ROOT/'verification-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
print('PASS all exact supplementary checks; elapsed',result['elapsed_seconds'],'seconds')
