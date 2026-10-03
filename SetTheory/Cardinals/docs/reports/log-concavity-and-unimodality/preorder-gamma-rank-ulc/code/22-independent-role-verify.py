#!/usr/bin/env python3
"""Replay the frozen exact dependencies and the explicit nonreal example."""
import sys
if not __debug__ or sys.flags.optimize:
    raise SystemExit('Run without -O: assertions in the independent checkers must remain enabled.')
from pathlib import Path
from tempfile import TemporaryDirectory
from itertools import combinations, permutations
import hashlib, json, subprocess, time, zipfile
ROOT=Path(__file__).resolve().parent

def require(ok,message):
    if not ok: raise RuntimeError(message)
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def verify_manifest(root):
    p=root/'SHA256SUMS'
    require(p.exists(),'Missing top-level SHA256SUMS')
    count=0
    for line in p.read_text().splitlines():
        h,name=line.split('  ',1)
        require(digest(root/name)==h,'Manifest hash mismatch: '+name);count+=1
    return count

def extract_checked(archive,dest):
    with zipfile.ZipFile(archive) as z:
        require(len(z.namelist())==len(set(z.namelist())),'Duplicate ZIP member')
        require(z.testzip() is None,'ZIP corruption: '+str(archive))
        for name in z.namelist():
            p=Path(name)
            require(not p.is_absolute() and '..' not in p.parts,'Unsafe ZIP member: '+name)
        manifests=[n for n in z.namelist() if n=='SHA256SUMS' or n.count('/')==1 and n.endswith('/SHA256SUMS')]
        require(len(manifests)==1,'Expected one package-root manifest: '+str(archive))
        manifest=manifests[0]
        prefix=manifest[:-len('SHA256SUMS')]
        for line in z.read(manifest).decode().splitlines():
            h,name=line.split('  ',1)
            require(hashlib.sha256(z.read(prefix+name)).hexdigest()==h,'Dependency member hash mismatch: '+name)
        z.extractall(dest)
        return dest/prefix

def nonreal_example():
    # Three lower tails; four upper vertices of each pair-neighborhood type.
    upper=list(range(3,15));types=[(0,1),(0,2),(1,2)]
    rows=[set() for _ in range(15)]
    for t,pair in enumerate(types):
        for h in range(3+4*t,7+4*t):
            for i in pair: rows[i].add(h)
    gamma=[1]
    hall_cases=0
    for k in range(1,4):
        count=0
        for S in combinations(range(3),k):
            for T in combinations(upper,k):
                hall=True
                for l in range(1,k+1):
                    for A in combinations(S,l):
                        neighbors=set().union(*(rows[i] for i in A))&set(T)
                        if len(neighbors)<l: hall=False
                bij=any(all(t in rows[s] for s,t in zip(S,p)) for p in permutations(T))
                require(hall==bij,'Hall/bijection disagreement in nonreal example')
                count+=hall;hall_cases+=1
        gamma.append(count)
    require(gamma==[1,24,162,208],'Unexpected example coefficients')
    d,c,b,a=gamma
    disc=b*b*c*c-4*a*c*c*c-4*b*b*b*d-27*a*a*d*d+18*a*b*c*d
    require(disc==-2592,'Unexpected cubic discriminant')
    gaps=[c*c-3*b,b*b-3*c*a]
    require(gaps==[90,11268],'Unexpected ULC gaps')
    return {'gamma':gamma,'discriminant':disc,'cubic_gaps':gaps,'Hall_vs_bijection_cases':hall_cases}

start=time.time();count=verify_manifest(ROOT)
pins=json.loads((ROOT/'dependency-pins.json').read_text())
for name,h in pins.items(): require(digest(ROOT/name)==h,'Pinned dependency mismatch: '+name)
print('PASS top-level manifest:',count,'files; pinned archives:',len(pins),flush=True)
results={}
with TemporaryDirectory(prefix='independent-role-degree-three-replay-') as td:
    td=Path(td)
    for key,archive,script,result in [
        ('independent_role','role-degree-three-audit-package.zip','verify_all.py','portable_replay.json'),
        ('role_cover','role-cover-package.zip','verify.py','verification-receipt.json')]:
        dest=td/key;dest.mkdir();dest=extract_checked(ROOT/'checker'/archive,dest)
        subprocess.run([sys.executable,str(dest/script)],cwd=dest,check=True)
        results[key]=json.loads((dest/result).read_text())
    require(results['independent_role']['passed'],'Independent-role dependency failed')
    require(results['independent_role']['complete_independent_role_finite_domain'],'Incomplete role domain')
    require(results['independent_role']['catalog_target_types']==1686,'Wrong finite domain size')
    require(results['independent_role']['vertex_only_proof_dependencies']==0,'Vertex-only scope dependency')
    require(results['independent_role']['side_HPP_and_published_positive_maps_replayed'],'HPP map replay missing')
    require(results['independent_role']['final_side_proper_minors_and_all_real_SOS_replayed'],'Final-side replay missing')
    require(results['role_cover']['status']=='passed','Role-cover dependency failed')
complementary=subprocess.run([sys.executable,str(ROOT/'proofs/final-rayleigh/verify_side1565_rayleigh.py')],check=True,capture_output=True,text=True)
results['complementary_final_rayleigh']=json.loads(complementary.stdout)
require(results['complementary_final_rayleigh']['passed'],'Complementary final Rayleigh check failed')
results['nonreal_example']=nonreal_example()
results['status']='passed';results['elapsed_seconds']=round(time.time()-start,3)
results['scope']='Exact finite and certificate replay; ordinary structural proofs remain mathematical dependencies.'
(ROOT/'local-replay.json').write_text(json.dumps(results,indent=2)+'\n')
print('PASS full independent-role degree-three package;',results['elapsed_seconds'],'seconds',flush=True)
