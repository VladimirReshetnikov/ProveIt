#!/usr/bin/env python3
"""Replay four authenticated Reports35-38 archives in an external cache only.
Archives and relocated source members are inert data; no extraction or execution.
"""
import argparse
from collections import Counter
import hashlib
import io
import json
import os
from pathlib import Path
import stat
import subprocess
import zipfile

REVISION = '7f9672c599194e150dee64ebaa0b19f0e035ba15'
PLACEMENTS = ['216bd81e116297214f443afddc2fc6252a7767a6',
              'a51a439cdcb43701241c83fdf8d185630df0b18d']
INVENTORY = [{'name': 'Literal_Periodic_Sandpiles_and_Diophantine_Certificates_Package.zip',
  'report': 35,
  'bytes': 1645467,
  'sha256': '3202b1f0430353a3cd05f15ac6f34e9a797ed931d9a86e3580a110d97b01a12d',
  'git_blob_sha1': '2846a325db6d513967998583c87b9dba0f4dfa7a',
  'members': [{'member': 'Research_Report35/evidence/composition/PROOF.md',
               'bytes': 25178,
               'sha256': '6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/22-literal-sandpiles-evidence-composition-PROOF.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report35/evidence/composition/prism_certificate.py',
               'bytes': 18431,
               'sha256': 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/22-literal-sandpiles-evidence-composition-prism_certificate.py',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report35/evidence/loader/LOADER-PROOF.md',
               'bytes': 16025,
               'sha256': '1791518f521a147b014ca7636910b7775df64fcfe799b6fcb5a0261de4f99d34',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/22-literal-sandpiles-evidence-loader-LOADER-PROOF.md',
               'relation': 'byte_identical_new_placement'}]},
 {'name': 'Real_Exactness_of_Binary_Sandpile_Certificates_Package.zip',
  'report': 36,
  'bytes': 423395,
  'sha256': '72cfb3a88640020e97f9b6b62c4f7580f97d75ed4f957b8c604536119bcf96ac',
  'git_blob_sha1': '69dc5988450343e354275ca189827002c8d4c31f',
  'members': [{'member': 'Research_Report36/evidence/real/PROOF.md',
               'bytes': 17044,
               'sha256': '9bc26062cc0e68fc8fee18290c347b309e2f711d208644ec541b29a5492071ae',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/23-real-sandpiles-evidence-real-PROOF.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report36/evidence/real/approved_base/prism_certificate.py',
               'bytes': 18431,
               'sha256': 'bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/22-literal-sandpiles-evidence-composition-prism_certificate.py',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report36/evidence/real/real_certificate.py',
               'bytes': 3999,
               'sha256': '073e164feadc6bd4850ed043043889c5755e27c809f3afcdd3b52a14b9a1a299',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/canonical-diophantine-certificates/code/23-real-sandpiles-evidence-real-real_certificate.py',
               'relation': 'byte_identical_new_placement'}]},
 {'name': 'Exact_Negative_Index_Obstruction_for_Positive_Diophantine_Interfaces_Package.zip',
  'report': 37,
  'bytes': 501623,
  'sha256': '018b960efd8069db99ec3eaa9b691cb2ca60edbc88932cc6e37cbf3562d169f9',
  'git_blob_sha1': '5da0abf451780b515d86b2cce2527836a2b7f81f',
  'members': [{'member': 'Research_Report37/evidence/EXACT-OBSTRUCTION.md',
               'bytes': 20882,
               'sha256': '918b82b7666b4f5cbab5fd7a0b8298275ac62fe84f83261ef88ea863765d455f',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/15-neg-obstruction-evidence-EXACT-OBSTRUCTION.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report37/evidence/independent/INDEPENDENT-REVIEW.md',
               'bytes': 19038,
               'sha256': '3eae6bf05a24f603f9d30c02f83363d55accb9d38852fbc0fc5539f276feb130',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/fixed-universal-polynomials/15-neg-obstruction-evidence-independent-INDEPENDENT-REVIEW.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report37/evidence/context/RAW-POSITIVE-REDUCTION.md',
               'bytes': 8904,
               'sha256': '0ae2f56e7db3177f3100198ae503c950d2f11d30d3d6d55d51f399dbdbeb48a9',
               'current_path': None,
               'relation': 'archive_only_context'},
              {'member': 'Research_Report37/evidence/context/PRIOR-INDEPENDENT-REVIEW.md',
               'bytes': 25341,
               'sha256': 'a82ee544ea93efae25ff8b4e60c3cbe01136d5db2273b82e8eee994f222b6656',
               'current_path': None,
               'relation': 'archive_only_context'},
              {'member': 'Research_Report37/evidence/sources/complete74_negative_index_refinement.md',
               'bytes': 10635,
               'sha256': 'a471a60a2b742e8d84ad9c19c333e6c7949e5da911c5b1149eded0854d3fbc99',
               'current_path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_negative_index_refinement.md',
               'relation': 'byte_identical_existing_frozen_source'},
              {'member': 'Research_Report37/evidence/sources/complete74_nonlinear_index_projection_scout.json',
               'bytes': 74001,
               'sha256': 'ea982f9585eb4e16d756dfc33c73041e73e5e18a38ea37c2302d57c1fe104c92',
               'current_path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete74_nonlinear_index_projection_scout.json',
               'relation': 'byte_identical_existing_frozen_source'},
              {'member': 'Research_Report37/evidence/sources/complete75_half_binomial_compiler.md',
               'bytes': 12918,
               'sha256': '68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117',
               'current_path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_half_binomial_compiler.md',
               'relation': 'byte_identical_existing_frozen_source'},
              {'member': 'Research_Report37/evidence/sources/complete75_positive_elimination.py',
               'bytes': 11453,
               'sha256': '70123af4f0787b38271f7c4f0fa60e4235cd2f1964ee1b0ad345fe0e3bb82749',
               'current_path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_positive_elimination.py',
               'relation': 'byte_identical_existing_frozen_source'},
              {'member': 'Research_Report37/evidence/sources/review_complete74_nonlinear_index_bootstrap.md',
               'bytes': 11355,
               'sha256': '4922eb2587fa1ecda313792ea0644c6da123b5ebdb86a0dbdfa02671d48ed1a8',
               'current_path': 'Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_complete74_nonlinear_index_bootstrap.md',
               'relation': 'byte_identical_existing_frozen_source'}]},
 {'name': 'Polynomial_First_Revisit_and_Exact_Pattern_Queries_for_Turmites_Package.zip',
  'report': 38,
  'bytes': 504531,
  'sha256': 'e5abfdbfbbc9c203bdfafb040cba7f8c280af8b031b02103c989aeb97e085277',
  'git_blob_sha1': '5edc1627eb9b3368eb0cf86cae59d9ea7e045ca2',
  'members': [{'member': 'Research_Report38/README.md',
               'bytes': 6187,
               'sha256': 'ea5315c3daacd04e5fe5306d17e18078e831fac2f10008c9d625f26ba22cfe38',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/README.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/boundary-context/proof.md',
               'bytes': 21645,
               'sha256': '7a855d4af90beb924475a3b9c0e7b06fbc033503c849f9f97bb70cfc8c905761',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-boundary-context-proof.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/PROOF.md',
               'bytes': 11362,
               'sha256': 'd4fa1ecec1b80d320a36ee464095c38fe671531757cc5dfcb85c3f8b62e30f12',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-PROOF.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/complexity-review.md',
               'bytes': 13614,
               'sha256': '5c8a72e42ac1d804f6179ba3b8d52033744897c2ae3ecf6de0fb5417aa8c5497',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-complexity-review.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/review.md',
               'bytes': 11573,
               'sha256': '2b9424773c2f0af9dee87c8e2829e9f351324e33ca3da834c1bfa74ce6785895',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-review.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/boundary-context/source-audit.md',
               'bytes': 2643,
               'sha256': 'ecffab51c5b44fe174774218fd4c29fe1e130e3cb6fefd42d3faf92ad236ff40',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/source-packet-boundary-context-source-audit.md',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/Research_Report38.tex',
               'bytes': 63197,
               'sha256': 'd81bc30804a381694454142e9939ee2c637f794289151566070078694d4812c7',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/article.tex',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/one_visit.py',
               'bytes': 8663,
               'sha256': '6b2bc54678a5a4c18db8eec23e37195a3c526d7f152863a1fb3a1f8d682429f7',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/code/source-packet-one_visit.py',
               'relation': 'byte_identical_new_placement'},
              {'member': 'Research_Report38/evidence/source-packet/observations.py',
               'bytes': 14311,
               'sha256': 'a9f951d4c12df99d0d78bf6eca3fdeee55539eb1bd3938e6e4fd71ae027b5210',
               'current_path': 'SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/periodic-turmite-first-revisits/code/source-packet-observations.py',
               'relation': 'byte_identical_new_placement'}]}]

def require(ok,message):
    if not ok: raise ValueError(message)
def digest(b): return hashlib.sha256(b).hexdigest()
def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) is list: return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

def git(repo,*args):
    p=subprocess.run(['git','--no-pager','-C',str(repo),*args],stdout=subprocess.PIPE,stderr=subprocess.PIPE)
    require(p.returncode==0,'Git read failed: '+p.stderr.decode(errors='replace').strip())
    return p.stdout

def inside(p,parent): return p==parent or parent in p.parents

def normalized(path):
    require('..' not in path.parts,'parent traversal is not an output path')
    return Path(os.path.abspath(path))

# Every write is relative to verified open directory descriptors. No output
# ancestor or leaf symlink is followed; files are created exclusively and never
# overwritten. These are filesystem guards, not a promise against arbitrary
# concurrent hostile directory renaming or storage failure.
def parent_fd(path,create=False):
    fd=os.open('/',os.O_RDONLY|os.O_DIRECTORY)
    try:
        for part in path.parts[1:-1]:
            try:
                nxt=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
            except FileNotFoundError:
                if not create:
                    os.close(fd);return None
                try: os.mkdir(part,mode=0o700,dir_fd=fd)
                except FileExistsError: pass
                nxt=os.open(part,os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW,dir_fd=fd)
            os.close(fd);fd=nxt
        return fd
    except BaseException:
        os.close(fd);raise

def regular_bytes(fd,name):
    leaf=os.open(name,os.O_RDONLY|os.O_NOFOLLOW|os.O_NONBLOCK,dir_fd=fd)
    try:
        require(stat.S_ISREG(os.fstat(leaf).st_mode),'output is not a regular file')
        with os.fdopen(leaf,'rb',closefd=False) as stream: return stream.read()
    finally: os.close(leaf)

def preflight(path,expected,protected):
    require(path.name not in ('','/'),'file output must have a leaf')
    for directory in protected:
        require(not inside(path,directory),'output lies inside protected repository storage')
    fd=parent_fd(path)
    if fd is None:return
    try:
        try: old=regular_bytes(fd,path.name)
        except FileNotFoundError:return
        require(old==expected,'refuse differing existing output: '+str(path))
    finally:os.close(fd)

def write_same_or_new(path,data,protected):
    preflight(path,data,protected)
    fd=parent_fd(path,True)
    try:
        try:
            leaf=os.open(path.name,os.O_WRONLY|os.O_CREAT|os.O_EXCL|os.O_NOFOLLOW,0o600,dir_fd=fd)
        except FileExistsError:
            require(regular_bytes(fd,path.name)==data,'existing output changed')
        else:
            with os.fdopen(leaf,'wb') as stream:stream.write(data)
        require(regular_bytes(fd,path.name)==data,'written bytes differ')
    finally:os.close(fd)

def prepare(repo_arg,cache_arg):
    repo=repo_arg.resolve(strict=True)
    require(repo.is_dir(),'repository directory')
    actual=Path(git(repo,'rev-parse','--show-toplevel').decode().strip()).resolve(strict=True)
    require(actual==repo,'--repo-root must be actual worktree root')
    require(git(repo,'rev-parse','--verify',REVISION+'^{commit}').decode().strip()==REVISION,'exact historical revision')
    protected=[repo]
    for flag in ('--git-dir','--git-common-dir'):
        p=Path(git(repo,'rev-parse','--path-format=absolute',flag).decode().strip()).resolve(strict=True)
        protected.append(p)
    cache=normalized(cache_arg)
    for p in protected:
        require(not inside(cache,p) and not inside(p,cache),'cache intersects protected repository storage')
    # Probe an otherwise unused child to validate the complete cache ancestor
    # chain without creating directories or requiring the cache to exist.
    fd=parent_fd(cache/'__path_probe__')
    if fd is not None:os.close(fd)
    require(len(INVENTORY)==4 and len({r['name'] for r in INVENTORY})==4,'fixed four-archive scope')
    work=[];records=[];member_count=0;relations=Counter();paths=set()
    for record in INVENTORY:
        name=record['name'];require(Path(name).name==name and name.endswith('.zip'),'fixed archive basename')
        raw=git(repo,'cat-file','blob',REVISION+':docs/incoming/'+name)
        require(len(raw)==record['bytes'] and digest(raw)==record['sha256'],'exact archive size/SHA256')
        oid=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\0'+raw).hexdigest()
        require(oid==record['git_blob_sha1'],'Git blob SHA1')
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            require(len(z.namelist())==len(set(z.namelist())),'unique ZIP members')
            for m in record['members']:
                b=z.read(m['member'])
                require(len(b)==m['bytes'] and digest(b)==m['sha256'],'selected member size/SHA256')
                if m['current_path'] is not None:
                    relative=Path(m['current_path'])
                    require(not relative.is_absolute() and '..' not in relative.parts,'fixed current source path')
                    require((repo/relative).read_bytes()==b,'current/member full-byte identity: '+str(relative))
                    paths.add(m['current_path'])
                relations[m['relation']]+=1;member_count+=1
        dest=cache/'docs/incoming'/name
        preflight(dest,raw,protected);work.append((dest,raw));records.append(record)
    require(member_count==24 and len(paths)==21,'selected member/current-source inventory')
    require(dict(relations)=={'byte_identical_new_placement':17,'archive_only_context':2,'byte_identical_existing_frozen_source':5},'exact relocation scope')
    receipt=dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),historical_revision=REVISION,
                 placement_commits=PLACEMENTS,archives=records,archive_count=4,archive_bytes=sum(r['bytes'] for r in records),
                 authenticated_members=member_count,member_relations=dict(relations),distinct_current_files=len(paths),
                 verification=dict(archive_extraction=False,archive_execution=False,repository_writes=False,
                                   source_bridge_created=False,overwrite_differing=False,exclusive_new_files=True,
                                   no_output_symlink_following=True),
                 scope='Historical archive compatibility and byte-identical member relocation only. No scientific theorem or archived verifier is rerun by this helper.')
    return protected,work,receipt

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--repo-root',type=Path,required=True);p.add_argument('--output-root',type=Path,required=True)
    g=p.add_mutually_exclusive_group(required=True);g.add_argument('--output',type=Path);g.add_argument('--expect',type=Path)
    a=p.parse_args();protected,work,r=prepare(a.repo_root,a.output_root)
    encoded=(json.dumps(r,indent=2,sort_keys=True)+'\n').encode()
    if a.expect:require(exact(r,json.loads(a.expect.read_text())),'saved exact typed receipt')
    receipt_path=normalized(a.output) if a.output else None
    if receipt_path:
        require(receipt_path not in {p for p,b in work},'receipt cannot replace an archive')
        preflight(receipt_path,encoded,protected)
    for path,data in work:write_same_or_new(path,data,protected)
    if receipt_path:write_same_or_new(receipt_path,encoded,protected)
    print(json.dumps({k:r[k] for k in ('status','archive_count','archive_bytes','authenticated_members','distinct_current_files')},sort_keys=True))
if __name__=='__main__':main()
