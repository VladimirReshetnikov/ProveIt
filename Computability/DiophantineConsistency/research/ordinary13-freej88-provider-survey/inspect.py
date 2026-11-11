#!/usr/bin/env python3
"""Read-only free-J provider/source survey; never invokes Lean or builds."""
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tarfile
from pathlib import Path

if not sys.flags.isolated or not sys.flags.no_site or sys.flags.optimize:
    raise SystemExit('use python3 -I -S -B')
HERE=Path(__file__).resolve().parent
PROJECT=HERE.parents[1]
ROOT=HERE.parents[3]
P72=Path('/tmp/p72-current-base-extension-attempt02-20261105')
BASE=Path('/tmp/current14-standard-fresh-build-20261104')
PKG=Path('/tmp/ipra-foundation-guarded-v2-cjHUaJun/package-lib')
TOOL=Path('/home/codex/.elan/toolchains/leanprover--lean4---v4.32.0/lib/lean')
pins={
 'prior_inspector':(PROJECT/'research/ordinary13-p73-provider-preflight/inspect.py','67ab841e465f8923c8f3c65e07d93fa055dbfea8e6f1f745ad79442786c097b7'),
 'prior_observation':(PROJECT/'research/ordinary13-p73-provider-preflight/observation.json','f37f6add7288d06a4e1ba60b97bc0ea5c00eeac13c5372bdceea4174c88bdae5'),
 'prior_auditor':(PROJECT/'reviews/ordinary13-p73-provider-preflight-independent/check.py','e7cc82dccb993320b72af7a5665013c8e96ff45ef649d5b5ee74150295fbcf5a'),
 'prior_result':(PROJECT/'reviews/ordinary13-p73-provider-preflight-independent/result.json','fc29d005ab3597cad866219fb8bdfe8f4495743ad3215cd02732c8933140480c'),
 'draft_preflight':(PROJECT/'research/ordinary13-freej88-lean-draft/preflight.py','3b80045b63f418e93738dc5126e4a696eea6e795da6211347662c7c1bdafee0c'),
 'draft_observation':(PROJECT/'research/ordinary13-freej88-lean-draft/preflight-observation.json','d1d33f1f8fb1763c053ad9342891a6eb3f2901564a33fd90dff0b742caf216f2'),
 'draft_auditor':(PROJECT/'reviews/ordinary13-freej88-lean-draft-independent/check.py','835b1ff7ed2c051588cd0fe684948f7bc4701adccdafbd717d5ecff6818ee7ac'),
 'draft_result':(PROJECT/'reviews/ordinary13-freej88-lean-draft-independent/result.json','598572932ccb239c860aa4cf865ff02c76f4cf317a84d563b5cca9b70d64efb5'),
 'p72_survey':(PROJECT/'research/p72-current-base-source-survey/result.json','29cb091647eb0800936795ac0494e5cedcbe8d770c076814e8d52f9c7a738954'),
 'p72_archive':(PROJECT/'research/p72-current-base-extension-build-attempt02/terminal/stage-evidence.tar.gz','884525ff2103d805cdb8b891fedaa9cf8b9be4bc5f1c67efbf8e95353b533541'),
 'base_state':(BASE/'state.json','f618a1c0970874ad349ea29b128cd8f775dd6a09036af3a75731e91f7982e014'),
 'draft_graph':(PROJECT/'research/ordinary13-freej88-lean-draft/P88PairGraph.lean','a792a7731d88b61483f34bf6fea4ef46a983d7e95b19cf9f891f622691ac49f2'),
 'draft_model':(PROJECT/'research/ordinary13-freej88-lean-draft/P88PairModel.lean','21d468a34cf1dfc8df9b2fa4e4ad359294a1047f28ac3aec39bb4f2cc054001a'),
 'draft_endpoint':(PROJECT/'research/ordinary13-freej88-lean-draft/P88PairEndpoint.lean','41682e57745920cfbe57e6198db41312976b7722f329c2b989a1e98d3d41eebf'),
}
def sha(path):
    with Path(path).open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()
for label,(path,digest) in pins.items():
    if not path.is_file() or sha(path)!=digest:raise RuntimeError('missing/changed pin: '+label)
assert json.loads(pins['prior_result'][0].read_text())['status']=='PASS_READ_ONLY_INDEPENDENT_REVIEW'
assert json.loads(pins['draft_result'][0].read_text())['status']=='PASS_SCOPED_SOURCE_REVIEW'
def invoke(path):
    p=subprocess.run([sys.executable,'-I','-S','-B',str(path)],cwd=ROOT,
                     stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=120)
    if p.returncode or p.stderr:raise RuntimeError('read-only subprocess failed: '+p.stderr.decode(errors='replace')[-2000:])
    return json.loads(p.stdout)
prior=invoke(pins['prior_inspector'][0]);draft=invoke(pins['draft_preflight'][0])
assert prior['status']=='READ_ONLY_OBSERVATION_NOT_BUILD_READINESS'
assert not prior['recorded_route_issues'] and not prior['source_head_issues'] and not prior['head_changed']
assert draft['status']=='READ_ONLY_OBSERVATION_NOT_LAUNCH_APPROVAL' and draft['literal_graph_rows_match']==88
assert all(x['matches_prior_point_hash'] for x in draft['p72_frontier_point_observations'].values())

prefix='DiophantineConsistency.Compact44.'
needed=[prefix+'FreeJ13',prefix+'FreeJ13Halt']
frontier=[prefix+n for n in ('FreeJGraphAuxiliary','FreeJSignedTransport','FreeJSumSquares','IPRAOrdinary12Chain','QCube92Halt')]
project=prior['endpoint']['project'];pfront=prior['endpoint']['p72_frontier']
assert all(n in project for n in needed) and all(n in pfront for n in frontier)
assert project[needed[0]]['imports']==[prefix+'FreeJSumSquares',prefix+'FreeJSignedTransport','Mathlib.Tactic.LinearCombination']
assert project[needed[1]]['imports']==[prefix+'FreeJ13',prefix+'FreeJGraphAuxiliary',prefix+'QCube92Halt']
def imports(path):
    return [x for line in path.read_text().splitlines() if line.startswith('import ')
            for x in line.split('--',1)[0].split()[1:]]
assert imports(pins['draft_graph'][0])==[prefix+'FreeJ13']
assert imports(pins['draft_model'][0])==['P88PairGraph',prefix+'FreeJ13Halt',prefix+'IPRAOrdinary12Chain']
assert imports(pins['draft_endpoint'][0])==['P88PairModel']

# The five frontiers are a subset of the six whose retained paths were
# rechecked in the preceding inspector. Reconstruct both captured route sets
# from the pinned archive/base records and check the subset explicitly.
order=json.loads(pins['p72_survey'][0].read_text())['extension_order']
index={n:i for i,n in enumerate(order)}
records={r['module']:r for r in json.loads(pins['base_state'][0].read_text())['records']}
rows={}
with tarfile.open(pins['p72_archive'][0],'r:gz') as tar:
    for member in tar:
        if member.isfile() and member.name.startswith('rows/'):
            row=json.loads(tar.extractfile(member).read());rows[row['module']]=row
assert set(rows)==set(order)
def routes(roots):
    pq=list(roots);bq=[];ps=set();bs=set();pedges=0;bedges=0;pguards=0;bguards=0
    while pq:
        n=pq.pop()
        if n in ps:continue
        ps.add(n);r=rows[n];pedges+=len(r['dependencies']);pguards+=len(r['direct_guard'])
        for dep in r['dependencies']:
            if dep in rows:pq.append(dep)
            elif dep in records:bq.append(dep)
    base_state=json.loads(pins['base_state'][0].read_text())
    while bq:
        n=bq.pop()
        if n in bs:continue
        bs.add(n);r=records[n];bedges+=len(r['direct_inputs']);bguards+=len(base_state['outputs'][n])
        for dep,entry in r['direct_inputs'].items():
            if entry['kind']=='project':
                assert dep in records
                bq.append(dep)
    return ps,bs,{'p72_objects':len(ps),'base_objects':len(bs),'p72_direct_edges':pedges,
                  'base_direct_edges':bedges,'p72_direct_guard_slots':pguards,'base_output_guard_slots':bguards}
ps,bs,counts=routes(frontier)
ps_all,bs_all,counts_all=routes(list(pfront))
assert ps <= ps_all and bs <= bs_all
assert len(ps_all)==prior['recorded_p72_trace']['unique_project_objects']
assert len(bs_all)==prior['recorded_base_trace']['unique_project_objects']
assert counts_all['p72_direct_edges']==prior['recorded_p72_trace']['direct_edges_checked']
assert counts_all['base_direct_edges']==prior['recorded_base_trace']['direct_edges_checked']

def git(*args):
    return subprocess.run(['git','-C',str(ROOT),*args],check=True,stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE,timeout=30).stdout
head=git('rev-parse','HEAD').decode().strip()
draft_paths=[str(pins[k][0].relative_to(ROOT)) for k in ('draft_graph','draft_model','draft_endpoint')]
tracked=set(git('ls-files','-z','--',*draft_paths).decode().split('\0'))
dirty=git('diff','--name-only',head,'--',*draft_paths).decode().splitlines()
assert all(p in tracked for p in draft_paths) and not dirty
assert git('rev-parse','HEAD').decode().strip()==head==prior['head_before']==prior['head_after']
targets=['DiophantineConsistency.Compact44.FreeJ13','DiophantineConsistency.Compact44.FreeJ13Halt',
         'P88PairGraph','P88PairModel','P88PairEndpoint']
stage_order=[targets[0],targets[2],targets[1],targets[3],targets[4]]
lower=P72/'lib'
existing={n:os.path.lexists(lower/(n.replace('.','/')+'.olean')) for n in targets}
suffixes=('.olean','.olean.private','.olean.server','.ir','.ilean',
          '.olean.hash','.olean.private.hash','.olean.server.hash','.ir.hash','.ilean.hash',
          '.so','.dll','.dylib')
roots=[('p72',lower),('base',BASE/'lib'),('package',PKG),('toolchain',TOOL),
       ('project_build',ROOT/'.lake/build/lib/lean')]
target_artifacts=[]
for n in targets:
    stem=Path(n.replace('.','/'))
    for label,root in roots:
        for suffix in suffixes:
            p=root/Path(str(stem)+suffix)
            if os.path.lexists(p):target_artifacts.append({'module':n,'root':label,'path':str(p)})
snapshot_targets=[str(P72/'src'/Path(n.replace('.','/')+'.lean')) for n in targets
                  if os.path.lexists(P72/'src'/Path(n.replace('.','/')+'.lean'))]
init=PKG/'Init.olean'
assert init.is_file() and sha(init)=='d2e85d72099f9d869c9582aad5fb13079968d9d121ac6061e8326b00800b306e'
frontier_paths={}
for n in frontier:
    obj=lower/Path(n.replace('.','/')+'.olean')
    assert obj.is_file() and sha(obj)==pfront[n]['object_sha256']
    frontier_paths[n]={'path':str(obj),'realpath':str(obj.resolve()),'sha256':sha(obj)}
print(json.dumps({
 'status':'READ_ONLY_OBSERVATION_NOT_BUILD_READINESS','inspector_sha256':sha(HERE/'inspect.py'),
 'head':head,'pins':{k:v[1] for k,v in pins.items()},
 'project_sources':{n:project[n] for n in needed},
 'p72_frontier':{n:pfront[n] for n in frontier},
 'p72_frontier_paths':frontier_paths,
 'declared_external':prior['endpoint']['external'],
 'implicit_init_observation':{'path':str(init),'realpath':str(init.resolve()),'sha256':sha(init)},
 'planned_stages':stage_order,'existing_p72_target_objects':existing,
 'target_artifacts_in_named_roots':target_artifacts,'p72_snapshot_target_sources':snapshot_targets,
 'target_suffixes_checked':list(suffixes),'target_roots_checked':[{'label':n,'path':str(p)} for n,p in roots],
 'recorded_freej_routes':counts,'recorded_freej_p72_modules':sorted(ps),'recorded_freej_base_modules':sorted(bs),
 'prior_endpoint_route_counts':counts_all,'prior_endpoint_route_issues':prior['recorded_route_issues'],
 'draft_source_graph_rows':draft['literal_graph_rows_match'],
 'tmp_free_bytes':shutil.disk_usage('/tmp').free,'disk_stop_bytes':5100000000,
 'scope':'Recorded direct routes and line-parsed source imports, not Lean deps/build readiness; package-transitive, dynamic, between-sample, all-signed-integer formalization and file-binding limits remain.'
},indent=2,sort_keys=True))
