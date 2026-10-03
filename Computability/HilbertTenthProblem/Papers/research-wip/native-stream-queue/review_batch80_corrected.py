#!/usr/bin/env python3
"""Pinned delta review of the three corrected batch80 research packages."""
import argparse, ast, copy, hashlib, io, json, subprocess, sys, tempfile, zipfile
from pathlib import Path, PurePosixPath
OLD='aebfa386e'; NEW='4e270aa46'
PACKAGES={
'Eager_Tree_Calculus_Research_Package':('eager-tree-certificates','5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4','2c053f50027ec632c2773c9d2ec3e2ace9f621eef5c08bebce0ca06c2d0f3dbd'),
'Reset_Petri_Net_Certificates':('reset-net-release','b1efbc90aac106061e93ffc92adda686b8e1b9f57539aae976bf227dffec83e3','8d5b9b1a52c33aeadb8b4200fd9c138bd016f2651ebcfccf1a939e03715486d3'),
'Sparse_Lattice_Diophantine_Certificates':('sparse-lattice-release','90c9dadeccad7c70c777b141b0c65029b992048fd69448f0f8e035ec522cdc68','cf9b546baaece745c047f6ce33574d10104f03c9849f4114626a916c1deec1e2')}
CHANGES={
'Eager_Tree_Calculus_Research_Package':{'README.md','reproduce.py','code/independent_receipt.json','code/receipt.json','code/tree_kernel.py','MANIFEST.sha256'},
'Reset_Petri_Net_Certificates':{'README.md','SHA256SUMS','build_net.py','checks/PADDING_AND_GENERIC_PEAK_RESULTS.json','peak_quadratic.py','run-checks.sh'},
'Sparse_Lattice_Diophantine_Certificates':{'README.md','SHA256SUMS','SOURCE-PROVENANCE.md','receipts/coefficient-crosscheck.json','receipts/release-verification.json','replay/core/sparse_mass.py','replay/run_release.py'}}
ADDED={
'Eager_Tree_Calculus_Research_Package':{'CORRECTION.md','code/test_application_domain.py'},
'Reset_Petri_Net_Certificates':{'CORRECTION.md','checks/EXACT_DOMAIN_RESULTS.json','checks/audit_exact_domains.py'},
'Sparse_Lattice_Diophantine_Certificates':{'CORRECTION.md','receipts/poly-exactness.json','replay/core/test_poly_exactness.py'}}
def need(ok,why):
    if not ok:raise ValueError(why)
def exact(a,b):
    if type(a)is not type(b):return False
    if type(a)is dict:return a.keys()==b.keys() and all(type(k)is str and exact(a[k],b[k]) for k in a)
    if type(a)in(list,tuple):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b
def sha(b):return hashlib.sha256(b).hexdigest()
def blob(repo,revision,path):return subprocess.check_output(['git','-C',str(repo),'show',revision+':'+path])
def archive(data,pin,prefix):
    need(sha(data)==pin,'Archive pin')
    with zipfile.ZipFile(io.BytesIO(data)) as z:
        infos=[i for i in z.infolist() if not i.is_dir()]
        need(len(infos)==len({i.filename for i in infos}),'Duplicate archive member')
        result={}
        for i in infos:
            p=PurePosixPath(i.filename)
            need(not p.is_absolute() and '..'not in p.parts and '\\'not in i.filename and p.parts[0]==prefix,'Unsafe archive member')
            need((i.external_attr>>16)&0o170000!=0o120000,'Symlink archive member')
            result[str(PurePosixPath(*p.parts[1:]))]=z.read(i)
    return result
def tree(data):return ast.parse(data.decode())
def dump(t):return ast.dump(t,include_attributes=False)
def fn(t,name):
    found=[n for n in ast.walk(t) if isinstance(n,(ast.FunctionDef,ast.AsyncFunctionDef)) and n.name==name]
    need(len(found)==1,'Unique function '+name);return found[0]
def compare_core(stem,old,new):
    names={'Eager_Tree_Calculus_Research_Package':['code/tree_kernel.py'],'Reset_Petri_Net_Certificates':['build_net.py','peak_quadratic.py'],'Sparse_Lattice_Diophantine_Certificates':['replay/core/sparse_mass.py']}[stem]
    result=[]
    for name in names:
        a,b=tree(old[name]),tree(new[name]);guards=[]
        if name.endswith('tree_kernel.py'):
            f=fn(b,'app');need(isinstance(f.body[0],ast.If),'Application guard');guards.append(dump(f.body.pop(0)))
        elif name=='peak_quadratic.py':
            f=fn(b,'compile_peak');need(isinstance(f.body[0],ast.If),'Peak guard');guards.append(dump(f.body.pop(0)))
        elif name=='build_net.py':
            f=fn(b,'initial');o=fn(a,'initial');need(isinstance(f.body[2],ast.If) and isinstance(o.body[2],ast.Assert),'Initial replacement guard');guards.append(dump(f.body[2]));f.body[2]=copy.deepcopy(o.body[2])
            f=fn(b,'fire');need([type(x) for x in f.body[:3]]==[ast.If,ast.Assign,ast.If],'Firing guards');guards.extend(map(dump,f.body[:3]));f.body=f.body[3:]
        else:
            classes=[n for n in b.body if isinstance(n,ast.ClassDef) and n.name=='Poly'];need(len(classes)==1,'Poly class');c=classes[0]
            nodes=[n for n in c.body if isinstance(n,ast.FunctionDef) and n.name=='__post_init__'];need(len(nodes)==1,'Constructor guard');guards.append(dump(nodes[0]));c.body.remove(nodes[0])
        need(dump(a)==dump(b),'Behavior beyond declared boundary edit: '+name)
        result.append(dict(file=name,old_sha256=sha(old[name]),new_sha256=sha(new[name]),erased_boundary_AST=guards,remaining_module_AST_identical=True))
    return result

def json_changes(a,b,path=()):
    if type(a)is type(b)is dict and a.keys()==b.keys():return [v for k in a for v in json_changes(a[k],b[k],path+(k,))]
    if type(a)is type(b)is list and len(a)==len(b):return [v for i,(x,y)in enumerate(zip(a,b)) for v in json_changes(x,y,path+(i,))]
    return [] if exact(a,b) else [dict(path=list(path),before=a,after=b)]
def receipts(old,new):
    results={}
    for name in old.keys()&new.keys():
        if not name.endswith('.json') or old[name]==new[name]:continue
        a,b=json.loads(old[name]),json.loads(new[name]);diff=json_changes(a,b)
        for d in diff:
            p=d['path'];x,y=d['before'],d['after']
            if p==['stages']:need(y==['poly-exactness']+x,'Only new exactness stage added')
            else:
                need(p in [['script_sha256'],['snapshot_sha256'],['sha256','build_net.py'],['sha256','peak_quadratic.py'],['producer_sha256'],['packaged_producer_sha256']],'Unexpected saved mathematical change')
                targets=[n for n in old.keys()&new.keys() if sha(old[n])==x and sha(new[n])==y]
                need(len(targets)==1,'Exact source hash replacement')
                d['source_file']=targets[0]
        results[name]=diff
    return results

def manifest(files):
    name='MANIFEST.sha256' if 'MANIFEST.sha256'in files else 'SHA256SUMS';listed={}
    for line in files[name].decode().splitlines():
        if not line.strip():continue
        h,path=line.split(maxsplit=1);path=path.lstrip('*').removeprefix('./')
        need(path in files and sha(files[path])==h and path not in listed,'Manifest entry '+path);listed[path]=h
    need(set(listed)==set(files)-{name},'Complete manifest coverage')
    return len(listed)
def extract(files,path):
    path.mkdir()
    for name,data in files.items():
        p=path/name;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
def call(args,cwd):
    p=subprocess.run(args,cwd=cwd,capture_output=True,text=True,timeout=180)
    need(p.returncode==0,'Replay failed: '+str(args)+'\n'+p.stdout+'\n'+p.stderr)
    return p

def run(repo):
    rows=[]
    with tempfile.TemporaryDirectory(prefix='batch80-corrections-') as tmp:
        tmp=Path(tmp)
        for stem,(prefix,oldpin,newpin) in PACKAGES.items():
            old=archive(blob(repo,OLD,'docs/incoming/'+stem+'.zip'),oldpin,prefix)
            new=archive(blob(repo,NEW,'docs/incoming/'+stem+'_corrected.zip'),newpin,prefix)
            changed={n for n in old.keys()&new.keys() if old[n]!=new[n]}
            need(set(old)<=set(new) and changed==CHANGES[stem] and set(new)-set(old)==ADDED[stem],'Exact package delta')
            m=manifest(new);core=compare_core(stem,old,new);changes=receipts(old,new)
            directory=tmp/stem;extract(new,directory);baseline=tmp/(stem+'-old');extract(old,baseline)
            if stem.startswith('Eager'):
                replay=[]
                for optimized in (False,True):
                    p=call([sys.executable,*(['-O'] if optimized else []),'code/test_application_domain.py','-v'],directory)
                    need('Ran 5 tests' in p.stderr and p.stderr.rstrip().endswith('OK'),'All five independent regression groups')
                    replay.append(dict(optimized=optimized,unittest_groups=5,parameter_scenarios=303))
                # Compare actual results and complete proof certificates for every
                # grid case in independent subprocesses, without sharing caches.
                script="import json,sys;sys.path.insert(0,'code');import tree_kernel as k\nout=[]\nfor x in range(20):\n for y in range(9):\n  e=k.Evaluation();z=e.app(x,y);out.append([x,y,z,k.certificate(e,(x,y))])\nprint(json.dumps(out,sort_keys=True))"
                a=call([sys.executable,'-c',script],baseline).stdout;b=call([sys.executable,'-c',script],directory).stdout
                need(a==b,'All valid Tree certificates unchanged');valid=180
            elif stem.startswith('Reset'):
                replay=[json.loads(call([sys.executable,*(['-O'] if opt else []),'checks/audit_exact_domains.py'],directory).stdout) for opt in (False,True)]
                need(all(r['rejected_calls']==64 and r['valid_stored_firings']==388 and r['full_schema_hash_matches']==9 for r in replay),'Exact reset coverage')
                # Evaluate all nine complete schemas from both actual producers.
                script="import json;from pathlib import Path;from source_quadratic import semantic_table;from peak_quadratic import compile_peak\nt=semantic_table(json.loads(Path('source/virtual3.json').read_text()))\nprint(json.dumps([compile_peak(t,h,with_duration=w,all_durations=a) for h in (1,2,3) for w,a in ((False,False),(True,False),(True,True))],sort_keys=True))"
                a=call([sys.executable,'-c',script],baseline).stdout;b=call([sys.executable,'-c',script],directory).stdout
                need(a==b,'Actual nine full reset schemas unchanged');valid=9
            else:
                replay=[json.loads(call([sys.executable,*(['-O'] if opt else []),'replay/core/test_poly_exactness.py','--baseline-module',str(baseline/'replay/core/sparse_mass.py')],directory).stdout) for opt in (False,True)]
                need(exact(*replay),'Optimization-independent exactness receipt');need(replay[0]['baseline']['exact_expression_coefficient_comparisons']==2700,'Exact coefficient comparison coverage');valid=2700
            preserved=sorted(n for n in old if old[n]==new[n])
            need(all(n in preserved for n in old if n.endswith(('.pdf','.tex','.csv','.gz'))),'Original mathematics or literal table changed')
            rows.append(dict(package=stem,old_archive_sha256=oldpin,new_archive_sha256=newpin,old_member_count=len(old),new_member_count=len(new),changed=sorted(changed),added=sorted(set(new)-set(old)),preserved=preserved,new_member_pins={n:sha(d) for n,d in sorted(new.items())},manifest_entries=m,core_AST_delta=core,saved_JSON_changes=changes,normal_and_optimized_replays=replay,independently_compared_valid_objects=valid))
    return dict(status='PASS_BATCH80_CORRECTED_PACKAGES',old_revision=OLD,new_revision=NEW,packages=rows,scope='Pinned correction-delta review. Original report/PDF/math fixtures preserved. Only constructor/evaluator/marking domain guards change. New targeted normal and optimized suites plus actual baseline/corrected comparisons; unchanged full historical suites are not rerun. No new arithmetic bound or universal theorem.')
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path,required=True);p.add_argument('--output',type=Path);p.add_argument('--expect',type=Path);a=p.parse_args();r=run(a.repo)
    if a.expect:need(exact(r,json.loads(a.expect.read_text())),'Exact typed saved receipt')
    if a.output:a.output.write_text(json.dumps(r,indent=2,sort_keys=True)+'\n')
    print(json.dumps(dict(status=r['status'],packages=[dict(package=q['package'],preserved=len(q['preserved']),members=q['new_member_count'],valid_comparisons=q['independently_compared_valid_objects']) for q in r['packages']]),indent=2))
