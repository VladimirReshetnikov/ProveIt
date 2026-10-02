"""Pinned review of the polynomial-history archive and exact-domain repair.

Original archives remain immutable. Original and repaired author CLIs run in
independent temporary directories; default mode compares the saved receipt.
"""
if not __debug__:
    raise RuntimeError('Review requires enabled assertions')
import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import importlib.util
from itertools import product
import json
from pathlib import Path
import random
import subprocess
import sys
import tempfile
import zipfile

ARCHIVE='unique_polynomial_histories.zip'
ARRIVAL='060e08a07d8e6a8ad5ab9ff6c1f7465e22e35630'
ARCHIVE_SHA='0f0f52d5c6617a22cdd0820386eb378c700e5f5c36bfee810ae13818137465e4'
SOURCE_SHA='1abf1b9a8a670b7b6b93c23a501eb29d55718307524cab52af3a5bdf21c21013'
REPAIRED_SHA='53c95479edfa477e878741d050644227efa898705ff416e54fb45e9368c52ad3'
PATCH_SHA='6fb34d781403cd495b7e15ae2e1c2c309c1ea86da100c4efe6776db62a828343'
COMMANDS=('verification.py','export_quadratic.py','feature_verification.py')


def require(ok, message):
    if not ok: raise ValueError(message)


def digest(data): return hashlib.sha256(data).hexdigest()


def exact(a,b):
    if type(a) is not type(b):return False
    if isinstance(a,dict):return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if isinstance(a,(list,tuple)):return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b


def load(path,name):
    spec=importlib.util.spec_from_file_location(name,path)
    module=importlib.util.module_from_spec(spec);sys.modules[name]=module
    spec.loader.exec_module(module);return module


def archive_bytes(repo):
    path=repo/'docs/incoming'/ARCHIVE
    data=path.read_bytes() if path.is_file() else subprocess.check_output(['git','show',f'{ARRIVAL}:docs/incoming/{ARCHIVE}'],cwd=repo)
    require(digest(data)==ARCHIVE_SHA,'Archive changed');return data


def author_replay(root):
    saved={p.name:json.loads(p.read_text()) for p in (root/'results').glob('*.json')}
    def stable(v):
        if type(v) is dict:return {k:stable(x) for k,x in v.items() if k!='elapsed_seconds'}
        if type(v) is list:return [stable(x) for x in v]
        return v
    for command in COMMANDS:
        done=subprocess.run([sys.executable,'code/'+command],cwd=root,text=True,capture_output=True,timeout=120)
        require(done.returncode==0,command+' failed: '+done.stderr[-3000:])
    current={p.name:json.loads(p.read_text()) for p in (root/'results').glob('*.json')}
    require(exact(stable(saved),stable(current)),'Author results changed beyond elapsed_seconds')
    return {'commands':list(COMMANDS),'saved_json_exports_reproduced':len(saved),
            'results':{name:stable(current[name]) for name in ('verification_results.json','quadratic_results.json','feature_results.json')}}


def affine(row):
    out={('@',i,j):c for (i,j),c in row.constant.items() if c}
    for name,pol in row.coefficients.items():
        out.update({(name,i,j):c for (i,j),c in pol.items() if c})
    return out


def combination(rows):
    out=Counter()
    for weight,row in rows:
        for key,c in affine(row).items():out[key]+=weight*c
    return {k:v for k,v in out.items() if v}


def verify(repo,patch):
    data=archive_bytes(repo);require(digest(patch.read_bytes())==PATCH_SHA,'Patch changed')
    counts=Counter();rng=random.Random(20261002621)
    with tempfile.TemporaryDirectory(prefix='polynomial-history-review-') as td:
        td=Path(td);archive=td/ARCHIVE;archive.write_bytes(data)
        with zipfile.ZipFile(archive) as z:
            names=z.namelist()
            require(len(names)==len(set(names)),'Duplicate archive member')
            require(all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names),'Unsafe member')
            hashes={n:digest(z.read(n)) for n in names if not n.endswith('/')}
            for label in ('original','repaired'):z.extractall(td/label)
        original=td/'original/unique_polynomial_histories';repaired=td/'repaired/unique_polynomial_histories'
        require(digest((original/'code/polynomial_histories.py').read_bytes())==SOURCE_SHA,'Source changed')
        done=subprocess.run(['git','apply','--check',str(patch)],cwd=repaired,capture_output=True,text=True)
        require(done.returncode==0,done.stderr)
        done=subprocess.run(['git','apply',str(patch)],cwd=repaired,capture_output=True,text=True)
        require(done.returncode==0,done.stderr)
        require(digest((repaired/'code/polynomial_histories.py').read_bytes())==REPAIRED_SHA,'Repair output changed')
        author={'original':author_replay(original),'repaired':author_replay(repaired)}
        old=load(original/'code/polynomial_histories.py','history_original')
        new=load(repaired/'code/polynomial_histories.py','history_repaired')
        table={t:t[1] for t in product(range(2),repeat=3)}
        failures=[]
        for bad in (True,1.0):
            ca=old.CA(2,table,frozenset({bad}));system=old.compile_system(ca,[1]);w,_=old.witness_for_horizon(system,0)
            try:system.residuals(w)
            except KeyError as e:failures.append({'accepting_symbol_type':type(bad).__name__,'dangling_variable':e.args[0]})
            else:raise AssertionError('Original defect no longer reproduced')
        counts['original_dangling_symbol_failures']=len(failures)
        def reject(f):
            try:f()
            except (TypeError,ValueError):counts['invalid_calls_rejected']+=1;return
            raise AssertionError('Invalid exact-domain input accepted')
        good=new.CA(2,table,frozenset({1}));system=new.compile_system(good,[1])
        for bad in (True,1.0):
            reject(lambda:new.CA(bad,table,frozenset({1})))
            reject(lambda:new.CA(2,table,frozenset({bad})))
            malformed=dict(table);malformed[(0,0,1)]=bad
            reject(lambda:new.CA(2,malformed,frozenset({1})))
            malformed_keys=dict(table);del malformed_keys[(0,0,1)];malformed_keys[(0,0,bad)]=1
            reject(lambda:new.CA(2,malformed_keys,frozenset({1})))
            reject(lambda:new.compile_system(good,[bad]))
            reject(lambda:new.witness_for_horizon(system,bad))
            reject(lambda:new.compile_feature_system(good,[1],features=[(0,),(bad,)]))
            reject(lambda:new.monomial(bad));reject(lambda:new.monomial(0,bad));reject(lambda:new.monomial(coefficient=bad))
            reject(lambda:new.shift({},bad));reject(lambda:new.shift({},0,bad))
            reject(lambda:new.repunit(bad));reject(lambda:new.repunit(1,bad))
            reject(lambda:new.elementary_ca(bad))
            for pol in ({(bad,0):1},{(0,bad):1},{(0,0):bad}):
                require(not new.is_natural(pol),'Nonexact polynomial accepted')
                w,_=new.witness_for_horizon(system,0);w['D']=pol;reject(lambda:system.residuals(w))
        for s in range(1,6):
            for case in range(3):
                triples=list(product(range(s),repeat=3));table={t:rng.randrange(s) for t in triples};table[(0,0,0)]=0
                acc=frozenset({s-1}) if s>1 else frozenset()
                ca0,ca1=old.CA(s,table,acc),new.CA(s,table,acc)
                for m in (1,3):
                    word=tuple(rng.randrange(s) for _ in range(m))
                    builders=[lambda mod,ca:mod.compile_system(ca,word),lambda mod,ca:mod.compile_system(ca,word,horizontal='pair'),
                              lambda mod,ca:mod.compile_feature_system(ca,word),lambda mod,ca:mod.compile_feature_system(ca,word,features=[(a,) for a in range(s)])]
                    for builder in builders:
                        a,b=builder(old,ca0),builder(new,ca1)
                        require(exact(a.serializable(),b.serializable()),'Valid compiler export changed')
                        counts['identical_valid_systems']+=1
                        for h in range(3):
                            u,history=old.witness_for_horizon(a,h);v,history1=new.witness_for_horizon(b,h)
                            require(exact(u,v) and exact(history,history1),'Valid witness constructor changed')
                            require(exact(a.residuals(u),b.residuals(v)),'Valid verifier changed')
                            counts['identical_valid_witness_and_residual_cases']+=1
                    base=new.compile_system(ca1,word);rows={e.name:e for e in base.equations}
                    for features in ([tuple((a>>k)&1 for k in range((s-1).bit_length())) for a in range(s)],[(a,) for a in range(s)]):
                        fs=new.compile_feature_system(ca1,word,features=features)
                        expected={name:affine(rows[name]) for name in ('clock_right','clock_time','no_early_acceptance','one_final_acceptance')}
                        expected['total_shape']=combination([(1,rows[f'left_marginal_{a}']) for a in range(s)])
                        expected['total_vertical']=combination([(1,rows[f'vertical_{a}']) for a in range(s)])
                        for k in range(len(features[0])):
                            expected[f'feature_left_{k}']=combination([(features[a][k],rows[f'left_marginal_{a}']) for a in range(s)])
                            expected[f'feature_right_{k}']=combination([(features[a][k],rows[f'right_marginal_{a}']) for a in range(1,s)])
                            expected[f'feature_vertical_{k}']=combination([(features[a][k],rows[f'vertical_{a}']) for a in range(s)])
                        require(expected=={r.name:affine(r) for r in fs.equations},'Feature affine row identity failed')
                        counts['exact_feature_system_row_maps']+=1;counts['exact_feature_residual_identities']+=len(expected)
                        require(len(fs.variables)==s**3+s+5 and len(fs.equations)==6+3*len(features[0]),'Feature count changed')
                        B0=max(1,max((c for f in features for c in f),default=0))
                        require(all(len(p)<=2 and all(abs(c)<=B0 and sum(e)<=3 for e,c in p.items()) for r in fs.equations for p in r.coefficients.values()),'Matrix bounds failed')
                        counts['feature_matrix_bound_audits']+=1
        return {'status':'PASS_WITH_REPAIRED_EXACT_DOMAIN_API','archive':ARCHIVE,'arrival':ARRIVAL,'archive_sha256':ARCHIVE_SHA,
                'member_sha256':hashes,'source_sha256':SOURCE_SHA,'repaired_source_sha256':REPAIRED_SHA,'patch_sha256':PATCH_SHA,
                'original_defect_reproductions':failures,'counts':dict(counts),'author_replays':author,
                'scope':'Written proof review and finite exact replays; fixed polynomial witnesses over N[X,Y], not fixed scalar integer arity. Feature row maps prove forward affine identities; reverse inclusion and uniqueness use nonnegative occupancy. No audited literal universal CA table or ordinary87 improvement.'}


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--repo',type=Path);p.add_argument('--patch',type=Path);p.add_argument('--write',action='store_true');a=p.parse_args()
    here=Path(__file__).resolve();repo=a.repo or next(x for x in here.parents if (x/'.git').exists())
    result=verify(repo.resolve(),(a.patch or here.with_name('unique_polynomial_histories_exact_domains.patch')).resolve())
    saved=here.with_suffix('.json')
    if a.write:saved.write_text(json.dumps(result,indent=2)+'\n')
    else:require(exact(result,json.loads(saved.read_text())),'Review receipt changed')
    print(json.dumps({'status':result['status'],'counts':result['counts']},indent=2))
