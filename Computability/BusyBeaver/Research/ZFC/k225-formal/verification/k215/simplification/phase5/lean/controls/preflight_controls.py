"""Tiny provider and nested-evidence controls, before any phase5 completion.

Uses private disposable files and in-memory copies only. No runner/compiler and
no archive-supplied code is invoked; all validators are reviewed local siblings.
"""
from pathlib import Path
from copy import deepcopy
import argparse,ast,gzip,io,json,tarfile,tempfile
from evidence import digest,manifest,read_archive,save,sha,validate_basis
from review import check_providers

HERE=Path(__file__).resolve().parent
REMOVED='BusyBeaver.ZFC.RMOffsetBisim'

def encoded(x):return (json.dumps(x,indent=2)+'\n').encode()

def archive(values):
    buf=io.BytesIO()
    with gzip.GzipFile(filename='',fileobj=buf,mode='wb',mtime=0) as zipped:
        with tarfile.open(fileobj=zipped,mode='w') as tar:
            for name,data in sorted(values.items()):
                entry=tarfile.TarInfo(name);entry.size=len(data)
                tar.addfile(entry,io.BytesIO(data))
    return buf.getvalue()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet',type=Path,required=True)
    parser.add_argument('--output',type=Path,required=True)
    args=parser.parse_args()
    assert not args.output.exists()
    outcomes=[]
    # Exercise the exact persisted live-receipt flag names used by both consumers.
    rt=ast.parse((HERE/'review.py').read_text())
    flags={n.value:True for n in ast.walk(rt) if isinstance(n,ast.Constant) and isinstance(n.value,str)
           and n.value.startswith('all') and ('_objects_' in n.value or '_basis_' in n.value)}
    assert flags=={'all184_objects_rehashed_after_audits':True,'all185_basis_objects_and_logs_unchanged':True}
    for name in ['publish.py','review_saved.py']:
        tree=ast.parse((HERE/name).read_text())
        nodes=[n for n in ast.walk(tree) if isinstance(n,ast.Assert) and isinstance(n.test,ast.Subscript)
               and isinstance(n.test.value,ast.Name) and n.test.value.id=='live'
               and isinstance(n.test.slice,ast.Constant) and str(n.test.slice.value).startswith('all')]
        assert len(nodes)==2
        code=compile(ast.Module(body=nodes,type_ignores=[]),str(HERE/name),'exec')
        exec(code,{'live':flags})
        outcomes.append({'name':name+' exact live receipt flags','status':'PASS'})
    def reject(name,fn):
        try:fn()
        except (AssertionError,KeyError,ValueError,FileNotFoundError,tarfile.TarError) as ex:
            outcomes.append({'name':name,'status':'REJECTED','exception':type(ex).__name__})
        else:raise AssertionError('Invalid control accepted: '+name)
    original={'basis-checkpoint/'+name:(args.packet/name).read_bytes() for name in
              ['execution.tar.gz','index.json','result.json','live-review.json']}
    for name in ['phase4_evidence.py','phase3_evidence.py']:
        original['review/'+name]=(HERE/name).read_bytes()
    _,checked=validate_basis(original)
    outcomes.append({'name':'exact complete phase4 and nested earlier checkpoint','status':'PASS'})
    for name in ['phase4_evidence.py','phase3_evidence.py']:
        values=dict(original);values['review/'+name]=b'# changed\n'
        reject('changed trusted sibling '+name,lambda v=values:validate_basis(v))
    def tamper_nested(name,data):
        values=dict(original)
        inside=read_archive(values['basis-checkpoint/execution.tar.gz'],json.loads(values['basis-checkpoint/index.json']))
        inside[name]=data
        rebuilt=archive(inside)
        values['basis-checkpoint/execution.tar.gz']=rebuilt
        values['basis-checkpoint/index.json']=encoded(manifest(inside))
        summary=json.loads(values['basis-checkpoint/result.json'])
        summary.update(execution_archive_sha256=digest(rebuilt),archive_members=len(inside))
        values['basis-checkpoint/result.json']=encoded(summary)
        return validate_basis(values)
    for name in ['extra.olean','extra.olean.server','extra.pyc','../escape','/absolute']:
        reject('resealed nested archive '+name,lambda n=name:tamper_nested(n,b'invalid'))
    reject('resealed nested removed-module log',lambda:tamper_nested('execution/logs/'+REMOVED+'.log',b'changed\n'))
    # The exact set guards are extracted from our current read-only validator.
    tree=ast.parse((HERE/'evidence.py').read_text())
    guards=[n for n in ast.walk(tree) if isinstance(n,ast.Assert) and ast.unparse(n.test) in
            ['set(modules) <= set(old_modules)', "set(old_modules) - set(modules) == {'BusyBeaver.ZFC.RMOffsetBisim'}"]]
    assert len(guards)==2
    code=compile(ast.Module(body=guards,type_ignores=[]),str(HERE/'evidence.py'),'exec')
    for name,modules,positive in [('exact offset removal',{'A'},True),('missing extra module',set(),False),
        ('extra current module',{'A','B'},False),('old offset module retained',{'A',REMOVED},False)]:
        fn=lambda m=modules:exec(code,{'modules':m,'old_modules':{'A',REMOVED}})
        if positive:fn();outcomes.append({'name':name,'status':'PASS'})
        else:reject(name,fn)
    def provider_case(mutate=None):
        with tempfile.TemporaryDirectory(prefix='provider-control-',dir=HERE) as td:
            root=Path(td);run=root/'run';basis=root/'basis'
            (run/'objects').mkdir(parents=True);(basis/'objects').mkdir(parents=True)
            for name in ['A','B','Removed']:(basis/'objects'/f'{name}.olean').write_bytes(b'same bytes')
            (run/'objects/A.olean').symlink_to(basis/'objects/A.olean')
            (run/'objects/B.olean').write_bytes(b'fresh')
            done={'A':{'origin':'phase4_hash_bound'},'B':{'origin':'phase5_fresh'}}
            old={n:{} for n in ['A','B','Removed']}
            if mutate:mutate(run/'objects',basis/'objects')
            check_providers(run,basis,done,old)
    provider_case();outcomes.append({'name':'valid overlay with an extra retained predecessor','status':'PASS'})
    def relink(path,target):path.unlink();path.symlink_to(target)
    def make_regular(path):path.unlink();path.write_bytes(b'same bytes')
    cases=[
        ('reused wrong same-byte provider',lambda r,b:relink(r/'A.olean',b/'B.olean')),
        ('reused regular file',lambda r,b:make_regular(r/'A.olean')),
        ('fresh symlink',lambda r,b:relink(r/'B.olean',b/'B.olean')),
        ('removed predecessor missing',lambda r,b:(b/'Removed.olean').unlink()),
        ('removed module in current overlay',lambda r,b:(r/'Removed.olean').symlink_to(b/'Removed.olean')),
        ('unexpected current provider',lambda r,b:(r/'Extra.olean').write_bytes(b'extra')),
        ('unexpected current companion',lambda r,b:(r/'B.olean.server').write_bytes(b'extra')),
        ('directory symlink hides providers',lambda r,b:(r/'Alias').symlink_to(b,target_is_directory=True)),
        ('broken reused symlink',lambda r,b:(b/'A.olean').unlink()),
        ('basis symlink',lambda r,b:relink(b/'Removed.olean',b/'B.olean')),
        ('fresh target missing',lambda r,b:(r/'B.olean').unlink()),
    ]
    for name,mutate in cases:reject(name,lambda m=mutate:provider_case(m))
    assert all((args.packet/name).read_bytes()==original['basis-checkpoint/'+name] for name in
               ['execution.tar.gz','index.json','result.json','live-review.json'])
    save(args.output,{'status':'PASS_PREFLIGHT_READ_ONLY_CONTROLS','checks':outcomes,
        'positive_count':sum(r['status']=='PASS' for r in outcomes),'negative_count':sum(r['status']=='REJECTED' for r in outcomes),
        'predecessor_actual_summary':checked,'input_packet_unchanged':True,
        'sources':{n:sha(HERE/n) for n in ['evidence.py','review.py','phase4_evidence.py','phase3_evidence.py',Path(__file__).name]},
        'scope':'Only exact saved phase4/nested evidence, in-memory metadata mutations, extracted current set guards and tiny disposable provider files. No phase5 actual PASS, compiler or archived-code execution claim.'})
    print(json.dumps({'status':'PASS_PREFLIGHT_READ_ONLY_CONTROLS','checks':len(outcomes)},indent=2))

if __name__=='__main__':main()
