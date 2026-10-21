"""Read-only record controls, using captured actual bytes; no compiler or runner is invoked."""
from pathlib import Path
from types import SimpleNamespace
import copy, gzip, io, json, tarfile
from capture import collect
from evidence import digest, manifest, save, validate, read_archive

HERE = Path(__file__).resolve().parent


def encode(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def archive(members):
    out = io.BytesIO()
    with gzip.GzipFile(fileobj=out, filename='', mode='wb', mtime=0) as zipped:
        with tarfile.open(fileobj=zipped, mode='w') as tar:
            for name, data in sorted(members.items()):
                entry = tarfile.TarInfo(name); entry.size = len(data)
                tar.addfile(entry, io.BytesIO(data))
    return out.getvalue()


def main():
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    options = SimpleNamespace(run=args.run, basis=Path('/tmp/k215-proof-phase3/lean-run1'),
        build=Path('/tmp/k215-proof-phase4/build.py'), basis_build=Path('/tmp/k215-proof-phase3/build.py'),
        basis_review=Path('/tmp/k215-proof-phase3/live-review.json'),
        basis_reviewer=Path('/tmp/k215-proof-phase3-publication/review.py'), basis_packet=None, stdout=None)
    before = collect(options)
    checked = validate(before)
    outcomes = []

    def reject(name, mutate):
        values = copy.deepcopy(before)
        mutate(values)
        try:
            validate(values)
        except (AssertionError, KeyError, ValueError, tarfile.TarError) as error:
            outcomes.append({'control': name, 'status': 'REJECTED', 'exception': type(error).__name__})
        else:
            raise AssertionError('Accepted invalid evidence: ' + name)

    def change_json(values, path, f):
        data = json.loads(values[path]); f(data); values[path] = encode(data)

    def completed_edit(values, module, f):
        data = json.loads(values['execution/completed.json']); f(data[module])
        values['execution/completed.json'] = encode(data)
        change_json(values, 'execution/result.json', lambda r: r.update(completed_sha256=digest(values['execution/completed.json'])))
        return data[module]

    done = json.loads(before['execution/completed.json'])
    fresh = next(m for m,r in done.items() if r['origin']=='phase4_fresh')
    reused = next(m for m,r in done.items() if r['origin']=='phase3_hash_bound')
    reject('current source changed', lambda d: d.__setitem__('execution/sources/'+fresh.replace('.','/')+'.lean', b'import Init\n'))
    reject('current selected log changed', lambda d: d.__setitem__('execution/logs/'+fresh+'.log', b'error: forged\n'))
    reject('basis selected log changed', lambda d: d.__setitem__('basis/logs/'+reused+'.log', b'changed\n'))
    reject('current driver changed', lambda d: d.__setitem__('review/build.py', b'# changed\n'))
    reject('trusted predecessor validator changed', lambda d: d.__setitem__('review/phase3_evidence.py', b'# changed\n'))
    reject('self-consistent wrong direct dependencies', lambda d: completed_edit(d, fresh, lambda r:r.update(dependencies={})))
    reject('self-consistent unknown reuse origin', lambda d: completed_edit(d,reused,lambda r:r.update(origin='assumed')))
    reject('self-consistent changed reused object', lambda d: completed_edit(d,reused,lambda r:r.update(object_sha256='0'*64)))

    def bad_audit(values, kind):
        result = json.loads(values['execution/result.json']); row=result['audits'][0]
        folder = 'execution/'+Path(row['log']).parent.name
        if kind=='axiom':
            text=values[folder+'/'+row['module']+'.log'].decode().replace('propext','InjectedAxiom')
            row['reports']=[r.replace('propext','InjectedAxiom') for r in row['reports']]
        else:
            text=values[folder+'/'+row['module']+'.log'].decode()+'\nwarning: injected\n'
        values[folder+'/'+row['module']+'.log']=text.encode(); row['log_sha256']=digest(text.encode())
        values[folder+'/'+row['module']+'.json']=encode(row); values['execution/result.json']=encode(result)
    reject('self-consistent unexpected endpoint axiom',lambda d:bad_audit(d,'axiom'))
    reject('self-consistent endpoint warning',lambda d:bad_audit(d,'warning'))

    def nested(values, name, data):
        index=json.loads(values['basis-checkpoint/index.json'])
        inside=read_archive(values['basis-checkpoint/execution.tar.gz'],index)
        inside[name]=data
        content=archive(inside)
        values['basis-checkpoint/execution.tar.gz']=content
        values['basis-checkpoint/index.json']=encode(manifest(inside))
        change_json(values,'basis-checkpoint/result.json',lambda r:r.update(execution_archive_sha256=digest(content),archive_members=len(inside)))
    for name in ('extra.olean','extra.olean.server','extra.pyc','../escape.txt','/absolute.txt'):
        reject('resealed nested archive rejects '+name,lambda d,n=name:nested(d,n,b'invalid'))
    reject('resealed nested selected log changed',lambda d:nested(d,'execution/logs/'+reused+'.log',b'changed\n'))
    for name in ('extra.olean','extra.olean.private','extra.pyc','../escape.txt','/absolute.txt'):
        try:
            read_archive(archive({name:b'invalid'}),manifest({name:b'invalid'}))
        except AssertionError:
            outcomes.append({'control':'outer archive rejects '+name,'status':'REJECTED'})
        else:
            raise AssertionError(name)
    assert collect(options)==before, 'Live inputs changed during controls'
    save(args.output, {'status':'PASS_METADATA_CONTROLS','positive_saved_validation':checked,
        'negative_controls':outcomes,'negative_count':len(outcomes),
        'all_captured_inputs_unchanged':True,'code_sha256':digest(Path(__file__).read_bytes()),
        'scope':'Mutates private in-memory copies only, resealing specified record/archive hashes. No compiler, candidate, or archived code execution.'})
    print(json.dumps({'status':'PASS_METADATA_CONTROLS','negative_count':len(outcomes)},indent=2))

if __name__=='__main__':
    main()
