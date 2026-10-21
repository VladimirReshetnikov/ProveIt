#!/usr/bin/env python3
"""Verify both alternative 215-state constructions, without network access.
Default: exact reconstruction, source/startup audits, and stored proof inventories.
--runtime: additionally rederive both quantified primitive-runtime certificates.
--primary-runtime / --secondary-runtime: rederive just the selected certificate.
"""
from pathlib import Path
import argparse,hashlib,json,subprocess,sys,tempfile

ROOT=Path(__file__).resolve().parent

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def inventory():
    manifest=json.loads((ROOT/'manifest.json').read_text())
    expected=manifest['files']
    actual={}
    for path in ROOT.rglob('*'):
        if path.is_symlink():
            raise RuntimeError('Symlinks are not permitted in the verified packet: '+str(path.relative_to(ROOT)))
        if not path.is_file() or '__pycache__' in path.relative_to(ROOT).parts:
            continue
        name=path.relative_to(ROOT).as_posix()
        if name!='manifest.json':
            actual[name]=digest(path)
    if actual!=expected:
        missing=sorted(set(expected)-set(actual))
        extra=sorted(set(actual)-set(expected))
        changed=sorted(name for name in expected.keys()&actual.keys() if expected[name]!=actual[name])
        raise RuntimeError('Manifest mismatch: '+json.dumps(dict(missing=missing,extra=extra,changed=changed)))
    return digest(ROOT/'manifest.json')

def compare_pair():
    def canonical(path,reflected=False):
        table={}
        for line in path.read_text().splitlines():
            if not line or line.startswith('#'):
                continue
            q,b,w,d,z=line.split()
            key=(int(q),int(b))
            if key in table:
                raise RuntimeError('Duplicate transition in '+path.name)
            table[key]=(int(w),1 if d=='R' else -1,int(z))
        states=set(range(215))
        assert set(table)=={(q,b) for q in states for b in (0,1)}
        assert all(w in (0,1) and z in states|{215} for w,d,z in table.values())
        mapping={0:0};queue=[0];rows=[]
        for q in queue:
            for b in (0,1):
                w,d,z=table[q,b]
                if z!=215 and z not in mapping:
                    mapping[z]=len(mapping);queue.append(z)
                rows.append([mapping[q],b,w,-d if reflected else d,'HALT' if z==215 else mapping[z]])
        assert len(mapping)==215
        return rows
    primary=ROOT/'primary/z201.tm'
    secondary=ROOT/'secondary/candidate.tm'
    a=canonical(primary);b=canonical(secondary);reflected=canonical(secondary,True)
    assert a!=b and a!=reflected
    return dict(working_states=215,primary_canonical_sha256=digest(primary),
                secondary_canonical_sha256=digest(secondary),rooted_graph_isomorphic=False,
                rooted_graph_isomorphic_after_tape_reflection=False)

def run(script,args,work,logname):
    log=work/logname
    with log.open('w') as stream:
        process=subprocess.run([sys.executable,'-B',str(script),*map(str,args)],cwd=work,stdout=stream,stderr=subprocess.STDOUT)
    if process.returncode:
        print(log.read_text()[-8000:],file=sys.stderr)
        raise RuntimeError(f'{logname}: verifier exited with status {process.returncode}')
    print('PASS '+logname,flush=True)
    return dict(exit_code=0,log=logname,log_sha256=digest(log))

def main():
    if not __debug__ or sys.flags.optimize:
        raise RuntimeError('Run with Python assertions enabled. -O and -OO are not supported.')
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--runtime',action='store_true',help='Freshly derive both complete runtime certificates')
    parser.add_argument('--primary-runtime',action='store_true')
    parser.add_argument('--secondary-runtime',action='store_true')
    parser.add_argument('--work',type=Path,help='New output directory outside the packet; retained for inspection')
    args=parser.parse_args()
    manifest_sha=inventory()
    print('PASS exact packet manifest',flush=True)
    temp=None
    if args.work:
        work=args.work.resolve()
        if work==ROOT or ROOT in work.parents:
            raise RuntimeError('The output directory must be outside the packet.')
        work.mkdir(parents=True,exist_ok=False)
    else:
        temp=tempfile.TemporaryDirectory(prefix='two-new215-')
        work=Path(temp.name)
    pair=compare_pair()
    (work/'pair_comparison.json').write_text(json.dumps(pair,indent=2)+'\n')
    full_primary=args.runtime or args.primary_runtime
    full_secondary=args.runtime or args.secondary_runtime
    primary_args=['--full-runtime',work/'primary_runtime'] if full_primary else []
    primary=run(ROOT/'primary/verify.py',primary_args,work,'primary.log')
    secondary_args=['--work',work/'secondary']+(['--runtime'] if full_secondary else [])
    secondary=run(ROOT/'secondary/verify.py',secondary_args,work,'secondary.log')
    secondary['verification']=json.loads((work/'secondary/verification.json').read_text())
    if inventory()!=manifest_sha:
        raise RuntimeError('The packet changed during verification.')
    result=dict(status='ALL_REQUESTED_CHECKS_PASS',working_states_per_machine=215,
                manifest_sha256=manifest_sha,pair_comparison=pair,primary=primary,secondary=secondary,
                fresh_primary_runtime=full_primary,fresh_secondary_runtime=full_secondary,
                scope='Two materially different 215-state machines. No completed 214-state blank-start machine or new proof-assistant kernel endpoint is claimed.')
    (work/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2),flush=True)
    if temp:
        temp.cleanup()
    else:
        print('Retained verification output: '+str(work),flush=True)

if __name__=='__main__':
    main()
