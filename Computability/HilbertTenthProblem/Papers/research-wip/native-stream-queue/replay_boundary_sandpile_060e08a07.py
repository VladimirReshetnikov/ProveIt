"""Safely unpack pinned reports, replay author CLIs/repair and saved review."""
if not __debug__:raise RuntimeError('Replay requires enabled assertions')
import hashlib,importlib.util,json,subprocess,sys,tempfile,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent
ARRIVAL='060e08a07d8e6a8ad5ab9ff6c1f7465e22e35630'

def require(value,message):
    if not value:raise ValueError(message)
def sha(data):return hashlib.sha256(data).hexdigest()
def stable(value):
    if type(value) is dict:return {k:stable(v) for k,v in value.items() if k not in ('python','elapsed_seconds')}
    if type(value) is list:return [stable(v) for v in value]
    return value

def main():
    repo=next(p for p in HERE.parents if (p/'.git').exists())
    pins=json.loads((HERE/'review_boundary_sandpile_060e08a07_members.json').read_text())
    require(sha((HERE/'linear_boundary_exact_boolean_guards.patch').read_bytes())=='6c566f21fe7e37c7cd5d6dd78a3bccd3c072d166856b31cac5741dc272ffb3be','Patch changed')
    require(sha((HERE/'review_boundary_sandpile_060e08a07.py').read_bytes())=='2e9714d5d8a2a99830f9769ca3272ae60322be1b846c7bfaa3ad8c2f2df5916f','Independent helper changed')
    with tempfile.TemporaryDirectory(prefix='boundary-sandpile-replay-') as td:
        td=Path(td);roots={};author_commands=0;preserved=0
        for name,record in pins.items():
            path=repo/'docs/incoming'/name;data=path.read_bytes() if path.is_file() else subprocess.check_output(['git','show',f'{ARRIVAL}:docs/incoming/{name}'],cwd=repo)
            require(sha(data)==record['sha256'],'Archive changed');path=td/name;path.write_bytes(data)
            with zipfile.ZipFile(path) as z:
                names=z.namelist();require(len(names)==len(set(names)) and all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names),'Unsafe archive')
                require({n:sha(z.read(n)) for n in names if not n.endswith('/')}==record['members'],'Members changed');z.extractall(td/'original')
                if name.startswith('Linear'):z.extractall(td/'repaired')
            package=next(iter(record['members'])).split('/')[0];root=td/'original'/package;roots[name]=root
            commands=['code/verify.py','code/boundary_transport.py'] if name.startswith('Linear') else ['verify.py','sandpile_certificates.py']
            for command in commands:
                p=subprocess.run([sys.executable,command],cwd=root,capture_output=True,text=True,timeout=120);require(p.returncode==0,p.stderr[-3000:]);author_commands+=1
            with zipfile.ZipFile(path) as z:
                for name1,digest in record['members'].items():
                    actual=(td/'original'/name1).read_bytes();original=z.read(name1)
                    if name1.endswith('/verification/results.json'):
                        require(stable(json.loads(actual))==stable(json.loads(original)),'Sandpile results changed')
                    elif name1.endswith('/verification/results.txt'):
                        trim=lambda b:[s for s in b.decode().splitlines() if not s.startswith(('python:','elapsed_seconds:'))]
                        require(trim(actual)==trim(original),'Sandpile text results changed')
                    else:require(sha(actual)==digest,'Original member changed: '+name1)
                    preserved+=1
        patched=td/'repaired/linear_boundary_transport'
        p=subprocess.run(['git','apply',str(HERE/'linear_boundary_exact_boolean_guards.patch')],cwd=patched,capture_output=True,text=True);require(p.returncode==0,p.stderr)
        for command in ('code/verify.py','code/boundary_transport.py'):
            p=subprocess.run([sys.executable,command],cwd=patched,capture_output=True,text=True,timeout=120);require(p.returncode==0,p.stderr[-3000:]);author_commands+=1
        original=roots['Linear_Boundary_Transport_Research.zip']
        for name in pins['Linear_Boundary_Transport_Research.zip']['members']:
            rel=Path(name).relative_to('linear_boundary_transport')
            if rel.as_posix()!='code/boundary_transport.py':require((original/rel).read_bytes()==(patched/rel).read_bytes(),'Patched valid export changed')
        out=td/'review.json'
        p=subprocess.run([sys.executable,str(HERE/'review_boundary_sandpile_060e08a07.py'),'--linear-root',str(original),'--sandpile-root',str(roots['no_borrowed_firings.zip']),'--patched-linear-root',str(patched),'--output',str(out)],capture_output=True,text=True,timeout=120)
        require(p.returncode==0,p.stderr[-3000:]);require(json.loads(out.read_text())==json.loads((HERE/'review_boundary_sandpile_060e08a07.json').read_text()),'Independent receipt changed')
        print(json.dumps(dict(status='PASS',author_cli_invocations=author_commands,authenticated_original_members=preserved,independent_receipt_exact=True)))
if __name__=='__main__':main()
