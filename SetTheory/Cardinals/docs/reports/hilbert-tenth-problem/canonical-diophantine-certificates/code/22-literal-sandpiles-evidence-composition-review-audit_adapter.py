"""Adapter integrity and huge lazy-geometry regressions; no Circuit is built."""
from pathlib import Path
import argparse,json,sys,tempfile,types
from itertools import islice
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
import literal_composition as lc
from prism_certificate import Prism

def require(condition,message):
    if not condition:raise AssertionError(message)

def run(root):
    root=Path(root).resolve()
    require(lc.DEFAULT_LOADER==Path(lc.__file__).resolve().parent.parent/'loader','nonportable default loader path')
    # Incorrect manifests and modified files must fail before importing code.
    with tempfile.TemporaryDirectory(prefix='sandpile-adapter-audit-') as temp:
        d=Path(temp);(d/'FROZEN-INPUTS.json').write_text('{}')
        try:lc.load_module(d)
        except ValueError as e:require('manifest' in str(e),'wrong bad-manifest rejection')
        else:raise AssertionError('modified manifest accepted')
        manifest=(root/'FROZEN-INPUTS.json').read_bytes();(d/'FROZEN-INPUTS.json').write_bytes(manifest)
        first=next(iter(json.loads(manifest)['files']));target=d/first;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(b'altered by local audit')
        try:lc.load_module(d)
        except ValueError as e:require('frozen loader file changed' in str(e),'wrong modified-file rejection')
        else:raise AssertionError('modified frozen file accepted')
    # Cache poisoning must not substitute a previously imported homonym.
    sentinel=object();old={name:sys.modules.get(name,sentinel) for name in ('lazy_u15','periodic_router')};path_before=list(sys.path)
    fake_ca=types.ModuleType('lazy_u15');fake_router=types.ModuleType('periodic_router')
    fake_ca.__file__='/not/the/verified/lazy_u15.py';fake_router.__file__='/not/the/verified/periodic_router.py'
    fake_ca.marker='unverified';fake_router.Edge=object
    def unverified(*args,**kwargs):raise AssertionError('unverified cached dependency used')
    for name in ('corners','primitive','port'):setattr(fake_router,name,unverified)
    sys.modules['lazy_u15']=fake_ca;sys.modules['periodic_router']=fake_router
    try:
        module=lc.load_module(root)
        require(module.ca is not fake_ca,'unverified cached CA reused')
        require(Path(module.ca.__file__).resolve()==root/'ca'/'lazy_u15.py','CA imported from unverified path')
        require(module.primitive is not unverified,'unverified cached router reused')
        require(Path(module.primitive.__code__.co_filename).resolve()==root/'geometry'/'periodic_router.py','router imported from unverified path')
        require(sys.modules.get('lazy_u15') is fake_ca and sys.modules.get('periodic_router') is fake_router,'caller module cache was not restored')
        require(sys.path==path_before,'caller sys.path was not restored')
        sys.modules['lazy_u15']=None;sys.modules['periodic_router']=None
        module=lc.load_module(root)
        require(all(name in sys.modules and sys.modules[name] is None for name in ('lazy_u15','periodic_router')),'explicit None cache entries were not restored')
        require(sys.path==path_before,'caller sys.path was not restored after None entries')
    finally:
        for name,previous in old.items():
            if previous is sentinel:sys.modules.pop(name,None)
            else:sys.modules[name]=previous
        sys.path[:]=path_before
    # itertools.product caches input pools. Explicit nested ranges must stream.
    P=Prism((-3,8,-1),(10**12,10**12,10**12))
    require(list(islice(P.points(),3))==[(-3,8,-1),(-3,8,0),(-3,8,1)],'huge point prefix')
    require(len(list(islice(P.edges(),3)))==3,'huge edge prefix')
    require(len(list(islice(P.halo(),3)))==3,'huge halo prefix')
    bound_cases=0
    for nl in range(0,13):
        for nr in range(0,13):
            for T in (0,1,2,10,100):
                for p in sorted({-T,0,T}):
                    Q=lc.halt_prism('0'*nl,'1'*nr,T,p);N=nl+nr+T+1
                    require(Q.V<=lc.C*N*N,'quadratic volume bound')
                    require(Q.lengths[0]<=16*lc.B*N and Q.lengths[1]<=5*lc.B*N,'axis bounds')
                    bound_cases+=1
    out={'status':'PASS','freeze_rejection_tests':2,'import_provenance_tests':2,'huge_iterator_prefix_tests':3,'candidate_bound_cases':bound_cases,'scope':'Verified loader module definitions imported; Circuit, edge scans, background evaluation and universal computation not executed'}
    print(json.dumps(out,indent=2));return out

if __name__=='__main__':
    parser=argparse.ArgumentParser();parser.add_argument('--loader-root',type=Path,default=lc.DEFAULT_LOADER);args=parser.parse_args();run(args.loader_root)
