#!/usr/bin/env python3
"""Rebuild principal and sparse endpoints, compare exact bytes, bind imports."""
from pathlib import Path
import argparse,hashlib,json,sys,tempfile
sys.dont_write_bytecode=True
from build_unified_cap import generate,HERE,INCOMING

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
    p=argparse.ArgumentParser();p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    checks=[]
    with tempfile.TemporaryDirectory(dir=HERE,prefix='reproduction_') as tmp:
        for name,sparse in [('unified_cap_h12',False),('unified_cap_sparse_h12',True)]:
            root=Path(tmp)/name;generate(root,horizon_minimum=12,sparse=sparse)
            reference=HERE/name
            for f in sorted(reference.rglob('*.json')):
                relative=f.relative_to(reference);g=root/relative
                if f.read_bytes()!=g.read_bytes():raise ValueError(f'Byte mismatch: {name}/{relative}')
                checks.append({'file':f'{name}/{relative}','sha256':sha(f)})
    imports=[]
    for module in sys.modules.values():
        f=getattr(module,'__file__',None)
        if not f:continue
        f=Path(f).resolve()
        if f.suffix=='.py' and (f.is_relative_to(INCOMING) or f.is_relative_to(HERE)):
            imports.append({'path':str(f.relative_to(HERE.parent)),'sha256':sha(f),'bytes':f.stat().st_size})
    result={'status':'passed','optimized':not __debug__,'byte_exact_artifacts':checks,
        'loaded_executable_closure':sorted(imports,key=lambda x:x['path'])}
    a.output.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'status':'passed','files':len(checks),'imports':len(imports),'optimized':not __debug__}))
if __name__=='__main__':main()
