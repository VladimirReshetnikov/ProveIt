"""Shared loading for finite QH6 reduction experiments."""
from pathlib import Path
import importlib.util,json,hashlib,sys

def runtime(root):
    p=root/'construction/symbolic_runtime.py'
    spec=importlib.util.spec_from_file_location('reduction_runtime',p)
    mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod);return mod

def load(root):
    c=runtime(root);folder=root/'machine';rows={}
    raw=(folder/'machine.native.tm').read_bytes()
    for line in raw.decode().splitlines():
        q,b,w,d,n=line.split();rows[int(q),int(b)]=(int(w),d=='R',int(n))
    sites=json.loads((folder/'sites.json').read_text());instructions=json.loads((folder/'instructions.json').read_text());contracts=[]
    frame=lambda i,extra=0,effect=c.PLAIN:c.frame(tuple(map(int,sites[i][0])),extra,effect)
    for i,ins in enumerate(instructions):
        start=frame(i)
        if ins[0]=='inc':
            _,r,n=ins;contracts.append((i,None,start,c.canonical(frame(n,0,('x','inc',c.PHYSICAL[r])))))
        elif ins[0]=='dec':
            _,r,z,p=ins;contracts.append((i,(c.PHYSICAL[r],True),start,c.canonical(frame(z))))
            contracts.append((i,(c.PHYSICAL[r],False),start,c.canonical(frame(p,1,('x','dec',c.PHYSICAL[r])))))
        elif ins[0]=='jump':contracts.append((i,None,start,c.canonical(frame(ins[1]))))
        else:assert ins==['halt'];contracts.append((i,None,start,None))
    return c,rows,sites,instructions,contracts,hashlib.sha256(raw).hexdigest()
