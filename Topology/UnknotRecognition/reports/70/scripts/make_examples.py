#!/usr/bin/env python3
from pathlib import Path
import json
import sys
ROOT=Path(__file__).resolve().parents[1]
sys.path.insert(0,str(ROOT/'src'))
from affine_orbits import Model,Edge,Weight,Defect,BulkIndex,SparseOverlay
from affine_orbits.core import wire
from affine_orbits.certificate import make_certificate
from affine_orbits.checker import verify

def emit(name,m,defects=()):
    data=dict(model=m.as_dict(),defects=[vars(d) for d in defects])
    i=BulkIndex(m);o=SparseOverlay(i)
    for d in defects:o.add(d)
    cert=make_certificate(i,o);assert verify(m,defects,cert)
    (ROOT/f'examples/{name}.json').write_text(json.dumps(wire(data),indent=2)+'\n')
    (ROOT/f'examples/{name}.certificate.json').write_text(json.dumps(wire(cert),indent=2)+'\n')

K=3;d=4*K+4;W=5*d
m=Model(1,W,1,(Edge(0,0,1,d),Edge(0,0,-1,0)),
        tuple(Weight(0,d-j,4*d+K+j+1,(1,)) for j in range(1,K+1)))
emit('sharp-nine-profiles',m)
m=Model(1,8,1,(),(Weight(0,0,8,(1,)),))
emit('attachment-same-component',m,[Defect(0,0,0,0,(-1,))])
emit('attachment-distinct-components',m,[Defect(0,0,0,1,(-1,))])
W=1<<1024
m=Model(2,W,2,(Edge(0,1,-1,17),Edge(0,0,1,W//16),Edge(0,0,-1,0)),
        (Weight(0,0,W,(1,0)),Weight(1,7,W-13,(0,1))))
emit('binary1024',m,[Defect(0,0,1,W-1,(-1,0))])
