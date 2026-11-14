#!/usr/bin/env python3
"""Replay the exact released certificate inventory without its builder."""
import argparse
import json
from pathlib import Path
from frozen_positive_emitter import encode, decode
from positive_stream import check_certificate, compile_certificate, require


def E(i,j): return ('E',i,j)
def A(v,f): return ('A',v,f)
def I(f,g): return ('I',f,g)


def raw_target(n):
    # Independent syntactic statement of the lower-first axiom template.
    phi=decode(n)
    atom=E(1,n)
    guard=A(2,I(E(2,1),E(2,0)))
    upper=A(1,I(atom,phi))
    lower=A(1,I(guard,I(phi,atom)))
    return encode(I(A(n,I(lower,I(upper,E(0,0)))),E(0,0)))


def targets():
    out={f'identity_{n}':encode(I(decode(n),decode(n))) for n in (0,1,2,3,7,33)}
    out['capture_avoiding_UI']=encode(I(A(0,A(1,E(0,1))),A(2,E(1,2))))
    out['derived_vacuity']=encode(I(E(0,0),A(1,E(0,0))))
    out['Peirce']=encode(I(I(I(E(0,0),A(0,E(0,0))),E(0,0)),E(0,0)))
    for n in (0,1,2,27,33,128): out[f'raw_axiom_{n}']=raw_target(n)
    q=E(27,27)
    phi=I(I(q,q),q)
    atom=E(1,28)
    guard=A(2,I(E(2,1),E(2,27)))
    upper=A(1,I(atom,phi))
    lower=A(1,I(guard,I(phi,atom)))
    out['raw_axiom_reinstantiation']=encode(I(A(28,I(lower,I(upper,q))),q))
    return out


def verify(data):
    expected=targets()
    require(type(data) is dict and set(data)==set(expected),'certificate inventory mismatch')
    for name,target in expected.items():
        lines=check_certificate(data[name])
        require(lines[-1]==target,f'wrong advertised target: {name}')
        compile_certificate(data[name])
    return {'status':'passed','exact_targets':len(expected),
            'names':sorted(expected),'target_inventory':'independently specified ASTs'}


def suite(path):
    data=json.loads(path.read_text())
    result=verify(data)
    controls=[]
    controls.append(('empty inventory',{}))
    partial=dict(data); partial.pop('Peirce'); controls.append(('missing target',partial))
    extra=dict(data); extra['unadvertised']=data['Peirce']; controls.append(('extra target',extra))
    wrong=dict(data); wrong['Peirce']=data['identity_0']; controls.append(('unrelated valid theorem',wrong))
    for name,bad in controls:
        try: verify(bad)
        except ValueError: pass
        else: raise ValueError('target-contract control accepted: '+name)
    result['rejected_inventory_controls']=[name for name,_ in controls]
    return result


if __name__=='__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('file',nargs='?',type=Path,
                        default=Path(__file__).resolve().parents[1]/'results'/'positive_certificates.json')
    parser.add_argument('--output',type=Path)
    args=parser.parse_args()
    text=json.dumps(suite(args.file),indent=2,sort_keys=True)+'\n'
    if args.output: args.output.write_text(text)
    print(text,end='')
