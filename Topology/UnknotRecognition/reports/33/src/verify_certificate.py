"""Standalone certificate replay; does not invoke either search algorithm."""
from __future__ import annotations
import argparse, json
from pathlib import Path
from dart_kernel import from_pd, triangles, footprint, apply_triangle, reductions

def _darts(value, size):
    if not isinstance(value,list) or len(value)!=size or any(type(d) is not int or d<0 for d in value):
        raise ValueError("invalid literal dart list")
    if len(set(value))!=size: raise ValueError("repeated dart")
    return tuple(value)

def verify(data):
    if not isinstance(data,dict) or data.get("format")!="proveit-r3-layer-certificate-v1":
        raise ValueError("unsupported certificate")
    state=from_pd(data["pd"])
    bound=data["max_depth"]
    if type(bound) is not int or bound<0: raise ValueError("invalid depth")
    layers=data["layers"]
    if not isinstance(layers,list): raise ValueError("invalid layers")
    previous=None; count=0
    for layer in layers:
        if not isinstance(layer,list) or not layer: raise ValueError("empty/invalid layer")
        seen=set(); moves=[]; keys=[]
        legal={tuple(sorted(f)):f for f in triangles(state)}
        for raw in layer:
            key=tuple(sorted(_darts(raw,3)))
            if key not in legal: raise ValueError("triangle is not a legal RIII face")
            support=footprint(state,legal[key])
            if not seen.isdisjoint(support): raise ValueError("layer is not footprint-disjoint")
            if previous is not None and support.isdisjoint(previous):
                raise ValueError("action does not meet preceding layer")
            seen.update(support); keys.append(key); moves.append(legal[key])
        if keys!=sorted(keys): raise ValueError("layer keys are not canonical")
        for f in moves:
            state=apply_triangle(state,f); state.validate()
        previous=frozenset(seen); count+=len(layer)
    if count>bound: raise ValueError("depth exceeded")
    terminal=data["terminal"]
    if not isinstance(terminal,dict) or terminal.get("kind") not in ("R1","R2"):
        raise ValueError("invalid terminal")
    kind=terminal["kind"]
    face=_darts(terminal["face"],1 if kind=="R1" else 2)
    legal=[r for r in reductions(state) if r[0]==kind and set(r[1])==set(face)]
    if len(legal)!=1: raise ValueError("terminal reduction is illegal/ambiguous")
    return {"verified":True,"moves":count,"layers":len(layers),"terminal":kind,
            "final_pd":[list(r) for r in state.pd()]}

def serialize(initial,witness,max_depth):
    kind,face=witness.terminal
    return {"format":"proveit-r3-layer-certificate-v1", "pd":[list(r) for r in initial.pd()],
            "max_depth":max_depth,
            "layers":[[list(a.key) for a in layer] for layer in witness.layers],
            "terminal":{"kind":kind,"face":list(face)}}

def main():
    p=argparse.ArgumentParser(description=__doc__); p.add_argument("certificate",type=Path)
    args=p.parse_args()
    try: result=verify(json.loads(args.certificate.read_text()))
    except (ValueError,KeyError,TypeError) as exc: p.error(str(exc))
    print(json.dumps(result,indent=2))
if __name__=="__main__": main()
