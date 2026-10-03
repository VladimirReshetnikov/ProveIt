#!/usr/bin/env python3
"""Verify every concrete essential-input witness with two evaluators.
This checker uses explicit exceptions and stays active under python -O.
"""
import importlib.util
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent.parent

def load(name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'code'/f'{name}.py')
    module=importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module

def require(condition,detail):
    if not condition: raise RuntimeError(detail)

def main():
    direct=load('component_rule'); local=load('local_rule')
    data=json.loads((ROOT/'audit'/'essential-input-witnesses.json').read_text())
    rectangle={(x,y) for x in range(-6,7) for y in range(-3,3)}
    found=set()
    for w in data['witnesses']:
        changed=tuple(w['changed_input'])
        a={tuple(p) for p in w['input0']}; b={tuple(p) for p in w['input1']}
        require(a^b=={changed},('more than one changed input',changed))
        va=int((0,0) in direct.step(a)); vb=int((0,0) in direct.step(b))
        require(va==w['output0'] and vb==w['output1'] and va!=vb,('bad witness',changed))
        require(local.evaluate(local.neighborhood(a,(0,0)))==va,('local first mismatch',changed))
        require(local.evaluate(local.neighborhood(b,(0,0)))==vb,('local second mismatch',changed))
        # Translating both input configurations down one row gives the matching
        # F witness, because F(S)(0)=G(S)(0,-1).
        ad={(x,y-1) for x,y in a}; bd={(x,y-1) for x,y in b}
        require(local.drift_evaluate(local.neighborhood(ad,(0,0)))==va,('drift first mismatch',changed))
        require(local.drift_evaluate(local.neighborhood(bd,(0,0)))==vb,('drift second mismatch',changed))
        found.add(changed)
    require(found==rectangle,('incomplete essential rectangle',rectangle-found))
    require(len(data['witnesses'])==78,'duplicate or missing witnesses')
    print('PASS: all 78 one-cell essentiality witnesses for G, independently evaluated by component and radius-local rules; translated witnesses also verify all 78 essential cells of F. Explicit checks remain active under -O.')
if __name__=='__main__': main()
