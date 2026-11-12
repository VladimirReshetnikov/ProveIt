"""Replay new certificates against both matched controls and the bounded checker.

The translations only elaborate fields removed by the new interface.
The separate witness-to-deterministic compiler tests the converse direction.
"""
from pathlib import Path
import ast, importlib.util, json
ROOT=Path(__file__).resolve().parents[1]
FIXTURES=ROOT/'validation/fixtures/positive'
def load(filename,name):
    spec=importlib.util.spec_from_file_location(name,ROOT/'code'/filename);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
K=load('checker.py','base')
C=load('control_witness.py','control_witness')
N=load('control_name.py','control_name')
F=load('checker_fuel.py','bounded')
CTX=[([], [1,1])]
def explicit(p,g):
    n=len(g);code,*args=p
    if type(code)is int:
        t,q=args;base,B=g[code]
        return [code,t,explicit(q,g) if base else None]
    if code:
        r,=args;B=K.sub(code,1-n,1);base=K.sub(B,0)
        hyp=K.sub(B,-n) if base==[0,0] else base
        return [code,1-n,explicit(r,g+[([],hyp)])]
    q,r=args;major=K.prove(q,g);B=K.sub(major[0],-n,1)
    return [[],explicit(q,g),explicit(r,g+[(K.sub(B,0),B)])]

def named(p,g):
    n=len(g);b=-n;code,*args=p
    if type(code)is int:
        t,q=args;base,B=g[code]
        return [code,t,named(q,g) if base else None]
    if code:
        r,=args;B=K.sub(code,1-n,1);base=K.sub(B,0)
        hyp=K.sub(B,b) if base==[0,0] else base
        return [code,named(r,g+[([],hyp)])]
    q,r=args;major=K.prove(q,g);B=K.sub(major[0],b,1)
    base=K.sub(B,0);row=K.sub(B,[0,0,0])
    eq=[n,[0,0,0],[0,0,None]] if base==[0,0] and row[0]==b else [0,b,None]
    return [[],named(q,g),eq,named(r,g+[(base,B)])]

report={'matched_witness_replays':0,'matched_name_replays':0,'fuel_boundaries':0,'invalid_fuels':0,'budgets':{}}
for path in sorted(FIXTURES.glob('*.json')):
    goal,p=json.loads(path.read_text())
    K.check([goal,p]);C.check([goal,explicit(p,CTX)]);N.check([goal,named(p,CTX)])
    report['matched_witness_replays']+=1;report['matched_name_replays']+=1
    F.check([goal,p,10**8]);used=10**8-F.fuel
    F.check([goal,p,used]);report['fuel_boundaries']+=1
    try:F.check([goal,p,used-1])
    except Exception:pass
    else:raise AssertionError((path.name,'one-short fuel accepted'))
    report['fuel_boundaries']+=1;report['budgets'][path.name]=used
for bad in (-1,True,False,0.0,1.0,'999',None,[],{}):
    try:F.check([[0,0],[0,0,None],bad])
    except Exception:pass
    else:raise AssertionError(('invalid fuel accepted',bad))
    report['invalid_fuels']+=1
(ROOT/'evidence/controls_and_fuel_audit.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
