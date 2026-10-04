#!/usr/bin/env python3
"""Independent inert-fixture checker. No import/execute of packet code.

Uses closed-form shear endpoints and closed-form duration sums, followed by
separately specified finite strand-label templates. It never locates/selects a
physical collision or propagates a trajectory. All packet .py/.lean files are
inert bytes or parsed Python syntax.
"""
from pathlib import Path
from fractions import Fraction as F
from math import gcd
import ast
import copy
import hashlib
import json

ROOT = Path('/workspace/shared/five-signal-rotation-family59-20261004')
OUT = Path(__file__).resolve().parent
PROOF_PIN = '14c3d694d9e0c21f3ad3b125c0d1f2bbf47793e1283c9314aa3855ef60c89fc5'
SOURCE_PIN = 'c6ce6ae3873da154c4b7f200f762408f36583d20e424ac6fca4661bd0bd9ce41'
MANIFEST_PIN = '646de47472089e9909fafbf0ed1e1a7851a114d862e4df9b31d0802815772044'

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_text())
def vec(*xs): return tuple(map(F, xs))
def plus(*vs): return tuple(sum(xs, F(0)) for xs in zip(*vs))
def times(c, v): return tuple(c*x for x in v)
def minus(v, w): return plus(v, times(-1,w))
def dot(v,w): return sum((x*y for x,y in zip(v,w)), F(0))
def matmul(A,B): return tuple(tuple(dot(r,c) for c in zip(*B)) for r in A)
def serial(v):
    if isinstance(v,F): return str(v)
    if isinstance(v,dict): return {k:serial(x) for k,x in v.items()}
    if isinstance(v,(tuple,list)): return [serial(x) for x in v]
    return v
def ceiling(q): return -((-q.numerator)//q.denominator)

D,XX,YY=vec(1,0,0),vec(0,1,0),vec(0,0,1)
ZERO=vec(0,0,0)

def static_expectation(a,b,c,lam):
    """Independent expected data; closed block formulas do not iterate endpoints."""
    assert c>1 and a*a+b*b==c*c and gcd(gcd(abs(a),abs(b)),c)==1
    tx,ty=F(-b,c+a),F(b,c)
    nx,ny=max(1,ceiling(4*abs(tx))),max(1,ceiling(4*abs(ty)))
    dx,dy=tx/nx,ty/ny
    K=2*nx+ny
    rows=[]
    plan=[]
    x=plus(times(F(1,3),D),XX)
    y=plus(times(F(2,3),D),YY)
    elapsed=ZERO

    def block(t,z,n,delta,name,target,anchor,near,far,eps):
        nonlocal elapsed
        center=minus(z,times(F(2,3),D))
        endpoints=[]
        for k in range(n+1):
            even=plus(t,times(k*delta,center))
            endpoints.append(even)
            if k<n: endpoints.append(plus(even,times(delta,z)))
        rows.extend([{'name':name+'_fixed_lower','row':z},
                     {'name':name+'_fixed_upper','row':minus(D,z)}])
        for k,e in enumerate(endpoints):
            rows.extend([{'name':f'{name}_endpoint{k}_lower','row':e},
                         {'name':f'{name}_endpoint{k}_upper','row':minus(z,e)}])
        # Sum t_k directly, rather than invoking/iterating translation code.
        starts=plus(times(n,t),times(delta*F(n*(n-1),2),center))
        shifted=plus(starts,times(n*delta,z))
        far_delta=-F(2,3)*delta
        elapsed=plus(elapsed,times(2*(1+1/(1-delta)),starts),
                     times(2*n,z),times(2*(1+1/(1-far_delta)),shifted),times(2*n,D))
        for k in range(n):
            for loc,e,reflector,middle in [('near',delta,near,()),('far',far_delta,far,(near,))]:
                prefix=f'{name}_{k}_{loc}'
                plan.append(('L',prefix+'_L',target,anchor,None,(),1/(1-e),eps))
                plan.append(('H',prefix+'_H',target,anchor,reflector,middle,1-e,eps))
        return plus(t,times(n*delta,center))

    x=block(x,y,nx,dx,'A1','X','L','Y','D',1)
    plan.append(('transfer','transfer_right',None,None,None,(),None,1))
    y=minus(D,block(minus(D,y),minus(D,x),ny,dy,'B','Y','D','X','L',-1))
    plan.append(('transfer','transfer_left',None,None,None,(),None,-1))
    x=block(x,y,nx,dx,'A2','X','L','Y','D',1)
    elapsed=plus(elapsed,times(2,D))
    assert x==vec(F(1,3),F(a,c),F(-b,c))
    assert y==vec(F(2,3),F(b,c),F(a,c))
    if lam!=1:
        elapsed=plus(elapsed,times(2*(1+lam),plus(x,y,D)))
        order=('X','Y','D') if lam<1 else ('D','Y','X')
        inner={'X':(),'Y':('X',),'D':('X','Y')}
        plan.extend(('L','scale_'+q,q,'L',None,inner[q],lam,1) for q in order)

    # Static grammar independently expanded as a list of (marker, action).
    phases=[]; label_speeds={q+'0':F(0) for q in ('L','X','Y','D')}
    prepost=[]
    for kind,name,target,anchor,reflector,intervening,param,eps in plan:
        start=len(prepost)
        if kind=='transfer':
            sequence=[('X','cross'),('Y','cross'),('D','bounce')] if eps==1 else [('Y','cross'),('X','cross'),('L','bounce')]
            temporary=None
        else:
            temporary=target+'_'+name
            speed=eps*(param-1)/(param+1) if kind=='L' else eps*(1-param)/(1+param)
            assert -1<speed<1
            label_speeds[temporary]=speed
            forward=[(q,'cross') for q in intervening]
            reverse=list(reversed(forward))
            if kind=='L':
                sequence=forward+[(target,'launch')]+reverse+[(anchor,'bounce')]+forward+[(target,'restore')]+reverse+[(anchor,'bounce')]
            else:
                sequence=[(target,'launch')]+forward+[(reflector,'bounce')]+reverse+[(target,'restore'),(anchor,'bounce')]
        direction=eps
        for q,act in sequence:
            outgoing=-direction if act=='bounce' or (kind=='L' and act in ('launch','restore')) else direction
            zin=temporary if act=='restore' else q+'0'
            zout=temporary if act=='launch' else q+'0'
            prepost.append((zin,zout,F(direction),F(outgoing)))
            direction=outgoing
        assert direction==(eps if kind!='transfer' else -eps)
        phase={'kind':kind,'name':name,'start':start,'stop':len(prepost)}
        if kind!='transfer': phase.update(target=target,parameter=param)
        phases.append(phase)
    m=len(prepost)
    rules=[]
    for j,(zin,zout,vin,vout) in enumerate(prepost):
        label_speeds['Q'+str(j)]=vin
        assert vout==prepost[(j+1)%m][2]
        rules.append({'in':['Q'+str(j),zin],'out':['Q'+str((j+1)%m),zout]})
    assert len(rows)==4*K+12 and m==18*K+6+24*(lam!=1)
    assert len(label_speeds)==22*K+(10 if lam==1 else 37)
    assert all(r['row'][0]>0 for r in rows)
    distances=[]
    for r in rows:
        alpha,v,w=r['row']; norm=v*v+w*w
        if norm: distances.append((alpha*alpha/norm,(-alpha*v/norm,-alpha*w/norm),r['name']))
    radius=min(d[0] for d in distances)
    nearest=[d for d in distances if d[0]==radius]
    points=sorted({d[1] for d in nearest})
    assert all(dot(p,p)==radius and all(dot(r['row'],(F(1),)+p)>=0 for r in rows) for p in points)
    Q=(vec(1,1,1),vec(F(2,3),F(-1,3),F(-1,3)),vec(F(1,3),F(1,3),F(-2,3)))
    gap_rows=(times(lam,x),times(lam,minus(y,x)),times(lam,minus(D,y)))
    M=matmul(gap_rows,Q)
    N=(vec(lam,0,0),vec(0,lam*F(a,c),-lam*F(b,c)),vec(0,lam*F(b,c),lam*F(a,c)))
    assert matmul(Q,M)==matmul(N,Q)
    result={
        'parameters':{'a':a,'b':b,'c':c,'lambda':lam,'tx':tx,'ty':ty,'Nx':nx,'Ny':ny},
        'counts':{'events':m,'meta_signals':len(label_speeds),'temporary_labels':4*K+3*(lam!=1),'guards':len(rows),'distinct_speeds':len(set(label_speeds.values())),'distinct_nearest_points':len(points)},
        'return_gap_matrix':M,'duration_row':elapsed,'guards':rows,'rho_squared':radius,
        'nearest_guards':nearest,'tangent_points':points,'phases':phases,'speeds':label_speeds,
        'rules':rules,'default_rule':'Identity on every other pairwise-distinct-speed collision input set'}
    return serial(result)

def compare_fixture(data):
    p=data['parameters']
    expected=static_expectation(p['a'],p['b'],p['c'],F(p['lambda']))
    assert set(data)==set(expected)
    for key in expected:
        assert data[key]==expected[key], ('fixture field mismatch',p,key)
    # Label occupancy only, no times/positions or collision search.
    live={'Q0','L0','X0','Y0','D0'}
    speed={k:F(v) for k,v in data['speeds'].items()}
    input_sets=set()
    for rule in data['rules']:
        ins,outs=set(rule['in']),set(rule['out'])
        assert len(ins)==len(outs)==2 and ins<=live
        assert len({speed[s] for s in ins})==len({speed[s] for s in outs})==2
        assert frozenset(ins) not in input_sets
        input_sets.add(frozenset(ins))
        live=(live-ins)|outs
        assert len(live)==5
    assert live=={'Q0','L0','X0','Y0','D0'}
    return expected

def main():
    assert sha(ROOT/'PROOF.md')==PROOF_PIN
    assert sha(ROOT/'static_family.py')==SOURCE_PIN
    assert sha(ROOT/'PACKET_MANIFEST.json')==MANIFEST_PIN
    before={str(p.relative_to(ROOT)):sha(p) for p in ROOT.rglob('*') if p.is_file()}
    manifest=read(ROOT/'PACKET_MANIFEST.json')
    for entry in manifest['files']:
        p=ROOT/entry['path']
        assert p.stat().st_size==entry['bytes'] and sha(p)==entry['sha256']
    assert set(before)=={e['path'] for e in manifest['files']}|{'PACKET_MANIFEST.json'}
    syntax=ast.parse((ROOT/'static_family.py').read_text())
    imports=[]
    for node in ast.walk(syntax):
        if isinstance(node,ast.Import): imports.extend(a.name for a in node.names)
        if isinstance(node,ast.ImportFrom): imports.append(node.module)
    assert set(imports)=={'fractions','math','json','hashlib','pathlib'}
    receipt=read(ROOT/'evidence/STATIC_RECEIPT.json')
    fixture_files=sorted((ROOT/'evidence').glob('a*_scale*.json'))
    assert len(fixture_files)==receipt['fixture_count']==len(receipt['fixtures'])==45
    summaries={r['file']:r for r in receipt['fixtures']}
    audit=[]
    for p in fixture_files:
        data=read(p); expected=compare_fixture(data); summary=summaries[p.name]
        assert summary['sha256']==sha(p)
        expected_summary={'file':p.name,'sha256':sha(p),**expected['parameters'],**expected['counts'],'rho_squared':expected['rho_squared'],'tangent_points':expected['tangent_points']}
        assert summary==expected_summary
        audit.append({'file':p.name,'sha256':sha(p),'events':len(data['rules']),'guards':len(data['guards']),'phases':len(data['phases']),'tangencies':len(data['tangent_points'])})
    # Negative controls must fail independent field reconstruction.
    seed=read(ROOT/'evidence/a3_b4_c5_scale1over2.json')
    mutations=[]
    def reject(name,change):
        altered=copy.deepcopy(seed); change(altered)
        try: compare_fixture(altered)
        except (AssertionError,KeyError,ValueError,TypeError): mutations.append(name)
        else: raise AssertionError(('undetected mutation',name))
    reject('delete spectator event',lambda d:d['rules'].pop(13))
    reject('swap contraction order',lambda d:d['phases'].__setitem__(slice(-3,None),list(reversed(d['phases'][-3:]))))
    reject('flip reflected target speed',lambda d:d['speeds'].__setitem__('Y_B_0_near_L','1/9'))
    reject('change guard coefficient',lambda d:d['guards'][4]['row'].__setitem__(0,'0'))
    reject('drop initial ordering row',lambda d:d['guards'].pop(3))
    reject('relax tangent sign',lambda d:d['tangent_points'][0].__setitem__(1,'7/65'))
    reject('alter duration',lambda d:d['duration_row'].__setitem__(0,'1'))
    reject('alter return orientation',lambda d:d['return_gap_matrix'][0].__setitem__(0,'1'))
    reject('omit default',lambda d:d.pop('default_rule'))
    reject('use stale messenger label',lambda d:d['rules'][8]['out'].__setitem__(0,'Q8'))
    reject('collapse temporary to stationary',lambda d:d['rules'][0]['out'].__setitem__(1,'X0'))
    reject('change phase endpoint',lambda d:d['phases'][0].__setitem__('stop',5))
    after={str(p.relative_to(ROOT)):sha(p) for p in ROOT.rglob('*') if p.is_file()}
    assert before==after
    result={'status':'PASS','scope':'independent closed-form rational endpoints, closed-form duration sums, static finite rule grammar, inert source syntax, manifest and all fixture fields; no physical simulator or author/upstream code executed',
            'proof_sha256':PROOF_PIN,'source_sha256':SOURCE_PIN,'packet_manifest_sha256':MANIFEST_PIN,
            'packet_file_count':len(before),'manifest_entries':len(manifest['files']),
            'fixture_count':len(audit),'total_events':sum(x['events'] for x in audit),'total_guard_rows':sum(x['guards'] for x in audit),'total_phases':sum(x['phases'] for x in audit),
            'all_fixture_tangencies_unique':all(x['tangencies']==1 for x in audit),
            'negative_controls':mutations,'inert_source_imports':imports,'packet_bytes_preserved':True,'fixtures':audit}
    (OUT/'STATIC_INDEPENDENT_RECEIPT.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'AUTHOR_PACKET_SNAPSHOT.json').write_text(json.dumps(before,indent=2,sort_keys=True)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='fixtures'},indent=2))

if __name__=='__main__': main()
