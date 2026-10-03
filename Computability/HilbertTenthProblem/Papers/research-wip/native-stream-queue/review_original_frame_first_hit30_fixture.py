#!/usr/bin/env python3
"""Independent coefficient/ledger/trajectory audit; dependencies are inert data."""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

AUTHOR_PINS = {
 'original_frame_first_hit30_fixture.py':'ba0015f75f709a67796a63da4184d1f922a8f5c5f64ec9ec767443e3066869fd',
 'original_frame_first_hit30_fixture.json':'69c4de90ab15d2397b0a0a7c23ff70b8316c81e3824af364faa92bbe6988af4e',
 'original_frame_first_hit30_fixture.md':'8e9f78d88c3d87ea403e4c749bea1ddfb5582fdc6b1c23ae2fe7c29f587662a7'}
def require(ok, message):
    if not ok:
        raise ValueError(message)
def digest(data):
    return hashlib.sha256(data).hexdigest()
def exact(a,b):
    if type(a) is not type(b): return False
    if type(a) is dict: return a.keys()==b.keys() and all(exact(a[k],b[k]) for k in a)
    if type(a) is list: return len(a)==len(b) and all(exact(x,y) for x,y in zip(a,b))
    return a==b

# Fixed exponent-vector ring, independent of the author's string-monomial ring.
NAMES = ['Lx','Ly','Hx','Hy','Rx','Ry','phase','e','sEn','sEj','sEk',
         'sWn','sWj','sWk','t','U','N','j','r']
ZERO = (0,)*len(NAMES)
def constant(c): return {ZERO:c} if c else {}
def atom(n):
    p=list(ZERO);p[NAMES.index(n)]=1
    return {tuple(p):1}
def plus(*ps):
    out=Counter()
    for p in ps:
        for m,c in p.items():out[m]+=c
    return {m:c for m,c in out.items() if c}
def scale(k,p):return {m:k*c for m,c in p.items() if k*c}
def product(a,b):
    out=Counter()
    for m,c in a.items():
        for n,d in b.items():out[tuple(x+y for x,y in zip(m,n))]+=c*d
    return {m:c for m,c in out.items() if c}
def square(p):return product(p,p)
def sub(a,b):return plus(a,scale(-1,b))
def sum_squares(rs):return plus(*(square(r) for r in rs))
def coefficients(p):
    rows=[]
    for mon,c in p.items():
        names=[]
        for n,k in zip(NAMES,mon):names.extend([n]*k)
        rows.append([sorted(names),c])
    return sorted(rows)
def stable(x):return json.dumps(x,sort_keys=True,separators=(',',':')).encode()

def reference(mode):
    projected=mode.endswith('_projected')
    base=mode.removesuffix('_projected')
    Lx,Ly,H,Hy,R,Ry,b=[atom(n) for n in NAMES[:7]]
    t=atom('t');e=sub(constant(1),b) if projected or base=='unified_direct' else atom('e')
    f=sub(constant(1),e)
    n=plus(R,constant(-4),e)
    C=plus(t,scale(-1,product(R,plus(R,constant(-3)))),
           scale(-1,product(sub(e,f),H)),e)
    geometry=[Lx,sub(Hy,Ly),sub(Ly,plus(t,n)),sub(sub(Ry,Ly),f)]
    if base=='unified_direct':
        rows=[product(b,e),sub(plus(H,constant(-1)),atom('j')),
              sub(plus(R,scale(-1,H),constant(-1),scale(-1,b)),atom('r')),
              *geometry,C]
    else:
        forms=[plus(R,constant(-3)),plus(H,constant(-1)),plus(R,scale(-1,H),constant(-1)),
               plus(R,constant(-4)),plus(R,scale(-1,H),constant(-2)),plus(H,constant(-1))]
        rows=[product(e,plus(e,constant(-1)))]
        rows += [sub(product(s,A),atom(name)) for s,A,name in zip([e,e,e,f,f,f],forms,NAMES[8:14])]
        rows += geometry
        if not projected:rows.append(sub(b,f))
        if base=='generic_square':
            J=sub(atom('U'),square(R))
            rows += [J,sub(C,J)]
        elif base=='shared_cycle':
            N=atom('N')
            K=plus(product(e,plus(H,constant(-1))),
                   product(f,plus(scale(2,R),constant(-4),scale(-1,H))))
            rows += [sub(N,n),sub(t,plus(square(N),scale(3,N),K))]
        else:
            require(base=='direct_clock','reference mode')
            rows.append(C)
    return rows,sum_squares(rows)

def evaluate(poly,values):
    answer=0
    for powers,c in poly.items():
        value=c
        for n,k in zip(NAMES,powers):
            if k:value*=values[n]**k
        answer+=value
    return answer

def replace(poly,name,value):
    index=NAMES.index(name);out=constant(0)
    for m,c in poly.items():
        power=m[index];rest=list(m);rest[index]=0
        term={tuple(rest):c}
        for _ in range(power):term=product(term,value)
        out=plus(out,term)
    return out

def identities(polys):
    e=atom('e');R=atom('Rx');N=atom('N')
    C=reference('direct_clock')[0][-1]
    J=sub(atom('U'),square(R))
    require(sub(polys['generic_square'],polys['direct_clock'])==
            plus(scale(2,square(J)),scale(-2,product(C,J))),'complete generic correction')
    n=plus(R,constant(-4),e);L=sub(N,n)
    B=product(e,plus(e,constant(-1)))
    D=plus(B,product(L,plus(N,n,constant(3))))
    require(sub(polys['shared_cycle'],polys['direct_clock'])==
            plus(square(L),square(D),scale(-2,product(C,D))),'complete cycle correction')
    for mode in ['generic_square','shared_cycle','direct_clock']:
        require(replace(polys[mode],'e',sub(constant(1),atom('phase')))==
                polys[mode+'_projected'],'entire external-selector projection')
    return dict(full_offzero_corrections=2,full_selector_graph_identities=3)

def mode_key(p):
    return p['mode']+('_projected' if p['project_phase'] and p['mode']!='unified_direct' else '')

def audit_packet(p):
    supplied=p['external']+p['witnesses']
    require(len(supplied)==len(set(supplied)),'supplied distinct')
    env={n:atom(n) for n in supplied};defs={};count=Counter()
    for name,op,a,b in p['source']:
        require(name not in env and op in ['+','-','*'],'valid fresh row')
        require(all(type(v) is int or type(v) is str and v in env for v in (a,b)),'closed source')
        aa=constant(a) if type(a) is int else env[a]
        bb=constant(b) if type(b) is int else env[b]
        env[name]=product(aa,bb) if op=='*' else plus(aa,scale(1 if op=='+' else -1,bb))
        defs[name]=(a,b);count['M' if op=='*' else 'A']+=1
    todo=[p['output']];live=set()
    while todo:
        v=todo.pop()
        if type(v) is int or v in live:continue
        live.add(v);todo.extend(defs.get(v,()))
    require(live==set(env),'every gate/port live')
    rs,poly=reference(mode_key(p))
    actual=[env[r] if type(r) is str else constant(r) for r in p['residuals']]
    require(actual==rs,'all residual coefficient dictionaries')
    require(env[p['output']]==poly,'entire output coefficients')
    require(max(map(sum,poly))==4,'exact quartic')
    require(len(p['source'])-p['final_start']==2*len(rs)-1,'complete SOS charge')
    require(count['M']==p['ledger']['M'] and count['A']==p['ledger']['A'],'saved ledger')
    require(digest(stable(coefficients(poly)))==p['coefficient_sha256'],'coefficient hash')
    return poly,dict(mode=mode_key(p),M=count['M'],A=count['A'],gates=len(defs),witnesses=len(p['witnesses']),residuals=len(rs),coefficient_entries=len(poly),exact_degree=4)

def step(state):
    # Three occupied positions only; direct transcription of printed single-head rules.
    L,H,R,head=state
    L=list(L);H=list(H);R=list(R)
    if head==0:
        if H[0]+1==R[0] and H[1]==R[1]:
            R=[H[0]+2,H[1]+1];head=1
        else:H[0]+=1
    else:
        if H[0]-1==L[0] and H[1]==L[1]:
            L[1]+=1;H[1]+=1;head=0
        else:H[0]-=1
    for point in [L,H,R]:point[1]+=1
    return tuple(L),tuple(H),tuple(R),head

def verify(root,repo):
    require(len(AUTHOR_PINS)==3,'frozen author trio')
    for name,pin in AUTHOR_PINS.items():require(digest((root/name).read_bytes())==pin,'pin '+name)
    data=json.loads((root/'original_frame_first_hit30_fixture.json').read_text())
    for name,pin in data['pins'].items():require(digest((repo/name).read_bytes())==pin,'placed proof pin')
    polys={};certs=[]
    for packet in data['packets']:
        require(mode_key(packet) not in polys,'unique mode')
        poly,cert=audit_packet(packet);polys[mode_key(packet)]=poly;certs.append(cert)
    ring=identities(polys)
    state=((0,0),(1,0),(3,0),0);zero_checks=0
    for tick,fixture in enumerate(data['fixtures']):
        external=fixture['external']
        require(tuple(external[n] for n in ['Lx','Ly','Hx','Hy','Rx','Ry','phase'])==(*state[0],*state[1],*state[2],state[3]),'independent exact physical step')
        require(len(fixture['zeros'])==len(polys),'all fixture maps present')
        for z in fixture['zeros']:
            w=z['witness'];require(w['t']==tick and all(type(v) is int and v>=0 for v in w.values()),'canonical natural time/coordinates')
            require(evaluate(polys[mode_key(z)],dict(external,**w))==0,'full legal zero')
            zero_checks+=1
        state=step(state)
    require(len(data['fixtures'])==88,'eight complete cycles')
    require(state==((0,96),(1,96),(11,96),0),'next cycle ownership')
    boundary=[]
    for phase in [0,1]:
        n=-1;R=2+phase;H=1;t=phase-2
        values=dict(Lx=0,Ly=t+n,Hx=H,Hy=t+n,Rx=R,Ry=t+n+phase,
                    phase=phase,j=0,r=0,t=t)
        require(evaluate(polys['unified_direct'],values)==0 and t<0,'excluded negative-time zero')
        values.update(t=0,Ly=n,Hy=n,Ry=n+phase)
        rejected=evaluate(polys['unified_direct'],values)
        require(rejected==(2-phase)**2,'natural boundary rejected')
        boundary.append(dict(phase=phase,only_zero_time=t,natural_t0_output=rejected))
    require(len(certs)==7 and sum(c['gates'] for c in certs)==404,'seven-source inventory')
    return dict(status='PASS',source_sha256=digest(Path(__file__).read_bytes()),author_pins=AUTHOR_PINS,
                proof_pins=data['pins'],source_certificates=certs,complete_sources=len(certs),
                paid_gates=sum(c['gates'] for c in certs),coefficient_entries=sum(c['coefficient_entries'] for c in certs),
                full_legal_zero_checks=zero_checks,distinct_configurations=88,identities=ring,
                excluded_negative_index_boundaries=boundary,
                scope='Independent fixed-input quartic coefficient/ledger/physical-trajectory review. No general CA compiler or universal operation claim.')

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True);ap.add_argument('--repo',type=Path,required=True)
    mode=ap.add_mutually_exclusive_group(required=True);mode.add_argument('--output',type=Path);mode.add_argument('--expect',type=Path);a=ap.parse_args()
    result=verify(a.root,a.repo)
    if a.output:a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    if a.expect:require(exact(result,json.loads(a.expect.read_text())),'exact saved receipt')
    print(json.dumps({k:result[k] for k in ['status','complete_sources','paid_gates','coefficient_entries','full_legal_zero_checks']}))
if __name__=='__main__':main()
