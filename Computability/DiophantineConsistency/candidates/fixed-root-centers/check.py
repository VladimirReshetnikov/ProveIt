#!/usr/bin/env python3
"""Exact cuts and degree leaders for the centered fixed-blank circuits.

Reads only literal JSON and an elementary sparse-ring utility; imports no
construction builder or archived emitter. Unbounded proofs are in PROOF.md.
"""
from collections import Counter
import hashlib
import importlib.util
import json
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parent.parent
RING_PATH=HERE.parent/'positive11-adaptive-shears/independent_ring.py'
spec=importlib.util.spec_from_file_location('sparse_ring',RING_PATH)
ring=importlib.util.module_from_spec(spec);spec.loader.exec_module(ring)
Ring=ring.Ring

def need(ok,label):
    if not ok:raise ValueError(label)

def op(f,a,b):return a+b if f=='+' else a-b if f=='-' else a*b

def cut(packet,target,formal):
    rows={r[0]:r[1:] for r in packet['source']};cache={}
    def go(n):
        if type(n)is int:return Ring.numeral(n)
        if n in formal:return formal[n]
        if n in cache:return cache[n]
        need(n in rows,'closed cut '+n)
        f,a,b=rows[n];v=op(f,go(a),go(b));cache[n]=v;return v
    return go(target)

def topology(packet,count):
    available=set(packet['witnesses']+packet['fixed_numerals']);deps={};counts=Counter()
    for n,f,a,b in packet['source']:
        need(n not in available and f in ['+','-','*'],'fresh producer')
        need(all(type(x)is int or x in available for x in [a,b]),'topological operands')
        deps[n]=[x for x in [a,b] if type(x)is str];available.add(n);counts[f]+=1
    seen=set();todo=[packet['output']]
    while todo:
        n=todo.pop()
        if n not in seen:seen.add(n);todo+=deps.get(n,[])
    need(seen==available,'all rows and input coordinates live')
    need(len(packet['witnesses'])==14 and len(packet['fixed_numerals'])==4,'14unknown4fixed')
    need(sum(counts.values())==packet['operations']==count,'charged operation total')
    return dict(counts)

def parent_prefix(packet,ordinary):
    path=ROOT/'con-zfc-diophantine-forms/36-small-tuple/baseline/product67.json'
    raw=path.read_bytes();need(hashlib.sha256(raw).hexdigest()=='732fecec5df8fecf98019f9aeadab7a63579c3ebfe6c179cbd7027dee24e9d08','parent pin')
    parent=json.loads(raw);dependent={'f'};retained=[]
    for row in parent['source']:
        if any(x in dependent for x in row[2:] if type(x)is str):dependent.add(row[0])
        else:retained.append(row)
    removed={'aux_y2','aux_coefficient_root','R16'} if ordinary else {'aux_y2'}
    prefix=[r for r in retained if r[0] not in removed]
    need(packet['source'][:len(prefix)]==prefix,'unchanged closed prefix')
    return prefix

def prefix_leaders(packet,ordinary):
    prefix=parent_prefix(packet,ordinary)
    sy={n:Ring.variable(n) for n in packet['witnesses']+packet['fixed_numerals']+['q0','k0']}
    env={n:sy[n] for n in packet['witnesses']+packet['fixed_numerals']}
    deg={n:1 if n in packet['witnesses'] else 0 for n in env}
    def operand(x):return (Ring.numeral(x),0) if type(x)is int else (env[x],deg[x])
    for n,f,a,b in prefix:
        av,ad=operand(a);bv,bd=operand(b)
        if f=='*':v,d=av*bv,ad+bd
        elif ad>bd:v,d=av,ad
        elif bd>ad:v,d=(bv if f=='+' else -bv),bd
        else:v,d=op(f,av,bv),ad
        if n=='repunit':
            need(v==sy['beta']*sy['J'],'leading q alias');v=sy['q0']
        if n=='R10b':
            need(v==sy['eta']+sy['zeta'],'leading k alias');v=sy['k0']
        if n=='norm_main':
            need(v==0 and d==22,'main top cancellation')
            v=2*env['R12']*env['R10a']*env['gam'];d=18
        need(v!=0,'nonzero prefix leader '+n)
        env[n]=v;deg[n]=d
    P0=env['norm_pair']*env['norm_index']*env['norm_transport']
    q,k=sy['q0'],sy['k0'];w,s=sy['w'],sy['s']
    Nt=w*(q-sy['F']-sy['alpha'])-sy['z']*q
    expected=8*sy['h']*sy['gamma']*k**3*w**5*s**8*q**29*Nt
    need(P0==expected,'whole prefix P leader')
    need(deg['norm_pair']+deg['norm_index']+deg['norm_transport']==49,'P degree49')
    need(env['A']==w*w*s*s*q**8,'Delta leader')
    need(env['c2']==k*k*s*s*q**6,'c squared leader')
    need(env['r_lhs']==q**3*(q-sy['F']),'rank leader')
    return sy,env,P0

def weighted_leader(poly,weights):
    def wt(mon):return sum(weights[n]*e for n,e in mon)
    d=max(wt(m) for m in poly.terms)
    return d,Ring({m:c for m,c in poly.terms.items() if wt(m)==d})

def verify(name):
    packet=json.loads((HERE/(name+'.json')).read_text());ordinary=name=='ordinary76'
    count=74 if name=='field74' else 76;counts=topology(packet,count)
    sy,env,P0=prefix_leaders(packet,ordinary)
    Q,D,b,u,y,P,dd,p=[Ring.variable(n) for n in ['Q','D','b','u','y','P','Delta','p']]
    if not ordinary:
        prefix='field' if name=='field74' else 'unit'
        aa=Q*(D*u*u+b*b)-(Q-1)*(y-b)**2-1
        norm=aa*aa-4*Q*Q*D*u*u*b*b
        expected=(P*(aa+1)-1)**2-D*(P*2*Q*u*b)**2 if name=='field74' else P*(norm+1)-1
        formal={prefix+'_D':D,prefix+'_b':b,prefix+'_u':u,prefix+'_P':P,'R16':Q,'y':y}
        need(cut(packet,packet['output'],formal)==expected,'complete normalized centered tail')
        adeg,alead=weighted_leader(aa,{'D':34,'Q':46,'b':38,'u':6,'y':1})
        need(adeg==92 and alead==Q*D*u*u,'A degree92 cut')
        weights={'D':34,'Q':46,'b':38,'u':6,'y':1,'P':49}
        degree,leader=weighted_leader(expected,weights)
        want=-4*D*Q*Q*u*u*b*b*(P*P if name=='field74' else P)
        need(leader==want,'centered output abstract leader')
        Q0=env['R16'];D0=env['A']*(sy['i']*env['c2'])**2
        b0=env['r_lhs']*D0;u0=env['R10a']*sy['T']
        actual=-4*D0*Q0**2*u0**2*b0**2*(P0**2 if name=='field74' else P0)
        if name=='field74':
            target={'q0':188,'h':2,'gamma':2,'i':10,'k0':28,'w':24,'s':52,'T':2,'F':2,'z':2};coefficient=-256
        else:
            target={'q0':158,'h':1,'gamma':1,'i':10,'k0':25,'w':19,'s':44,'T':2,'F':2,'z':1};coefficient=32
    else:
        aa=Q*(p+b*b)-(Q-1)*(y-b)**2-dd*dd
        norm=aa*aa-4*Q*Q*p*b*b;expected=P*(norm+1)-1
        formal={'ordinary_p':p,'ordinary_b':b,'ordinary_Q':Q,'ordinary_P':P,'y':y,'A':dd}
        need(cut(packet,packet['output'],formal)==expected,'complete ordinary scaled centered tail')
        c,R,I,tt=[Ring.variable(n) for n in ['c','R','I','T']]
        need(cut(packet,'ordinary_Q',{'ordinary_I':I})==I*I,'Q=I squared')
        need(cut(packet,'ordinary_Dnum',{'ordinary_Q':Q,'A':dd})==dd+Q,'Dnum')
        need(cut(packet,'ordinary_b',{'ordinary_Dnum':D,'A':dd,'R10a':c,'r_lhs':R})==dd*c+R*D,'b numerator')
        need(cut(packet,'ordinary_p',{'Ac2':dd*c*c,'ordinary_Dnum':D,'T':tt})==dd*D*c*c*tt*tt,'scaled p identity')
        weights={'Q':22,'p':46,'b':26,'y':1,'Delta':12,'P':49}
        adeg,alead=weighted_leader(aa,weights);need(adeg==68 and alead==Q*p,'ordinary A degree68')
        degree,leader=weighted_leader(expected,weights)
        need(leader==-4*P*Q*Q*p*b*b,'ordinary output abstract leader')
        Q0=(sy['i']*env['c2'])**2
        b0=env['r_lhs']*Q0;p0=env['A']*Q0*env['c2']*sy['T']**2
        actual=-4*P0*Q0**2*p0*b0**2
        target={'q0':110,'h':1,'gamma':1,'i':10,'k0':25,'w':7,'s':32,'T':2,'F':2,'z':1};coefficient=32
    unknowns=set(packet['witnesses'])|{'q0','k0'}
    need(actual.degree(unknowns)==degree==packet['exact_degree'],'actual homogeneous degree')
    need(actual.coefficient(target,unknowns)==coefficient,'uniform selected coefficient')
    need(sum(target.values())==degree,'selected degree')
    return {'sha256':hashlib.sha256((HERE/(name+'.json')).read_bytes()).hexdigest(),'operations':count,'operation_counts':counts,'exact_degree':degree,'abstract_A_degree':adeg,'selected_compressed_monomial':target,'selected_coefficient':str(coefficient)+'*beta^'+str(target['q0']),'all_gates_unknowns_ports_live':True,'exact_complete_tail_identity':True}

def universal_checks():
    d,Q,R,c,u,y,f,x,z,a,b=[Ring.variable(n) for n in ['d','Q','R','c','u','y','f','x','z','a','b']]
    dn=d+Q;bn=d*c+R*dn;aa=Q*(d*dn*u*u+bn*bn)-(Q-1)*(y-bn)**2-d*d
    B=2*Q*u*bn;E=d*f*f-d-Q;V=u*f-c-R*f*f
    cleared=Q*(d*V)**2-(Q-1)*(y-bn)**2-d*d
    rem=Q*E*(d*u*u-2*R*(d*u*f-bn)+R*R*E)
    need(cleared==aa-B*d*f+rem,'full ordinary remainder identity')
    # Integer norm multiplication/inversion used in the balanced-unit lemma.
    xp=a*x-d*b*z;zp=a*z-b*x
    need(xp*xp-d*zp*zp==(a*a-d*b*b)*(x*x-d*z*z),'integer unit norm preservation')
    # Exact main-norm cancellation used by every prefix leader.
    X,A,C,G,H=[Ring.variable(n) for n in ['X','A','C','G','H']]
    full=(X+A*C+G)**2-(A*A+H)*C*C
    need(full==X*X+2*A*C*X+2*G*X+2*A*C*G+G*G-H*C*C,'main cancellation')
    residues=0
    for aval in range(4):
        for bval in range(4):
            K=(aval*aval-4*bval)%4
            need(K!=2,'norm cannot equal negative2');residues+=1
    # The unguarded ordinary rational-root inference really fails.
    from fractions import Fraction
    need(63*(Fraction(4,3)**2-1)==49,'rational ordinary-root negative control')
    return {'full_scaled_auxiliary_remainder':True,'integer_unit_norm_preservation':True,'main_norm_cancellation':True,'negative_unit_residue_cases':residues,'rational_root_negative_control':{'A':8,'Delta':63,'I':7,'f':'4/3','requires_large_c_hypothesis':True}}

def main():
    result={'status':'PASS','universal_identities':universal_checks(),'circuits':{n:verify(n) for n in ['field74','unit76_reference','ordinary76']},'sparse_ring_sha256':hashlib.sha256(RING_PATH.read_bytes()).hexdigest(),'scope':'Exact finite literal/degree algebra. Balanced-unit and signed-source unbounded proofs are ordinary mathematics in PROOF.md, not finite-test consequences.'}
    path=HERE/('CHECKS_OPTIMIZED.json' if not __debug__ else 'CHECKS.json')
    path.write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
