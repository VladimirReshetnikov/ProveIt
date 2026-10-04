#!/usr/bin/env python3
"""Independent, source-pinned static verification of frozen branching64.

Standard library only. No author module is loaded or executed. No event is
predicted, no live configuration is advanced, and no program is simulated.
The manually transcribed proof tables are checked as finite algebraic data.
Source files are opened read-only with O_NOATIME; output goes only to stdout.
"""
import argparse
import hashlib
import json
import os
from fractions import Fraction as Q
from itertools import product
from pathlib import Path

PINS = {
    'PROOF.md': '85f5de45c0a30f8bdf45b82a613ef9e5a8c766b5d8215d17a3ebbbd0f60b370f',
    'MANIFEST.json': 'e5d9f9a399ab9515a13b66ea4160b063a585c801002105b62f4528da516c1589',
    'README.md': '4d51e383b9df76e3e6baca3d83a8cb958273364b342df3e95549e8f7d231a1b1',
    'static_algebra.py': '270dbc8d79f09d390f8c9558adcc9dfddb5aa5cb5ba2e15d44d90b3a472f1f00',
    'dependencies/realization63_PROOF.md': '31f0db773daa015075e74dabb8955c110288e1c0f9ed2121c647df034773aa67',
    'evidence/static_checks.json': '482d1c79ab16b83173fed84dbf491d8effc0ff3cdf14c48a9b578d8cb9c17d73',
}
NASSERT = 0

def check(condition, explanation):
    global NASSERT
    NASSERT += 1
    if not condition:
        raise ValueError(explanation)

class A:
    """Homogeneous affine expression in (D,x,y), also used as (D,t,s)."""
    def __init__(self, d=0, x=0, y=0): self.c = tuple(Q(z) for z in (d,x,y))
    def __add__(self,o): return A(*(u+v for u,v in zip(self.c,o.c)))
    def __sub__(self,o): return A(*(u-v for u,v in zip(self.c,o.c)))
    def __neg__(self): return self * -1
    def __mul__(self,n): return A(*(v*Q(n) for v in self.c))
    __rmul__ = __mul__
    def __truediv__(self,n): return self * (1/Q(n))
    def __eq__(self,o): return isinstance(o,A) and self.c == o.c
    def at(self,d,x,y): return sum(v*Q(w) for v,w in zip(self.c,(d,x,y)))
    def subst(self,d,x,y): return d*self.c[0]+x*self.c[1]+y*self.c[2]
    def serial(self): return [str(v) for v in self.c]

O,D,x,y = A(),A(1),A(0,1),A(0,0,1)
SPEEDS = {'L':Q(0),'X':Q(0),'Y':Q(0),'R':Q(0),
          'q0':Q(1),'q1':Q(-3,2),'q2':Q(1),'q3':Q(-1,4),'q4':Q(4),
          'pre':Q(-1,2),'fast':Q(2),'post':Q(-1,2),'cZ':Q(-1),'cN':Q(-1),
          'outZ':Q(1),'outN':Q(1)}
RULES={}

def rule(ins,outs):
    key=frozenset(ins); val=frozenset(outs)
    check(len(ins)==len(key)==len(outs)==len(val)==2,'binary distinct labels')
    check(len({SPEEDS[z] for z in ins})==2,'distinct incoming speeds')
    check(len({SPEEDS[z] for z in outs})==2,'distinct outgoing speeds')
    check(key not in RULES or RULES[key]==val,'deterministic rule inputs')
    RULES[key]=val

for ins,outs in [
    (('q0','X'),('q1','pre')),(('q1','L'),('q2','L')),
    (('q2','pre'),('q3','fast')),(('q3','L'),('q4','L')),
    (('fast','Y'),('post','Y')),(('q4','post'),('cZ','X')),
    (('q4','fast'),('cN','X'))]: rule(ins,outs)

for branch in ('Z','N'):
    for name in ('q0','q1','q2','q3','q4','pre','fast','post','c'+branch):
        SPEEDS[f'{name}r{branch}']=-SPEEDS[name]
    rev=lambda name: f'{name}r{branch}'
    rule(('c'+branch,'L'),(rev('c'+branch),'L'))
    rule((rev('c'+branch),'X'),(rev('q4'),rev('post' if branch=='Z' else 'fast')))
    if branch=='Z': rule((rev('post'),'Y'),(rev('fast'),'Y'))
    for ins,outs in [
        ((rev('q4'),'L'),(rev('q3'),'L')),
        ((rev('q3'),rev('fast')),(rev('q2'),rev('pre'))),
        ((rev('q2'),'L'),(rev('q1'),'L')),
        ((rev('q1'),rev('pre')),(rev('q0'),'X')),
        ((rev('q0'),'L'),('out'+branch,'L'))]: rule(ins,outs)

TEST_RULES=dict(RULES)

# Rows record absolute time, positions in fixed role order L,Q,X,Y,R,
# and outgoing labels in that order. These are declarations, not a schedule engine.
def row(time,q,target,qlabel,xlabel):
    return (time,[O,q,target,y,D],['L',qlabel,xlabel,'Y','R'])

prefix=[row(O,O,x,'q0','X'),row(x,x,x,'q1','pre'),
        row(5*x/3,O,2*x/3,'q2','pre'),
        row(19*x/9,4*x/9,4*x/9,'q3','fast'),
        row(35*x/9,O,4*x,'q4','fast')]
f=(10*y-8*x)/9
zword=prefix+[
    row(17*x/9+y/2,2*y-8*x,y,'q4','post'),
    row(11*x/3+5*y/18,f,f,'cZ','X'),
    row(25*(2*x+y)/18,O,f,'cZrZ','X')]
nword=prefix+[
    row(53*x/9,8*x,8*x,'cN','X'),
    row(125*x/9,O,8*x,'cNrN','X')]

# Read-only proof checks validate all ten unordered strand pairs, all five
# velocities, and all unchanged remote labels at each listed event.
def audit_rows(name,rows,strict,rulebook=RULES):
    events=[]
    for n,(tm,positions,labels) in enumerate(rows):
        zeros=[]
        for i in range(5):
            for j in range(i+1,5):
                diff=positions[j]-positions[i]
                if diff==O: zeros.append((i,j))
                else: strict(diff, f'{name} endpoint {n} pair {i},{j}',allow_negative=True)
        check(len(zeros)==1,f'{name}: exactly one binary contact at endpoint {n}')
        if n:
            oldtm,oldpos,oldlabels=rows[n-1]
            dt=tm-oldtm
            strict(dt,f'{name} flight {n}',allow_negative=False)
            for i in range(5):
                check(positions[i]-oldpos[i] == SPEEDS[oldlabels[i]]*dt,
                      f'{name} flight {n} role {i} velocity identity')
            # On an open flight every pair must have a fixed nonzero order.
            for i in range(5):
                for j in range(i+1,5):
                    a=oldpos[j]-oldpos[i]; b=positions[j]-positions[i]
                    if a!=O and b!=O:
                        check(strict(a,'old order',True)==strict(b,'new order',True),
                              f'{name} flight {n} unlisted crossing')
                    check(not(a==O and b==O),f'{name}: no coincident flight')
            i,j=zeros[0]
            check(frozenset((oldlabels[i],oldlabels[j])) in rulebook,
                  f'{name} event {n} missing local rule')
            check(rulebook[frozenset((oldlabels[i],oldlabels[j]))] == frozenset((labels[i],labels[j])),
                  f'{name} event {n} wrong local outputs')
            for k in set(range(5))-{i,j}:
                check(oldlabels[k]==labels[k],f'{name}: remote label change')
            events.append({'number':n,'time':tm.serial(),'contact_roles':[i,j],
                           'flight_duration':dt.serial(),'labels_after':labels})
    return events

def cone(branch):
    basis=(2*D+x+y,(D+x)/4,2*D+x) if branch=='Z' else (8*D+x+y,D,8*D+x)
    # Formal variables D,x,y in this basis stand for three independent positive slacks.
    def strict(expr,why,allow_negative=False):
        coeff=expr.subst(*basis).c
        sign=1 if all(v>=0 for v in coeff) and any(v>0 for v in coeff) else -1 if all(v<=0 for v in coeff) and any(v<0 for v in coeff) else 0
        check(sign==1 or (allow_negative and sign==-1),why+' lacks strict cone sign')
        return sign
    return strict

def reverse_word(rows,branch):
    # Formal time-reflection of declarations, no dynamic evolution.
    T=rows[-1][0]; result=[]
    for n in range(len(rows)-1,-1,-1):
        tm,positions,_=rows[n]
        source_labels=rows[n-1][2] if n else ['L','q0','X','Y','R']
        labels=[z if z in ('L','X','Y','R') else f'{z}r{branch}' for z in source_labels]
        if n==0: labels=['L','out'+branch,'X','Y','R']
        result.append((T-tm,positions,labels))
    return result

RESULT={'scope':'independent static identities and local rule incidence; not simulation',
        'test_words':{}}
for branch,rows in [('Z',zword),('N',nword)]:
    forward=audit_rows(branch+' forward',rows,cone(branch))
    reverse=reverse_word(rows,branch)
    check(reverse[0][2]==rows[-1][2],branch+' real anchor interface')
    backward=audit_rows(branch+' inverse',reverse,cone(branch))
    check(reverse[-1][1]==rows[0][1],branch+' restores all marker positions')
    check(reverse[-1][2]==['L','out'+branch,'X','Y','R'],branch+' restores stationary labels')
    RESULT['test_words'][branch]={'forward':forward,'inverse':backward,
        'total_events':len(forward)+len(backward),
        'duration':(2*rows[-1][0]).serial()}

# Independently check the boundary comparisons used in the first-failure proof.
check((17*x/9+y/2)-(35*x/9)==(y-4*x)/2,'remote tie boundary')
check((53*x/9)-(17*x/9+y/2)==(8*x-y)/2,'branch competition boundary')
check((f-(10*y)/9)*Q(-9,8)==x,'Z full-coordinate inverse')
check((8*x)/8==x,'N inverse')

# Encoded rectangles cover every natural counter value; endpoints here include
# unattained limiting values and so establish stronger closed-box inequalities.
def box(lo,hi):
    vertices=list(product([Q(1)],[Q(lo),Q(hi)],[Q(17,20),Q(19,20)]))
    def strict(expr,why,allow_negative=False):
        vals=[expr.at(*v) for v in vertices]
        sign=1 if min(vals)>0 else -1 if max(vals)<0 else 0
        check(sign==1 or (allow_negative and sign==-1),why+' lacks strict box sign')
        return sign
    return strict

for branch,lo,hi,guards in [
    ('Z',Q(3,20),Q(3,20),[x,y-4*x,8*x-y,D-y]),
    ('N',Q(1,20),Q(1,10),[x,y-8*x,D-y])]:
    bound=box(lo,hi)
    for guard in guards: bound(guard,'uniform '+branch)
    elapsed=2*({'Z':zword,'N':nword}[branch][-1][0])
    bound(elapsed-D,'test longer than D'); bound(4*D-elapsed,'test shorter than 4D')

# All update event tables are newly assembled from the two stated primitives.
# Collisions use fresh labels. Base stationary labels remain globally fixed.
next_id=0

def fresh(speed):
    global next_id
    next_id+=1; name='u'+str(next_id); SPEEDS[name]=Q(speed); return name

def scale_rows(t,k):
    h=(k-1)/(k+1); marker=fresh(h)
    qs=[fresh(v) for v in [1,-1,1,-1,1]]
    data=[row(O,O,t,qs[0],'X'),row(t,t,t,qs[1],marker),
          row(2*t,O,t+h*t,qs[2],marker),
          row((2+k)*t,k*t,k*t,qs[3],'X'),
          row((2+2*k)*t,O,k*t,qs[4],'X')]
    for ins,outs in [((qs[0],'X'),(qs[1],marker)),((qs[1],'L'),(qs[2],'L')),
                     ((qs[2],marker),(qs[3],'X')),((qs[3],'L'),(qs[4],'L'))]: rule(ins,outs)
    check(t+h*(t+k*t)==k*t,'general scale target identity')
    return data

def translation_rows(t,e):
    u=t/(1-e); target=t+e*D; h=e/(2-e)
    first=scale_rows(t,1/(1-e)); alpha=first[-1][0]
    marker=fresh(h)
    qs=[first[-1][2][1]]+[fresh(v) for v in [1,1,-1,-1,-1,1]]
    # Rows include target's position at all actual spectator/reflector contacts.
    second=[row(alpha+u,u,u,qs[1],marker),
            row(alpha+y,y,u+h*(y-u),qs[2],marker),
            row(alpha+D,D,u+h*(D-u),qs[3],marker),
            row(alpha+2*D-y,y,u+h*(2*D-y-u),qs[4],marker),
            row(alpha+2*D-target,target,target,qs[5],'X'),
            row(alpha+2*D,O,target,qs[6],'X')]
    for ins,outs in [((qs[0],'X'),(qs[1],marker)),((qs[1],'Y'),(qs[2],'Y')),
                     ((qs[2],'R'),(qs[3],'R')),((qs[3],'Y'),(qs[4],'Y')),
                     ((qs[4],marker),(qs[5],'X')),((qs[5],'L'),(qs[6],'L'))]: rule(ins,outs)
    check(u+h*(2*D-target-u)==target,'translation restoration identity')
    check(u-t==e*t/(1-e),'hidden endpoint first difference')
    check(target-u==e*(D-target)/(1-e),'hidden endpoint second difference')
    return first+second

RESULT['updates']={}
UPDATE_TEMPLATES={}
ALL_UPDATE_ROWS=[]
for name,k,e,lo,hi,durcoef in [
    ('increment',Q(1,2),Q(1,40),Q(1,20),Q(3,20),Q(196,39)),
    ('positive_decrement',Q(2),Q(-1,20),Q(1,20),Q(1,10),Q(290,21))]:
    before=set(RULES)
    scale=scale_rows(x,k); translation=translation_rows(k*x,e); bound=box(lo,hi)
    ALL_UPDATE_ROWS.extend([scale,translation])
    # The outgoing label at the existing scale terminal bounce is identified
    # with the translation entry. There is no extra zero-time collision.
    rename={scale[-1][2][1]:translation[0][2][1]}
    update_rules={frozenset(rename.get(z,z) for z in ins):frozenset(rename.get(z,z) for z in outs)
                  for ins,outs in RULES.items() if ins not in before}
    UPDATE_TEMPLATES[name]=(update_rules,scale[0][2][1],translation[-1][2][1])
    a=audit_rows(name+' scale',scale,bound)
    b=audit_rows(name+' translation',translation,bound)
    total=scale[-1][0]+translation[-1][0]
    check(total==2*D+durcoef*x,'update duration')
    bound(total-2*D,'update duration lower'); bound(4*D-total,'update duration upper')
    check(translation[-1][1]==[O,O,k*x+e*D,y,D],'update full marker restoration')
    # q=2^-n is an independent formal variable in the encoding identities.
    original=D/20+x/10
    next_encoding=D/20+(x/2 if k==Q(1,2) else 2*x)/10
    check(k*original+e*D==next_encoding,'all-n direct counter update identity')
    RESULT['updates'][name]={'scale':a,'translation':b,'events':len(a)+len(b),
                             'duration':total.serial(),'endpoint':(k*x+e*D).serial()}

# Reflection is an involution. For each declared row and rule it preserves
# contact incidence and negates velocities, hence also every positive duration.
reflect=lambda a: a.subst(D,D-y,D-x)
check(reflect(reflect(x))==x and reflect(reflect(y))==y,'reflection involution')
for rows in [zword,nword]+ALL_UPDATE_ROWS:
    for left,right in zip(rows,rows[1:]):
        dt=right[0]-left[0]
        for old,new,label in zip(left[1],right[1],left[2]):
            check((D-new)-(D-old)==-SPEEDS[label]*dt,'physical reflection line identity')

# Transfers list every marker crossing and end with the real far-anchor bounce.
TRANSFER_TEMPLATES={}
RESULT['transfers']={}
for direction in ['right','left']:
    qs=[fresh(v) for v in ([1,1,1,-1] if direction=='right' else [-1,-1,-1,1])]
    if direction=='right':
        data=[row(O,O,x,qs[0],'X'),row(x,x,x,qs[1],'X'),
              row(y,y,x,qs[2],'X'),row(D,D,x,qs[3],'X')]
        partners=['X','Y','R']
    else:
        data=[row(O,D,x,qs[0],'X'),row(D-y,y,x,qs[1],'X'),
              row(D-x,x,x,qs[2],'X'),row(D,O,x,qs[3],'X')]
        partners=['Y','X','L']
    before=set(RULES)
    for i,partner in enumerate(partners): rule((qs[i],partner),(qs[i+1],partner))
    TRANSFER_TEMPLATES[direction]=({ins:outs for ins,outs in RULES.items() if ins not in before},qs[0],qs[-1])
    RESULT['transfers'][direction]=audit_rows('transfer '+direction,data,box(Q(1,20),Q(3,20)))
    check(data[-1][0]==D,'exact transfer duration')

# Static finite-table assembly for one representative finite control graph.
# This checks namespace separation, real-anchor interfaces, reflection and HALT.
# It never executes this graph. The general arbitrary-program argument is in
# the accompanying audit: each instruction's internal namespace is disjoint.
COMP={}; COMPSPEED={z:Q(0) for z in ['L','X','Y','R']}
for i in ['IA','IB','CA','CB','H']: COMPSPEED['Q_'+i]=Q(1)

def install(template,tag,entry,exits,reflected=False):
    rules,local_entry,local_exits=template
    rename={z:z for z in ['L','X','Y','R']}
    if reflected: rename.update({'L':'R','R':'L','X':'Y','Y':'X'})
    labels=set().union(*(ins|outs for ins,outs in rules.items()))
    for z in labels-set(rename): rename[z]=tag+'_'+z
    rename[local_entry]=entry
    for old,new in zip(local_exits,exits): rename[old]=new
    for z in labels:
        name=rename[z]; speed=(-1 if reflected else 1)*SPEEDS[z]
        check(name not in COMPSPEED or COMPSPEED[name]==speed,'compiled phase speed consistency')
        COMPSPEED[name]=speed
    for ins,outs in rules.items():
        a=frozenset(rename[z] for z in ins); b=frozenset(rename[z] for z in outs)
        check(a not in COMP or COMP[a]==b,'compiled input determinism')
        check(len(a)==len(b)==2,'compiled population preservation')
        check(len({COMPSPEED[z] for z in a})==len({COMPSPEED[z] for z in b})==2,
              'compiled incoming and outgoing distinct speeds')
        COMP[a]=b

def upd(kind):
    rules,ent,out=UPDATE_TEMPLATES[kind]; return rules,ent,[out]
def tra(direction):
    rules,ent,out=TRANSFER_TEMPLATES[direction]; return rules,ent,[out]
test=(TEST_RULES,'q0',['outZ','outN'])
install(upd('increment'),'IA','Q_IA',['Q_IB'])
install(tra('right'),'IB_to','Q_IB',['IB_at_R'])
install(upd('increment'),'IB_update','IB_at_R',['IB_return'],True)
install(tra('left'),'IB_from','IB_return',['Q_CA'])
install(test,'CA_test','Q_CA',['Q_H','CA_decrement'])
install(upd('positive_decrement'),'CA_dec','CA_decrement',['Q_CB'])
install(tra('right'),'CB_to','Q_CB',['CB_at_R'])
install(test,'CB_test','CB_at_R',['CB_zero_return','CB_decrement'],True)
install(upd('positive_decrement'),'CB_dec','CB_decrement',['CB_positive_return'],True)
install(tra('left'),'CB_zero_from','CB_zero_return',['Q_IA'])
install(tra('left'),'CB_pos_from','CB_positive_return',['Q_CB'])
for marker in ['X','Y','R']:
    key=frozenset(['Q_H',marker]);check(key not in COMP,'HALT input freshness');COMP[key]=key

# Counts are derived from audited block lengths, not entered as 32 by fiat.
nz=RESULT['test_words']['Z']['total_events'];nn=RESULT['test_words']['N']['total_events']
nu=RESULT['updates']['increment']['events'];nd=RESULT['updates']['positive_decrement']['events']
nt=len(RESULT['transfers']['right'])+len(RESULT['transfers']['left'])
counts={'INC_A':nu,'INC_B':nt+nu,'COND_A_zero':nz,'COND_A_positive':nn+nd,
        'COND_B_zero':nt+nz,'COND_B_positive':nt+nn+nd}
check(max(counts.values())==32,'32-event instruction bound')
full_speeds={Q(0)}|{sgn*v for sgn in [-1,1] for v in
    [Q(1),Q(1,3),Q(1,79),Q(1,41),Q(3,2),Q(1,4),Q(4),Q(1,2),Q(2)]}
check(len(full_speeds)==19,'19 distinct speeds')
check(set(SPEEDS.values())|set(COMPSPEED.values())<=full_speeds,'all actual labels use fixed speed set')
RESULT['counts']=counts
RESULT['speed_set']=list(map(str,sorted(full_speeds)))
RESULT['explicit_local_rules_checked']=len(RULES)
RESULT['compiled_syntax']={'explicit_rules':len(COMP),'labels':len(COMPSPEED),
    'instruction_graph':'IA increments A to IB; IB increments B to CA; CA branches zero to H, otherwise decrements A to CB; CB branches zero to IA, otherwise decrements B to CB; H escapes',
    'execution_performed':False,
    'rules':[{'input':sorted(a),'output':sorted(b)} for a,b in sorted(COMP.items(),key=lambda r:sorted(r[0]))]}
RESULT['timing_note']='D<T<10D follows from strict test (D,4D), update (2D,4D), and D transfers; no accumulation since fixed D>0'


def read_source(path):
    flags=os.O_RDONLY
    # Refuse silent fallback when preserving source access times is unavailable.
    if not hasattr(os,'O_NOATIME'):
        raise RuntimeError('O_NOATIME unavailable; run on an expendable copied packet, then adjust this reader explicitly')
    fd=os.open(path,flags|os.O_NOATIME)
    with os.fdopen(fd,'rb') as f: return f.read()

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('packet',type=Path)
    args=parser.parse_args()
    stamps={}
    for name,digest in PINS.items():
        p=args.packet/name; st=p.stat()
        stamps[name]=(st.st_mode,st.st_size,st.st_atime_ns,st.st_mtime_ns,st.st_ctime_ns)
        check(hashlib.sha256(read_source(p)).hexdigest()==digest,'source hash '+name)
    manifest=json.loads(read_source(args.packet/'MANIFEST.json'))
    check(manifest['files']=={k:v for k,v in PINS.items() if k!='MANIFEST.json'},'manifest binding')
    for name,old in stamps.items():
        st=(args.packet/name).stat()
        check(old==(st.st_mode,st.st_size,st.st_atime_ns,st.st_mtime_ns,st.st_ctime_ns),
              'source metadata changed '+name)
    RESULT['source_sha256']=PINS
    RESULT['source_mode_size_atime_mtime_ctime_unchanged']=True
    RESULT['assertions_passed']=NASSERT
    RESULT['audit_checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    print(json.dumps(RESULT,indent=2))

if __name__=='__main__': main()
