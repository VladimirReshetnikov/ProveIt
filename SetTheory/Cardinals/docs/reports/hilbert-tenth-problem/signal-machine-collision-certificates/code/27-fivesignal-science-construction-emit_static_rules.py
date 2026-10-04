"""Static finite grammar expansion ONLY.
Emits symbolic collision rules; does not evaluate any position, flight time,
trajectory, event search, stored schedule, or external program.
"""
import json
from fractions import Fraction as F
from pathlib import Path
ROOT=Path('/workspace/shared/signal-map-obstruction-20261004')
events=[]
meta={name+'0':'0' for name in ('L','X','Y','D')}
primitive_id=0

def rational(q):
    q=F(q)
    return str(q.numerator) if q.denominator==1 else f'{q.numerator}/{q.denominator}'

def event(marker_in,marker_out,q_in,q_out,description,primitive):
    events.append({'marker_in':marker_in,'marker_out':marker_out,
                   'messenger_in_speed':rational(q_in),'messenger_out_speed':rational(q_out),
                   'description':description,'primitive':primitive})

def cross(marker,direction,primitive):
    event(marker+'0',marker+'0',direction,direction,'transparent crossing of '+marker,primitive)

def bounce(marker,incoming,outgoing,primitive):
    event(marker+'0',marker+'0',incoming,outgoing,'reflection at '+marker,primitive)

def scaling(target,inner,u,orientation=1,anchor='L'):
    global primitive_id
    primitive_id+=1
    pid=f'L{primitive_id:02d}'
    o=F(orientation)
    a=o*(u-1)/(u+1)
    moving=f'{target}_{pid}'
    meta[moving]=rational(a)
    for marker in inner: cross(marker,o,pid)
    event(target+'0',moving,o,-o,'launch moving target '+target,pid)
    for marker in reversed(inner):cross(marker,-o,pid)
    bounce(anchor,-o,o,pid)
    for marker in inner:cross(marker,o,pid)
    event(moving,target+'0',o,-o,'restore target '+target,pid)
    for marker in reversed(inner):cross(marker,-o,pid)
    bounce(anchor,-o,o,pid)

def homothety(target,reflector,between,v,orientation=1,anchor='L'):
    global primitive_id
    primitive_id+=1
    pid=f'H{primitive_id:02d}'
    o=F(orientation)
    a=o*(1-v)/(1+v)
    moving=f'{target}_{pid}'
    meta[moving]=rational(a)
    event(target+'0',moving,o,o,'launch moving target '+target,pid)
    for marker in between:cross(marker,o,pid)
    bounce(reflector,o,-o,pid)
    for marker in reversed(between):cross(marker,-o,pid)
    event(moving,target+'0',-o,-o,'restore target '+target,pid)
    bounce(anchor,-o,o,pid)

def translation(target,reflector,between,c,orientation=1,anchor='L'):
    scaling(target,[],1/(1-c),orientation,anchor)
    homothety(target,reflector,between,1-c,orientation,anchor)

def upper_shear():
    for _ in range(2):
        translation('X','Y',[],F(-1,4))
        translation('X','D',['Y'],F(1,6))

upper_shear()
cross('X',1,'transfer_right');cross('Y',1,'transfer_right');bounce('D',1,-1,'transfer_right')
for _ in range(2):
    translation('Y','X',[],F(2,5),-1,'D')
    translation('Y','L',['X'],F(-4,15),-1,'D')
cross('Y',-1,'transfer_left');cross('X',-1,'transfer_left');bounce('L',-1,1,'transfer_left')
upper_shear()
rotation_count=len(events)
scaling('X',[],F(1,2))
scaling('Y',['X'],F(1,2))
scaling('D',['X','Y'],F(1,2))
assert rotation_count==114 and len(events)==138 and primitive_id==27
m=len(events)
for j,e in enumerate(events):
    meta[f'Q{j}']=e['messenger_in_speed']
    assert e['messenger_out_speed']==events[(j+1)%m]['messenger_in_speed']
for j,e in enumerate(events):
    e['index']=j
    e['input']=[f'Q{j}',e['marker_in']]
    e['output']=[f'Q{(j+1)%m}',e['marker_out']]
    assert len(set(meta[z] for z in e['input']))==2
    assert len(set(meta[z] for z in e['output']))==2
assert events[-1]['output']==['Q0','L0']
assert meta['Q0']=='1'
assert set(meta.values())=={'0','1','-1','-1/9','1/11','-1/4','2/17','-1/3'}
artifact={
 'description':'Static finite rule table for the five-live-signal rotation-plus-contraction construction',
 'warning':'Inert construction data. No physical schedule or trajectory was executed.',
 'live_population':5,'explicit_rule_count':m,'meta_signal_count':len(meta),
 'rotation_rule_count':rotation_count,
 'meta_signals':[{'name':name,'speed':speed} for name,speed in meta.items()],
 'initial_section':{'labels':['L0','Q0','X0','Y0','D0'],'positions':['0','0','x','y','d'],
                    'domain':'0 < x < y < d'},
 'explicit_rules':events,
 'default_rule':'For every other incoming meta-signal set S of cardinality at least two with pairwise distinct speeds, use S -> S.',
 'gap_return_matrix':[['7/30','-1/15','1/3'],['7/15','11/30','-1/3'],['-1/5','1/5','1/2']],
 'essential_guards_file':'GUARDS.txt',
 'convention':'Rules are unordered input/output sets; event order is the listed fixed proposed complete binary collision word.'
}
(ROOT/'RULES.json').write_text(json.dumps(artifact,indent=2)+'\n')
print(json.dumps({'rules':m,'meta_signals':len(meta),'primitives':primitive_id,'rotation_rules':rotation_count,'speeds':sorted(set(meta.values()))}))
