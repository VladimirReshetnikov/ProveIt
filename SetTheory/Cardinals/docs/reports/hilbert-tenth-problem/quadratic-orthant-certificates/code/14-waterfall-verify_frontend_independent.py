"""Independent 46-clock audit. No import from the original verifier.

Loop guards are proved by nonnegative-cone reparameterization, not by sampling
or by evaluating the original verifier's endpoint conditions. For a loop index
j<Q, write Q=j+1+u. For j<Y use Y=j+1+u. For j<2Y split
j=2v+e, e in {0,1}, Y=v+1+u. All free variables are natural numbers.
"""
from pathlib import Path
from itertools import product
import hashlib,json

ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'receipts'

def check(b,*message):
    if not b: raise AssertionError(message)

def add(a,b): return tuple(x+y for x,y in zip(a,b))
def sub(a,b): return tuple(x-y for x,y in zip(a,b))
def scale(a,b): return tuple(x*b for x in a)
def const(x): return (x,0,0)
def value(a,q,y): return a[0]+a[1]*q+a[2]*y

# Hand-transcribed from the rendered Table16, p.121, primary paper.
# Column order here is u1,...,u15, with separate c and b rows.
C='cR2 bR3 cL7 cL6 bR1 bL4 cL8 bL9 cR1 bL11 cR12 cR13 cL2 cL3 cR14'.split()
B='bR1 bR1 cL5 bL5 bL4 bL4 bL7 bL7 bL10 --- bR14 bR12 bR12 cR15 bR14'.split()
TABLE={}
for q in range(15):
    for s,row in enumerate([C,B]):
        z=row[q]
        TABLE[q,s]=None if z=='---' else (int(z[0]=='b'),z[1],int(z[2:])-1)

names=['LeftTape','LeftTemp','LeftTrans','LeftDiv0','LeftDiv1','LeftMult','LeftWrite0','LeftWrite1']
names += ['Trans'+chr(q+65)+str(s) for q in range(15) for s in range(2)]
names += ['RightWrite0','RightWrite1','RightMult','RightDiv0','RightDiv1','RightTrans','RightTemp','RightTape']
I={n:i for i,n in enumerate(names)}
H=I['TransJ1']
raw=(ROOT/'source/UniversalTM15x2.twm.txt').read_bytes()
full=json.loads(raw)
check(len(full)==47 and all(len(row)==47 for row in full),'shape')
check(full[0]==[47]+[46]*46,'format header')
M=[row[1:] for row in full[1:]]  # source-trigger rows
check(all(type(x)==int and x>=0 for row in M for x in row),'natural matrix')
check([i for i,row in enumerate(M) if not any(row)]==[H],'halt row')
check(all(M[i][i]>0 for i in range(46) if i!=H),'positive resets')
check(max(map(max,M))==12,'entry bound')
creator=(ROOT/'source/UniversalTM15x2.tm.txt').read_text().splitlines()[0].split('_')
for (q,s),rule in TABLE.items():
    z='---' if rule is None else str(rule[0])+rule[1]+chr(65+rule[2])
    check(creator[q][3*s:3*s+3]==z,'primary table',q,s,z)

def state(q,s,l,r):
    d=[const(2) for _ in range(46)]
    d[I['LeftTape']]=add(const(2),scale(l,2))
    d[I['RightTape']]=add(const(2),scale(r,2))
    for side in ['Left','Right']:
        for a in range(2): d[I[side+'Div'+str(a)]]=const(2+int(a!=s))
    for z in range(15):
        for a in range(2): d[I['Trans'+chr(65+z)+str(a)]]=const(1+int(z!=q)+int(a!=s))
    return d

check([row[0] for row in full[1:]]==[a[0] for a in state(0,0,const(0),const(0))],'initial vector')

def blocks(q,s,r):
    w,d,qp=TABLE[q,s]
    D,O=('Left','Right') if d=='L' else ('Right','Left')
    b=[(['Trans'+chr(65+q)+str(s)],'one'),([D+'Div0',D+'Div1'],'q')]
    if r: b += [([D+'Div0'],'one')]
    b += [([D+'Tape'],'one'),([D+'Trans'],'q'),([D+'Temp'],'one'),([O+'Mult'],'y'),
          ([O+'Tape'],'one'),([O+'Trans'],'2y'),([O+'Temp'],'one'),([O+'Write'+str(w)],'one')]
    return [([I[z] for z in word],kind) for word,kind in b]

# With gap=c+aQ+bY+d*j, return coefficients on an exact union of
# nonnegative orthants parameterizing every active iteration.
def cones(gap,step,kind):
    c,a,b=gap
    if kind=='one': return [(c,a,b)]
    if kind=='q': return [(c+a,a+step,a,b)] # j,u,Y
    if kind=='y': return [(c+b,a,b+step,b)] # Q,j,u
    if kind=='2y': return [(c+b+e*step,a,b+2*step,b) for e in [0,1]] # Q,v,u
    raise ValueError(kind)

multiplicity={'one':const(1),'q':(0,1,0),'y':(0,0,1),'2y':(0,0,2)}
guards=0;cone_count=0;records=[]
for (q,s),rule in TABLE.items():
    if rule is None: continue
    w,d,qp=rule
    for r in [0,1]:
        x=(r,2,0);y=(0,0,1)
        l,rr=(x,y) if d=='L' else (y,x)
        deadlines=state(q,s,l,rr)
        count=const(0)
        for word,kind in blocks(q,s,r):
            delta=[sum(M[i][j] for i in word) for j in range(46)]
            prefix=[0]*46
            for i in word:
                for j in range(46):
                    if i==j: continue
                    gap=add(sub(deadlines[j],deadlines[i]),const(prefix[j]-prefix[i]))
                    step=delta[j]-delta[i]
                    for coefficients in cones(gap,step,kind):
                        check(coefficients[0]>=1 and all(v>=0 for v in coefficients[1:]),
                              'strict guard',q,s,r,names[i],names[j],kind,gap,step,coefficients)
                        cone_count+=1
                    guards+=1
                prefix=[p+v for p,v in zip(prefix,M[i])]
            k=multiplicity[kind]
            deadlines=[add(a,scale(k,b)) for a,b in zip(deadlines,delta)]
            count=add(count,scale(k,len(word)))
        newl,newr=((0,1,0),(w,0,2)) if d=='L' else ((w,0,2),(0,1,0))
        target=state(qp,r,newl,newr)
        shifts=[sub(a,b) for a,b in zip(deadlines,target)]
        check(len(set(shifts))==1,'uniform canonical shift',q,s,r)
        check(shifts[0]==(19+2*r,6,6),'time coefficient',q,s,r)
        check(count==(6+r,3,3),'event coefficient',q,s,r)
        check(shifts[0]==add(scale(count,2),const(7)),'time-event identity')
        records.append({'q':q,'s':s,'r':r,'delta':shifts[0],'events':count})
check(len(records)==58,'macro cases')

# Independent concrete event engine: actual physical residual countdown and
# deadline engine run side by side; neither chooses its event from the macro.
cases=0;events=0;first_trace=[]
for (q,s),rule in TABLE.items():
    if rule is None: continue
    w,d,qp=rule
    for r,Q,Y in product(range(2),range(7),range(7)):
        X=2*Q+r
        L,R=(X,Y) if d=='L' else (Y,X)
        a=[z[0] for z in state(q,s,const(L),const(R))]
        deadlines=a[:];physical=a[:];time=0
        expected=[i for word,kind in blocks(q,s,r) for k in range(value(multiplicity[kind],Q,Y)) for i in word]
        trace=[]
        for wanted in expected:
            t=min(deadlines);ids=[i for i,v in enumerate(deadlines) if v==t]
            dt=min(physical);ids2=[i for i,v in enumerate(physical) if v==dt]
            check(ids==ids2==[wanted],'event mismatch',q,s,r,Q,Y,ids,ids2,wanted)
            i=ids[0];check(i!=H,'premature halt')
            time+=dt;check(time==t,'timestamp mismatch')
            trace.append([names[i],t])
            physical=[v-dt+M[i][j] for j,v in enumerate(physical)]
            deadlines=[v+M[i][j] for j,v in enumerate(deadlines)]
            check(all(v>0 for v in physical),'positive after firing')
            check(deadlines==[v+time for v in physical],'physical/deadline relation')
            events+=1
        newL,newR=(Q,2*Y+w) if d=='L' else (2*Y+w,Q)
        target=[z[0] for z in state(qp,r,const(newL),const(newR))]
        shift=19+6*Q+2*r+6*Y
        check(deadlines==[v+shift for v in target],'canonical concrete endpoint')
        check(min(deadlines)==1+shift,'next transition time')
        check([i for i,v in enumerate(deadlines) if v==min(deadlines)]==[I['Trans'+chr(65+qp)+str(r)]],'next transition identity')
        cases+=1
        if (q,s,r,Q,Y)==(0,0,0,0,0): first_trace=trace+[ ['NEXT:'+names[I['TransB0']],min(deadlines)] ]
# The actual halt clock is the unique selected event in every canonical J1 state.
for L,R in [(0,0),(3,8),(10**100,10**80)]:
    a=[z[0] for z in state(9,1,const(L),const(R))]
    check([i for i,v in enumerate(a) if v==min(a)]==[H],'canonical halt')

# Independent signed conservation potential; this is an identity, not a
# nonnegative ranking function. Tape weights vanish, so arbitrary L,R are covered.
weights=[]
for n in names:
    if n in ['LeftTrans','RightTrans']: weights.append(288)
    elif 'Div' in n: weights.append(-373)
    elif n in ['LeftMult','RightMult']: weights.append(970)
    elif 'Write' in n: weights.append(-4)
    else: weights.append(0)
check(sum(weights)==1008,'potential total')
for q,s in product(range(15),range(2)):
    d=state(q,s,(0,1,0),(0,0,1))
    z=const(0)
    for wi,di in zip(weights,d): z=add(z,scale(di,wi))
    check(z==const(1270),'canonical potential',q,s,z)
for i,row in enumerate(M):
    if i==H: continue
    dot=sum(w*x for w,x in zip(weights,row))
    check(dot==2016+7056*int(names[i].startswith('Trans')),'trigger potential',i,dot)

receipt={'status':'PASS','clocks':46,'source_sha256':hashlib.sha256(raw).hexdigest(),
 'source_orientation':'M[source][destination]','primary_table_match':True,
 'source_table_corrections':{'u15_b':'bRu14 (also Table19)','halt':'u10,b; author PDF page19 final prose c is inconsistent with Table16 and its displayed head'},
 'unbounded_symbolic_macros':len(records),'symbolic_guards':guards,'nonnegative_cone_checks':cone_count,
 'symbolic_method':'Exact loop-index reparameterization into natural orthants; 2Y loop split into even/odd indices',
 'concrete_macro_cases':cases,'concrete_nonhalt_events':events,'concrete_domain':'All 29 rules; residues0,1; Q,Y in0..6',
 'timing':'delta=2*events+7 between selected transition deadlines; not time spent through last Write firing',
 'potential':{'weight_sum':1008,'canonical_dot':1270,'nontransition_row_dot':2016,'transition_row_dot':9072,'identity':'1008*delta=2016*C+7056*k'},
 'zero_input_first_macro':first_trace,'halt_clock_one_based':H+1,'records':records,
 'scope':'Independent arithmetic audit and finite concrete replay; not a proof-assistant kernel check and not a fixed-arity universal polynomial'}
(OUT/'independent-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:v for k,v in receipt.items() if k!='records'},indent=2))
