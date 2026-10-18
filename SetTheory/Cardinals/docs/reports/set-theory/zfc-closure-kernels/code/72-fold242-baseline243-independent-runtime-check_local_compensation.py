"""Independent, standard-library-only audit. Candidate files are read as data.
Finite formulas and exact bounded blocks establish arbitrary-tape induction.
No supplied Python/Lean code is executed or imported.
"""
import hashlib,itertools,json,sys
from pathlib import Path
if not __debug__ or sys.flags.optimize: raise RuntimeError('Enabled assertions required')
ROOT=Path(__file__).resolve().parent.parent
PACK=ROOT/'sources'
def table(path):
    out={}
    for s in path.read_text().splitlines():
        if not s or s.startswith('#'):continue
        q,b,w,d,t=s.split();q,b,w,t=map(int,(q,b,w,t))
        assert (q,b) not in out and b in (0,1) and w in (0,1) and d in ('L','R')
        out[q,b]=(w,1 if d=='R' else -1,t)
    states={q for q,b in out}
    assert len(out)==2*len(states) and all((q,b) in out for q in states for b in (0,1))
    assert {x[2] for x in out.values()}-states=={254}
    return out
op=PACK/'candidate-rotation244__zfc_rotation244_old.tm';np=PACK/'candidate-combined243__zfc_combined243_old.tm'
old,new=table(op),table(np)
assert len(old)==488 and len(new)==486
removed=sorted(set(old)-set(new));changed={k:(old[k],new[k]) for k in old.keys()&new.keys() if old[k]!=new[k]}
assert removed==[(122,0),(122,1)]
assert changed=={(92,1):((1,-1,24),(1,1,66)),(104,1):((1,1,122),(1,1,92)),(106,1):((1,1,122),(1,1,92)),(167,1):((1,-1,92),(1,-1,151))}

def invariant(q,h,tape):
    if q in (68,122,167):return tape[h-1]==1
    if q==81:return tape[h-1]==0 or tape[h-2]==1
    return True
# Coordinates include everything either pre- or post-invariant can inspect.
coords=range(-3,2); implications=0;excluded_antecedents=0
for (q,b),(w,d,t) in old.items():
    for bits in itertools.product((0,1),repeat=5):
        tape=dict(zip(coords,bits))
        if tape[0]!=b or not invariant(q,0,tape):continue
        nxt=tape.copy();nxt[0]=w
        assert invariant(t,d,nxt),(q,b,tape,w,d,t)
        implications+=1
for bits in itertools.product((0,1),repeat=5):assert invariant(95,0,dict(zip(coords,bits)))
# Verify inventory from actual parsed table, rather than trusting named predecessors.
incoming={t:sorted([q,b,w,d] for (q,b),(w,d,n) in old.items() if n==t) for t in (68,81,92,122,167)}
assert incoming[68]==[[52,1,1,1],[123,1,1,1]]
assert incoming[81]==[[68,1,1,1],[123,0,0,1]]
assert incoming[92]==[[81,1,1,-1],[167,1,1,-1]]
assert incoming[122]==[[104,1,1,1],[106,1,1,1]]
assert incoming[167]==[[145,1,1,1],[148,1,1,1]]
excluded={92,122};exceptional={(104,1),(106,1),(167,1),(81,1)}
ordinary=[]
for key,row in old.items():
    if key[0] in excluded or key in exceptional:continue
    assert new[key]==row and row[2] not in excluded
    ordinary.append(key)
assert len(ordinary)==480

def block(tab,q,known,n):
    h=0;tape=known.copy();trace=[];seen=set()
    for i in range(n):
        assert h in tape,('Read outside finite known window',q,h)
        assert q!=254
        b=tape[h];w,d,t=tab[q,b]
        trace.append({'q':q,'h':h,'read':b,'write':w,'move':d,'target':t})
        seen.add((q,b));tape[h]=w;h+=d;q=t
    assert q not in excluded and q!=254
    return (q,h,tape),trace,seen
specs=[]
for q in (104,106):
    for b in (0,1):specs.append((q,{0:1,1:b},2,4 if b==0 else 2,25 if b==0 else 66,2,{0:1,1:b}))
specs.extend([(167,{-1:1,0:1},2,2,24,-2,{-1:1,0:1}),(81,{-1:0,0:1},2,2,107,-2,{-1:0,0:1}),(81,{-2:1,-1:1,0:1},6,4,2,-2,{-2:1,-1:0,0:0})])
macros=[];oldrows=set(ordinary);newrows=set(ordinary)
for q,known,a,b,endq,endh,expected in specs:
    lhs,lt,lr=block(old,q,known,a);rhs,rt,rr=block(new,q,known,b)
    assert lhs==rhs==(endq,endh,expected)
    # Every local block has positive time with the claimed clock ratios.
    assert 1<=a<=6 and 1<=b<=4 and 2*a<=3*b and b<=2*a
    oldrows.update(lr);newrows.update(rr)
    macros.append({'entry':q,'input':known,'old_steps':a,'new_steps':b,'endpoint':lhs,'old_trace':lt,'new_trace':rt})
assert oldrows==set(old) and newrows==set(new)
# The guard split is exhaustive under I for each exceptional entry.
for q,b in exceptional:
    for bits in itertools.product((0,1),repeat=5):
        tape=dict(zip(coords,bits))
        if tape[0]!=b or not invariant(q,0,tape):continue
        matches=[s for s in specs if s[0]==q and all(tape[h]==v for h,v in s[1].items())]
        assert len(matches)==1
result={'status':'INDEPENDENT_ALL_TAPE_STUTTERING_PASS','table_old_sha256':hashlib.sha256(op.read_bytes()).hexdigest(),'table_new_sha256':hashlib.sha256(np.read_bytes()).hexdigest(),'checker_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'invariant_boolean_implications':implications,'incoming_inventory':incoming,'ordinary_rows':len(ordinary),'old_total_rows_covered':len(oldrows),'new_total_rows_covered':len(newrows),'guard_cover_exhaustive':True,'macros':macros,'scope':'All binary tapes (including infinite support), all integer head positions, from state95. More generally any common checkpoint state satisfying the old invariant. No register bounds, gap bounds, source assumptions, finite execution fuel, or tape bounds.','clock':'Ordinary blocks 1:1; exceptional old/new 2:4, 2:2 or 6:4. Thus (2/3)t_old <= t_new <= 2t_old at every paired endpoint.','proof':'The old invariant is initially true and closed under every transition. Each ordinary row or unique exceptional guarded macro has identical endpoint state, head and entire tape. Induction couples all paired configurations. Blocks have positive bounded lengths and exceptional blocks cannot hit halt, so neither infinite run can be matched by finite time on the other side; halting is equivalent.','limitation':'Independent executable ordinary mathematical proof, not a Lean/Rocq kernel endpoint. Consistency interpretation is inherited from baseline and is not established by this local reduction alone.'}
(ROOT/'independent-runtime/local_compensation.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ('macros','incoming_inventory')},indent=2))
