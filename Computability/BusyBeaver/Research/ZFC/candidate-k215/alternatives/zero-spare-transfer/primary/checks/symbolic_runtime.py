"""Self-authored universal mathematical checker of literal binary TM tables.

Only Python standard library plus our independent_runtime helper is executed.
Downloaded code is not imported or executed. Supplied tables/AST/JSON are data.
Sound rules: literal steps; induction over a natural unary length when a row
is a self-loop in the scan direction; structural induction over a finite list
of blocks after independently proving its one-block schema on the actual table.
This is executable mathematical evidence, not a proof-assistant kernel check.
"""
from pathlib import Path
import json,hashlib,time,argparse,os,sys
if not __debug__ or sys.flags.optimize:
    raise RuntimeError("Universal checking requires enabled assertions; disable -O and PYTHONOPTIMIZE.")
import independent_runtime as r

# Thirteen affine slots: constant, gap, nine independent primary values,
# first-spare value, and remaining spare-list width. The separate generic
# one-block proof reuses slot 2 for its arbitrary natural block value.
NV=13
ZERO=(0,)*NV

def num(n):return (n,)+(0,)*(NV-1)
def var(i):return tuple(int(j==i) for j in range(NV))
def add(a,b):return tuple(x+y for x,y in zip(a,b))
def neg(a):return tuple(-x for x in a)
def minus1(a):return (a[0]-1,)+a[1:]
def nonnegative(a):return all(x>=0 for x in a)
def run(bit,n):return ('run',bit,n if isinstance(n,tuple) else num(n))
def bit(b):return run(b,1)
def block(value,family='B'):
    # B(v)=0 1^(v+1), C(v)=1 0 1^v.
    return [bit(0),run(1,add(value,num(1)))] if family=='B' else [bit(1),bit(0),run(1,value)]
def tail(family='B',reverse=False):return ('list',family,'spare_tail',reverse)
BLANK=('blank',)
def rev(atoms):
    return [a if a[0]!='list' else (a[0],a[1],a[2],not a[3]) for a in reversed(atoms)]

def normal(atoms):
    out=[]
    for a in atoms:
        if a[0]=='run':
            assert a[1] in (0,1) and nonnegative(a[2]),('negative run',a)
            if a[2]==ZERO:continue
            if out and out[-1][0]=='run' and out[-1][1]==a[1]:
                a=run(a[1],add(out.pop()[2],a[2]))
        out.append(a)
    # An infinite zero exterior absorbs any finite adjacent zero run.
    if len(out)>1 and out[-1]==BLANK and out[-2][0]=='run' and out[-2][1]==0:out.pop(-2)
    # Finite-list word identity, proved by base/cons algebra independently below:
    # C(A) 1 = 1 B(A), and its reversal 1 rev(C(A)) = rev(B(A)) 1.
    for i in range(len(out)-1):
        a,b=out[i:i+2]
        if a[:2]==('list','C') and not a[3] and b[:2]==('run',1) and b[2][0]>=1:
            return normal(out[:i]+[bit(1),('list','B',a[2],False),run(1,minus1(b[2]))]+out[i+2:])
        if a[:2]==('run',1) and a[2][0]>=1 and b[:2]==('list','C') and b[3]:
            return normal(out[:i]+[run(1,minus1(a[2])),('list','B',b[2],True),bit(1)]+out[i+2:])
    return out

class State:
    def __init__(self,q,left,right,direction=1):self.q=q;self.left=list(left);self.right=list(right);self.direction=direction
    def key(self):
        self.left=normal(self.left);self.right=normal(self.right)
        return self.q,self.direction,self.left,self.right
    def step(self,table,lemmas,clock,motion):
        self.key()
        src,dst=(self.right,self.left) if self.direction==1 else (self.left,self.right)
        if not src:raise AssertionError('Unrepresented tape exterior')
        a=src[0]
        if a==BLANK:src.insert(0,bit(0));a=src[0]
        if a[0]=='list':
            key=(self.q,self.direction,a[1],a[3])
            assert key in lemmas,('No checked list traversal',key)
            src.pop(0);dst.insert(0,('list',lemmas[key],a[2],not a[3]))
            width=var(12)
            return add(clock,width),add(motion,width if self.direction==1 else neg(width)),('list',key)
        assert a[0]=='run',('Opaque context reached',self.q,self.direction,a)
        w,d,q=table[self.q,a[1]]
        row=(self.q,a[1],w,d,q)
        if q==self.q and d==self.direction:
            src.pop(0);dst.insert(0,run(w,a[2]))
            return add(clock,a[2]),add(motion,a[2] if d==1 else neg(a[2])),('unary',row,a[2])
        assert a[2][0]>=1,('Unknown run may be empty',row,a)
        src[0]=run(a[1],minus1(a[2]))
        if d==self.direction:dst.insert(0,bit(w))
        else:src.insert(0,bit(w));self.direction=d
        self.q=q
        return add(clock,num(1)),add(motion,num(d)),('literal',row)


def prove_blocks(table):
    # These names merely identify entry states. Every theorem is rederived
    # from this exact literal table; failed derivation is fatal.
    signatures=[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')]
    lemmas={};certificates=[];v=var(2)
    # Empty-list identity, and one-element identity with symbolic natural v.
    assert normal([bit(1)])==normal([bit(1)])
    assert normal(block(v,'C')+[bit(1)])==normal([bit(1)]+block(v,'B'))
    for q,d,before,after in signatures:
        L=('opaque','left');R=('opaque','right')
        if d==1:
            state=State(q,[L],block(v,before)+[R]);target=State(q,rev(block(v,after))+[L],[R])
        else:
            state=State(q,rev(block(v,before))+[L],[R],-1);target=State(q,[L],block(v,after)+[R],-1)
        steps=ZERO;motion=ZERO;trace=[]
        for _ in range(50):
            if state.key()==target.key():break
            steps,motion,event=state.step(table,{},steps,motion);trace.append(event)
        else:raise AssertionError(('One-block lemma did not close',q,d))
        assert steps==add(v,num(2))
        assert motion==(steps if d==1 else neg(steps))
        lemmas[q,d,before,d==-1]=after
        certificates.append({'entry':q,'direction':d,'before':before,'after':after,'steps':'v+2','arbitrary_contexts':True,'trace':trace})
    return lemmas,certificates


def file_bits(values,append=None):
    atoms=[]
    for v in values:atoms+=block(v)
    atoms+=block(var(11))+[tail()]
    if append is not None:atoms+=block(num(append))
    return atoms+[BLANK]

def case(table,lemmas,site,positive,append=1,keep_trace=False):
    pc,op,arg=site
    values=[var(2+i) for i in range(9)]
    if op=='CD':values[arg]=add(num(1),values[arg]) if positive else ZERO
    physical=[None]*9
    for i,j in enumerate(r.PHY):physical[j]=values[i]
    result=physical.copy();overflow=0;delta=0;extra=None
    if op=='CI':
        result[r.PHY[arg]]=add(result[r.PHY[arg]],num(1));successor,overflow=r.inc(pc);extra=append
    elif op=='CD' and positive:
        result[r.PHY[arg]]=minus1(result[r.PHY[arg]]);successor,overflow=r.inc(pc);delta=1
    elif op in ('CD','CB'):successor,overflow=r.inc(r.strip(pc,'0',arg if op=='CB' else 1))
    elif op=='CC':successor=r.strip(pc,'1',arg)
    elif op=='CH':successor=''
    else:raise AssertionError(site)
    state=State(96,[bit(1),BLANK],[bit(int(b)) for b in pc]+[run(0,add(var(1),num(64-len(pc)))),bit(1)]+file_bits(physical))
    target=State(96,[bit(1),BLANK],[bit(int(b)) for b in successor]+[run(0,add(var(1),num(64+delta+overflow-len(successor)))),bit(1)]+file_bits(result,extra))
    target_key=target.key();clock=ZERO;motion=ZERO;trace=[];rows=set();kinds={}
    for count in range(4000):
        key=state.key()
        if count and ((op=='CH' and state.q==254) or (op!='CH' and key==target_key)):
            assert nonnegative(clock) and clock[0]>0,('No positive progress',clock)
            if op!='CH':assert motion==num(-overflow),('Wrong head displacement',motion,overflow)
            return {'symbolic_steps':count,'duration':clock,'motion':motion,'rows':rows,'kinds':kinds,'trace':trace}
        clock,motion,event=state.step(table,lemmas,clock,motion)
        kinds[event[0]]=kinds.get(event[0],0)+1
        if event[0]!='list':rows.add(event[1][:2])
        if keep_trace:trace.append(event)
    raise AssertionError(('Symbolic proof did not close',site,positive,state.key(),target_key))



def validate_inputs(table,sites):
    working={q for q,b in table}
    assert 95 in working and 96 in working and 254 not in working
    assert len(table)==2*len(working) and all((q,b) in table for q in working for b in (0,1))
    assert {row[2] for row in table.values()}-working=={254}
    assert isinstance(sites,list) and len(sites)==4581
    leaves=set();prefixes=set()
    for row in sites:
        assert isinstance(row,list) and len(row)==3
        pc,op,arg=row
        assert isinstance(pc,str) and 0<len(pc)<=64 and set(pc)<={'0','1'}
        assert pc not in leaves
        assert op in ('CI','CD','CB','CC','CH')
        if op=='CH':assert arg is None
        elif op in ('CI','CD'):assert type(arg) is int and 0<=arg<9
        else:assert type(arg) is int and arg>=1
        leaves.add(pc);prefixes.update(pc[:i] for i in range(len(pc)))
    assert not leaves.intersection(prefixes)
    assert all(p+b in leaves or p+b in prefixes for p in prefixes for b in ('0','1'))
    assert len(prefixes)==len(leaves)-1
    # The complete QT source list is independently source-calibrated separately.
    # Pin its canonical serialization here; generic runtime rules are unchanged.
    encoded=(json.dumps(sites,indent=2)+'\n').encode()
    assert hashlib.sha256(encoded).hexdigest()=='a05f93768858315df92bdf1c7a55fc38d2a873ac7998e31fd361dbb04b90e024'
    return {'working_states':len(working),'leaf_count':len(leaves),'complete_binary_tree':True,'maximum_depth':max(map(len,leaves)),'exact_boundary_reassociated_source_pin':True,'source_equivalence_checked_separately':True}



def main():
    ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,default=r.BASE/'candidate-routing245/zfc_routing245_old.tm');ap.add_argument('--sites',type=Path,default=r.BASE/'certificate__sites_logical.json');ap.add_argument('--output',type=Path,default=r.OUT/'baseline245_universal_summary.json');ap.add_argument('--limit',type=int);ap.add_argument('--append',type=int,default=1);args=ap.parse_args()
    table=r.table(args.table);ss=json.loads(args.sites.read_text());started=time.monotonic()
    input_facts=validate_inputs(table,ss)
    checker_hash=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    helper_hash=hashlib.sha256(Path(r.__file__).read_bytes()).hexdigest()
    lemmas,blocks=prove_blocks(table)
    print('All four exact-table one-block schemas proved',flush=True)
    cases=[];rows=set();count=0
    for i,site in enumerate(ss):
        for positive in ((False,True) if site[1]=='CD' else (False,)):
            try:answer=case(table,lemmas,site,positive,args.append)
            except (AssertionError,KeyError) as exc:
                report={'status':'NOT_PROVED','site_index':i,'site':site,'positive':positive,'prior_cases':count,'reason':str(exc),'seconds':time.monotonic()-started}
                args.output.write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report),flush=True);return
            rows.update(answer.pop('rows'));answer.pop('trace');cases.append({'site_index':i,'positive':positive,**answer});count+=1
            if count%1000==0:print('proved',count,'cases',round(time.monotonic()-started,2),'seconds',flush=True)
            if args.limit and count>=args.limit:break
        if args.limit and count>=args.limit:break
    total=sum(2 if x[1]=='CD' else 1 for x in ss)
    report={'status':'UNIVERSAL_MATHEMATICAL_PASS' if count==total else 'PARTIAL_UNIVERSAL_PASS','checker_sha256':checker_hash,'helper_sha256':helper_hash,'input_validation':input_facts,'execution':{'python_version':sys.version,'python_executable':sys.executable,'optimization':sys.flags.optimize,'debug_enabled':__debug__,'dont_write_bytecode':sys.dont_write_bytecode,'PYTHONOPTIMIZE':os.environ.get('PYTHONOPTIMIZE'),'B245_INPUTS':str(r.BASE),'B245_OUTPUT':str(r.OUT),'argv':sys.argv},'cases':count,'expected_cases':total,'symbolic_steps':sum(x['symbolic_steps'] for x in cases),'minimum_actual_steps':min(x['duration'][0] for x in cases),'seconds':time.monotonic()-started,'table_sha256':hashlib.sha256(args.table.read_bytes()).hexdigest(),'sites_sha256':hashlib.sha256(args.sites.read_bytes()).hexdigest(),'scope':'All independent natural primary values at each decrement guard, arbitrary natural additional gap, arbitrary first spare value and arbitrary finite remaining spare list, whole tape including zero exterior. Mathematical checker, not a formal proof-assistant artifact.','loop_bounds_scope':'4000 bounds proof construction only; it does not bound actual runtime, register values, gap, or spare-list length','blocks':blocks,'directly_used_rows':sorted(rows),'cases_data_file':args.output.stem+'_cases.json'}
    args.output.write_text(json.dumps(report,indent=2)+'\n');args.output.with_name(args.output.stem+'_cases.json').write_text(json.dumps(cases,indent=2)+'\n');print(json.dumps({k:v for k,v in report.items() if k not in ('blocks','directly_used_rows')},indent=2),flush=True)
if __name__=='__main__':main()
