"""Reproduce a bounded short-gap diagnostic for runtime252 on blank input.

Dependencies under --upstream: ZF/m254/machine/zfc_254.tm,
ZF/m254/coq/tm/Prog254.v, and ZF/m254/tools/tm/symexec.py.
The literal prefix uses the full table. Accelerated continuations use the
upstream prototype's register-box summaries and are not kernel proofs.
Both affine gaps g+n and exact fixed gap g are reported distinctly.
"""
from pathlib import Path
import sys,json,re,argparse,hashlib
HERE=Path(__file__).resolve().parent
REPO=HERE.parent/'vendor'/'busy-beaver'
PHYS=(6,7,0,2,1,8,4,3,5)

def rows():
    raw=(REPO/'ZF/m254/machine/zfc_254.tm').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='d655ce2cf8cccebd21caa21a49f0f9f010960a44b95c17aae6cc425c518954eb'
    table={}
    for line in raw.decode().splitlines():
        if not line or line.startswith('#'):continue
        q,b,w,d,t=line.split();table[int(q),int(b)]=int(w),d,int(t)
    table.update({(3,0):(0,'L',48),(5,0):(1,'R',97),(5,1):(1,'R',64),(49,1):(0,'R',5)})
    table={k:(w,d,64 if t==5 else t) for k,(w,d,t) in table.items() if k[0] not in (5,8)}
    assert len(table)==504
    return table

def program():
    raw=(REPO/'ZF/m254/coq/tm/Prog254.v').read_bytes()
    assert hashlib.sha256(raw).hexdigest()=='1fbc30fcf82a1442ed88d1a1dde412630a431d32a7265d22bdf8517bffe01746'
    text=raw.decode()
    body=text.split('Definition p254_tab',1)[1].split('[',1)[1].split('].',1)[0]
    edge=r'(?:CN \d+|CI \d+|CD \d+|CB \d+|CC \d+|CH)'
    nodes=re.findall(r'\(('+edge+r'),\s*('+edge+r')\)',body)
    assert len(nodes)==6459
    return nodes
NODES=[]

def walk(p):
    edge='CN 0';path=''
    while edge.startswith('CN '):
        b=p[len(path)] if len(path)<len(p) else '0'
        edge=NODES[int(edge[3:])][int(b)];path+=b
    op,*arg=edge.split();r=None if not arg else int(arg[0])
    if op in ('CI','CD'):r=PHYS[r]
    return path,op,r

def parse_frame(frame):
    ones=set(frame['relative']);left={x for x in ones if x<0}
    if left!={-1}:return
    hi=max(ones)
    path,op,r=walk(''.join(str(int(i in ones)) for i in range(hi+1)))
    h=next((i for i in sorted(ones) if i>=len(path)),None)
    if h is None or h<len(path):return
    cursor=h+1;reg=[]
    while cursor<=hi:
        if cursor in ones:return
        cursor+=1;n=0
        while cursor in ones:n+=1;cursor+=1
        if n==0:return
        reg.append(n-1)
    if len(reg)<9:return
    # No assumptions about the local gap here: the symbolic verifier checks it.
    return {'p':path,'op':op,'r':r,'gap':h,'regs':reg[:9], 'spares':reg[9:],
            'time':frame['t'],'head':frame['h']}

def blank_checkpoint(fuel=999186):
    table=rows();q=64;h=0;ones=set()
    for _ in range(fuel):
        w,d,q=table[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=1 if d=='R' else -1
    assert q==96 and h==4
    frame={'t':fuel,'h':h,'relative':sorted(x-h for x in ones)}
    start=parse_frame(frame)
    assert start is not None and start['gap']==32
    assert start['p']=='1110100100101000101100110110'
    assert start['regs']==[60,4,2,4,0,0,0,0,0]
    assert len(start['spares'])==359
    assert [(i,x) for i,x in enumerate(start['spares']) if x]==[(62,1),(63,1),(75,1),(88,1)]
    assert paint(start['p'],start['gap'],start['regs'],start['spares'])==set(frame['relative'])
    return start

def executor():
    f=REPO/'ZF/m254/tools/tm/symexec.py'
    raw=f.read_bytes();assert hashlib.sha256(raw).hexdigest()=='5bf83da419c47b9c8d79fcc755e40048f599255c2f1b2cb4656dc04bb02bb85d'
    code=raw.decode().split('paths = json.load',1)[0]
    code='SKIP ='+code.split('SKIP =',1)[1]
    ns={'T':{(str(q),b):(w,d,str(t)) for (q,b),(w,d,t) in rows().items()},'D0':40}
    exec(compile(code,str(f),'exec'),ns)
    return ns

def input_segments(ns,p,exact_gap):
    segs=ns['tape_R'](p,0,())
    return [((s[0],s[1],0,s[3]) if s[0]=='r' else s) for s in segs] if exact_gap else segs

def expected(ns,p,op,r,br,g,exact_gap=False):
    ns['D0']=g
    if op=='CI' or op=='CD' and br=='p':p2=ns['inc'](p)
    elif op=='CD':p2=ns['inc'](ns['strip']('0',1,p))
    elif op=='CC':p2=ns['strip']('1',r,p)
    elif op=='CB':p2=ns['inc'](ns['strip']('0',r,p))
    else:p2=''
    effect=() if op not in ('CI','CD') else ((('inc' if op=='CI' else 'dec0' if br=='z' else 'dec'),r),)
    if p2 is None:
        segs=[('r',0,1,g+1),('b',1),('box',('plain',)+effect)]
    else:segs=ns['tape_R'](p2,0,effect)
    if exact_gap:segs=[((s[0],s[1],0,s[3]) if s[0]=='r' else s) for s in segs]
    exp=ns['canon']([('b',1)],segs)
    return p2,exp

def case(ns,p,op,r,br,g,exact_gap=False):
    if g<len(p):return False,None,'path exceeds header'
    p2,exp=expected(ns,p,op,r,br,g,exact_gap)
    try:
        res=ns['run']('96',[('b',1)],input_segments(ns,p,exact_gap),br,exp, fuel=5000)
        good=res[0]==('halt' if op=='CH' else 'ok')
        return good,p2,res
    except (ns['Fail'], KeyError) as ex:return False,p2,str(ex)

def paint(p,g,regs,spares):
    assert len(p)<=g
    ones={-1,g}|{i for i,b in enumerate(p) if b=='1'}
    cursor=g+1
    for n in regs+spares:
        assert n>=0
        cursor+=1
        ones.update(range(cursor,cursor+n+1));cursor+=n+1
    return ones

def literal_failure(result,limit=100000):
    state=result['state'];ns=executor();p=state['p'];g=state['gap'];op=state['op'];r=state['r'];br=state['branch']
    p2,_=expected(ns,p,op,r,br,g)
    regs=state['regs'].copy();spares=state['spares']+[0]*state['positive_decs']
    tape=paint(p,g,regs,spares);q=96;h=0;table=rows();frames=[]
    newregs=regs.copy();newspares=spares.copy();newg=g;newh=0
    if op=='CI':newregs[r]+=1
    elif op=='CD' and br=='p':newregs[r]-=1;newspares.append(0)
    if p2 is None:p2='';newg+=1;newh-=1
    target={x+newh for x in paint(p2,newg,newregs,newspares)}
    for t in range(limit+1):
        if q==254:return {'reason':'literal_halt','microsteps':t,'h':h}
        if t and q==96:
            if h==newh and tape==target:return {'reason':'literal_correct_instruction','microsteps':t,'h':h,'frames':frames}
            f={'t':t,'h':h,'relative':sorted(x-h for x in tape)}
            parsed=parse_frame(f)
            if parsed:frames.append({k:v for k,v in parsed.items() if k!='spares'}|{'spares':len(parsed['spares']),'nonzero_spares':[(i,x) for i,x in enumerate(parsed['spares']) if x]})
        if t==limit:break
        w,d,q=table[q,int(h in tape)]
        if w:tape.add(h)
        else:tape.discard(h)
        h+=1 if d=='R' else -1
    return {'reason':'literal_fuel','microsteps':limit,'q':q,'h':h,'ones':len(tape),'frames':frames,'end_tape':sorted(tape)}

def accelerate(start,limit,verbose=False,exact_gap=False):
    ns=executor();p=start['p'];regs=start['regs'].copy();g=start['gap'];head=start['head']
    spares=start['spares'].copy();cache={};events=[];positive_decs=0
    for i in range(limit):
        p,op,r=walk(p)
        br=('z' if regs[r]==0 else 'p') if op=='CD' else '-'
        key=p,op,r,br,g
        if key not in cache:cache[key]=case(ns,*key,exact_gap=exact_gap)
        good,p2,res=cache[key]
        state={'rm_step':i,'p':p,'op':op,'r':r,'branch':br,'gap':g,'head':head,'regs':regs.copy(),'spares':spares,'positive_decs':positive_decs}
        if not good:return {'reason':'failed_local_contract','result':res,'state':state,'events':events,'cases':len(cache)}
        if op=='CH':return {'reason':'halt','state':state,'events':events,'cases':len(cache)}
        if op=='CI':regs[r]+=1
        if op=='CD' and br=='p':regs[r]-=1;positive_decs+=1
        if p2 is None:
            g+=1;head-=1;p2=''
            events.append({'kind':'overflow','rm_step':i,'gap':g,'head':head,'regs':regs.copy(),'spares_initial':len(spares),'spares_appended':positive_decs})
            if verbose:print('OVERFLOW',events[-1],flush=True)
        if p2 in ('','0','00','000'):
            events.append({'kind':'root','rm_step':i+1,'p':p2,'gap':g,'head':head,'regs':regs.copy(),'spares_initial':len(spares),'spares_appended':positive_decs})
            if verbose:print('ROOT',events[-1],flush=True)
            if g>=40:
                return {'reason':'root_with_uniform_gap','state':events[-1],'events':events,'cases':len(cache)}
        p=p2
    p,op,r=walk(p)
    state={'rm_step':limit,'p':p,'op':op,'r':r,'gap':g,'head':head,'regs':regs.copy(),'spares':spares,'positive_decs':positive_decs}
    return {'reason':'fuel','state':state,'events':events,'cases':len(cache)}

def main():
    global REPO,NODES
    if not __debug__:
        raise SystemExit('Run without -O: pinned hashes and contracts use assertions.')
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--upstream',type=Path,default=REPO);ap.add_argument('--limit',type=int,default=1000000);ap.add_argument('--output',type=Path,default=HERE/'runtime252_short_gap.json');a=ap.parse_args()
    REPO=a.upstream.resolve();NODES=program()
    start=blank_checkpoint()
    affine=accelerate(start,a.limit,exact_gap=False)
    literal=literal_failure(affine) if affine['reason']=='failed_local_contract' else None
    fixed=accelerate(start,a.limit,exact_gap=True)
    result={'scope':'Literal prefix and one literal instruction; bounded accelerated continuation using upstream design-model register-box summaries. Not a kernel proof or a consistency-equivalent blank machine.','source':{'upstream_commit':'297ab8df7e5de329605c3875b4934643b371a5e3','table':'ZF/m254/machine/zfc_254.tm','program':'ZF/m254/coq/tm/Prog254.v','executor':'ZF/m254/tools/tm/symexec.py'},'literal_start':start,'affine':affine,'literal_check_at_affine_failure':literal,'fixed_gap':fixed}
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    for tag,x in [('affine',affine),('fixed_gap',fixed)]:
        print(tag,x['reason'],x.get('result'),{k:v for k,v in x['state'].items() if k!='spares'},'cases',x['cases'])
    print('literal',literal)

if __name__=='__main__':main()

