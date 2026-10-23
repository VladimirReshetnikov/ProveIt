"""New, read-only finite diagnostic, transcribed from pinned KRuntimeCore.

Does not import or execute repository code. Not a proof-assistant certificate.
"""
import collections
import hashlib
import json
from pathlib import Path
import re
import sys

if not __debug__:
    raise RuntimeError('Optimization is unsupported; run without -O.')

D = Path(__file__).resolve().parent
PHY = (6, 2, 0, 4, 3, 7, 8, 5, 1)
SK = (51, 36, 25, 48, 32, 33, 22, 55, 60)
B = lambda b: ('bit', int(b))
R = lambda b, a, c: ('run', int(b), a, c)
X = lambda k='none', r=0: ('box', k, r)

def require(c, message):
    if not c:
        raise ValueError(message)

def load_table():
    text = (D/'inputs/KTable215.lean').read_text()
    body = text.split('def table215 : List (Row × Row) := [', 1)[1].split(']', 1)[0]
    rows = []
    for line in body.splitlines():
        if not line.strip():
            continue
        matches = re.findall(r'none|some \((true|false), (true|false), (\d+)\)', line)
        require(len(matches) == 2, 'Bad table line: ' + line)
        rows.append([None if not q else (int(w=='true'),int(d=='true'),int(q)) for w,d,q in matches])
    require(len(rows)==226, 'Expected the 226-row table with disabled rows')
    return {(q,b): row for q,pair in enumerate(rows) for b,row in enumerate(pair) if row is not None}

def check_sources(table, sites):
    """Independently bind every literal site and port to current production text."""
    source=(D/'inputs/KSource215Program.lean').read_text()
    nodes={}
    for index,a,b in re.findall(r'\| (\d+) => \(\(([^()]*)\), \(([^()]*)\)\)',source):
        edges=[]
        for raw in (a,b):
            parts=raw.split();edges.append((parts[0][1:],int(parts[1]) if len(parts)==2 else 0))
        nodes[int(index)]=edges
    for index,a in re.findall(r'\| (\d+) => \(\(([^()]*)\), \.halt\)',source):
        parts=a.split();nodes[int(index)]=[(parts[0][1:],int(parts[1])),('halt',0)]
    root,count=map(int,re.search(r'def p215 : Program := ⟨p215Nodes, (\d+), (\d+)⟩',source).groups())
    require(len(nodes)==count,'Program node census')
    rocq_program=(D/'inputs/Prog215.v').read_text()
    rocq_block=rocq_program.split('Definition p215_tab :',1)[1].split('[',1)[1].split(']',1)[0]
    rocq_nodes={};kinds={'CI':'inc','CD':'decnz','CB':'brk','CC':'cont','CN':'node','CH':'halt'}
    for index,(left,right) in enumerate(re.findall(r'\((C[IDBCNH](?: \d+)?), (C[IDBCNH](?: \d+)?)\)',rocq_block)):
        es=[]
        for raw in (left,right):
            parts=raw.split();es.append((kinds[parts[0]],int(parts[1]) if len(parts)==2 else 0))
        rocq_nodes[index]=es
    require(rocq_nodes==nodes,'Rocq and Lean source programs differ')
    rocq_root,rocq_count=map(int,re.search(r'root := (\d+); nnodes := (\d+)',rocq_program).groups())
    require((rocq_root,rocq_count)==(root,count),'Rocq source root/count differ')
    expected=[];opnames={'inc':'CI','decnz':'CD','brk':'CB','cont':'CC','halt':'CH'}
    def visit(index,prefix):
        require(len(prefix)<=48,'Cyclic or oversized source path')
        for bit,(kind,arg) in enumerate(nodes[index]):
            pc=prefix+str(bit)
            if kind=='node':visit(arg,pc)
            else:expected.append([pc,opnames[kind],None if kind=='halt' else arg])
    visit(root,'')
    require(expected==sites,'Maintained source does not equal all supplied sites')
    decoder=(D/'inputs/K215Decoder.lean').read_text()
    block=decoder.split('def sourceNodes :',1)[1].split('#[',1)[1].split(']',1)[0]
    semantic=[(kind,int(a),int(b))for kind,a,b in re.findall(r'\.(leaf|fork) (\d+) (\d+)',block)]
    roles=[]
    block=decoder.split('def roles : Array Role := #[',1)[1].split('\n\n',1)[0]
    for line in block.splitlines():
        if not line.strip() or line.strip()==']':continue
        match=re.fullmatch(r'\s*⟨(\d+), (\d+), \[([^]]*)\], (.*)⟩[,\]]*',line)
        require(match is not None,'Unparsed decoder role')
        node,q,ctx,edges=match.groups();parsed=[]
        for edge in re.finditer(r'\(\.internal (\d+) (\d+)\)|\(\.primitive (\d+) ⟨(true|false), (\(?-?1\)?), (\d+)⟩\)',edges):
            rid,window,n,w,d,t=edge.groups()
            parsed.append(('internal',int(rid))if rid is not None else ('primitive',int(n),(int(w=='true'),int(d.strip('()')=='1'),int(t))))
        require(len(parsed)==2,'Expected two role edges')
        roles.append((int(node),int(q),tuple(int(x.strip()=='true')for x in ctx.split(',')if x.strip()),parsed))
    ports={};ops={0:'CI',1:'CD',2:'CB',3:'CC',4:'CH'}
    for pc,op,arg in sites:
        rid=0;node=roles[0][0];history=(1,)
        for bit in map(int,pc[:-1]):
            n,q,ctx,edges=roles[rid]
            require(n==node and ctx==history[-2:] and semantic[n][0]=='fork','Role prefix mismatch')
            edge=edges[bit];require(edge[0]=='internal','Premature primitive')
            rid=edge[1];node=semantic[n][1+bit];history+=(bit,)
        n,q,ctx,edges=roles[rid];bit=int(pc[-1]);edge=edges[bit]
        require(n==node and ctx==history[-2:] and edge[0]=='primitive','Leaf role mismatch')
        require(semantic[n][0]=='fork' and semantic[n][1+bit]==edge[1],'Wrong semantic leaf')
        kind,code,a=semantic[edge[1]]
        require((kind,ops[code],a)==('leaf',op,0 if op=='CH' else arg),'Wrong source operation')
        require(table[q,bit]==edge[2],'Primitive table binding mismatch')
        ports[pc]=q
    raw=(D/'inputs/Table230.v').read_text().split('Definition table230 :',1)[1]
    entries=re.findall(r'\((true|false), ([LR]), (\d+), (true|false), ([LR]), (\d+)\)',raw)
    tm=(D/'inputs/TM230.v').read_text().split('Definition tmn',1)[1].split('Definition tm :',1)[0]
    disabled=set(map(int,re.findall(r'Nat.eqb q (\d+)',tm)))
    rocq={}
    for q,e in enumerate(entries):
        if q in disabled:continue
        for bit in (0,1):
            w,d,t=e[bit*3:bit*3+3];rocq[q,bit]=(int(w=='true'),int(d=='R'),int(t))
    require(rocq==table,'Rocq and Lean physical tables differ')
    return ports

def step(table, branch, s):
    q,left,ls,rs=s
    if left:
        if not ls:
            return (q,False,(),(B(0),)+rs),False,'reorient'
        x,*tail=ls;tail=tuple(tail)
        if x[0]=='bit':
            return (q,False,tail,(x,)+rs),False,'reorient'
        if x[0]!='run': return None
        _,b,a,c=x
        row=table.get((q,b))
        if row is not None and row[1:]==(0,q):
            return (q,True,tail,(R(row[0],a,c),)+rs),False,'scan'
        if c: return (q,True,(B(b),R(b,a,c-1))+tail,rs),False,'peel'
        if not a: return (q,True,tail,rs),False,'peel'
        return None
    if not rs: return None
    x,*tail=rs;tail=tuple(tail)
    if x[0]=='bit':
        row=table.get((q,x[1]))
        if row is None:return None
        w,d,t=row
        return ((t,False,(B(w),)+ls,tail) if d else (t,True,ls,(B(w),)+tail)),True,'literal'
    if x[0]=='run':
        _,b,a,c=x;row=table.get((q,b))
        if row is not None and row[1:]==(1,q):
            return (q,False,(R(row[0],a,c),)+ls,tail),False,'scan'
        if c:return (q,False,ls,(B(b),R(b,a,c-1))+tail),False,'peel'
        if not a:return (q,False,ls,tail),False,'peel'
        return None
    if tail:return None
    _,kind,r=x;answer=None
    if kind=='none' and q in SK:
        r=SK.index(q);answer=(1 if not r else 3,X('mark',r),False)
    elif kind=='mark' and r<9:
        if q==64:answer=(40,X('inc',r),False)
        elif q==0 and branch is not None and branch[0]==r:
            answer=(97,X(),False) if branch[1] else (40,X('dec',r),True)
    if answer is not None:
        t,y,extra=answer
        return (t,True,((B(1),) if extra else ())+ls,(y,)),False,'oracle'
    row=table.get((q,0))
    if row is not None and row[:2]==(0,0):return (row[2],True,ls,rs),True,'boxedge'
    return None

def oracle_cut(s, op, reg):
    return s[0] == (64 if op=='CI' else 0) and not s[1] and s[3]==(X('mark',reg),)

def scan_bound(xs):
    i=0
    for x in xs:
        if x[0]=='bit':i=0 if x[1] else i+1
        elif x[0]=='run':
            _,b,a,c=x
            if b:
                if c:i=0
            elif a:return None
            else:i+=c
        else:return None
        if i>=8:return None
    return i

def home(s):
    q,on,ls,rs=s
    if q!=2 or not on:return None
    xs=list(reversed(ls))
    while xs:
        x=xs.pop(0)
        if x[0] in ('bit','run') and x[1]==0:continue
        if x!=B(1):return None
        if scan_bound(reversed(xs)) is None:return None
        return (84,False,(B(1),),tuple(xs)+rs),True,'home'
    return None

def step_home(table,br,s):
    return home(s) or step(table,br,s)

def norm(xs,left=False):
    out=[]
    for x in xs:
        if x[0]=='bit':x=R(x[1],0,1)
        if x[0]=='run' and x[2:]==(0,0):continue
        if out and x[0]=='run' and out[-1][:2]==x[:2]:
            y=out.pop();x=R(x[1],x[2]+y[2],x[3]+y[3])
        out.append(x)
    if left and out and out[-1][:2]==('run',0):out.pop()
    return tuple(out)

def matches(a,b):
    return a[:2]==b[:2] and norm(a[2],True)==norm(b[2],True) and norm(a[3])==norm(b[3])

def execute(table,br,start,target,next_step=step_home,moved=False,fuel=4000):
    s=start;trace=[]
    for _ in range(fuel):
        if moved and target(s):return s,trace
        out=next_step(table,br,s)
        if out is None:return None
        t,m,k=out;trace.append((s,t,m,k));moved|=m;s=t
    return None

def run_to(table,br,start,target,next_step=step_home):
    result=execute(table,br,start,lambda s:matches(s,target),next_step)
    require(result is not None,'Incomplete symbolic execution')
    return result[1]

def inc_path(pc):
    v=int(pc,2)+1
    return format(v%(1<<len(pc)),'0'+str(len(pc))+'b'),v==(1<<len(pc))

def break_path(pc):
    k=pc.rfind('0')
    pre=pc[:k] if k>=0 else ''
    if not pre:return '',True
    return inc_path(pre)


def main():
    pins=json.loads((D/'inputs/SOURCE_PINS.json').read_text())
    for name,pin in pins.items():
        data=(D/'inputs'/name).read_bytes()
        require(hashlib.sha256(data).hexdigest()==pin['sha256'],'Changed source '+name)
        if 'git_blob' in pin:
            require(hashlib.sha1(b'blob '+str(len(data)).encode()+b'\0'+data).hexdigest()==pin['git_blob'],'Source blob identity '+name)
    table=load_table()
    sites=json.loads((D/'inputs/sites.json').read_text())
    ports=check_sources(table,sites)
    renaming={301:102,302:120,254:230}
    native={}
    for ln in (D/'inputs/native.tm').read_text().splitlines():
        if not ln or ln.startswith('#'):continue
        q,b,w,d,t=ln.split();native[renaming.get(int(q),int(q)),int(b)]=(int(w),int(d=='R'),renaming.get(int(t),int(t)))
    require(native==table,'Native/formal label map mismatch')
    uses=[];cut_counter=collections.Counter();total=0;saved=0;rocq_total=0;rocq_saved=0;lean_total=0;lean_saved=0
    for i,(pc,op,arg) in enumerate(sites):
        if op!='CD':continue
        q=renaming.get(ports[pc],ports[pc]);r=PHY[arg]
        start=(q,False,tuple(B(int(b)) for b in reversed(pc[:-1]))+(B(1),),(B(int(pc[-1])),R(0,1,64-len(pc)),B(1),X()))
        targets=[];traces=[]
        for z in (True,False):
            successor,overflow=break_path(pc) if z else inc_path(pc)
            target=(84,False,(B(1),),tuple(B(int(b)) for b in successor)+(R(0,1,64+int(overflow)+int(not z)-len(successor)),B(1),X() if z else X('dec',r)))
            trace=run_to(table,(r,z),start,target)
            targets.append(target);traces.append(trace)
        common=0
        for a,b in zip(*traces):
            if a!=b:break
            common+=1
        require(common>0,'Missing positive common prefix')
        cut=traces[0][common][0]
        require(oracle_cut(cut,op,r),'First differing step not the expected register oracle')
        prefix=traces[0][:common]
        require(any(x[2] for x in prefix),'Prefix does not establish positive progress')
        for s,t,m,k in prefix:
            require(step_home(table,None,s)==(t,m,k),'Neutral prefix differs')
        factored=execute(table,None,start,lambda s:oracle_cut(s,op,r))
        require(factored==(cut,prefix),'Explicit neutral-prefix checker mismatch')
        for z,target,trace in zip((True,False),targets,traces):
            tail=execute(table,(r,z),cut,lambda s:matches(s,target),moved=True)
            require(tail is not None and tail[1]==trace[common:],'Factored continuation mismatch')
        require(sum(x[3]=='oracle' for x in traces[0][common:])==1,'Unexpected second oracle')
        require(sum(x[3]=='oracle' for x in traces[1][common:])==1,'Unexpected second oracle')
        before=sum(map(len,traces));after=before-common
        total+=before;saved+=common;cut_counter[r]+=1
        raw_start=(84,False,(B(1),),tuple(B(int(b))for b in pc)+(R(0,1,64-len(pc)),B(1),X()))
        raw_traces=[run_to(table,(r,z),raw_start,target,step)for z,target in zip((True,False),targets)]
        raw_common=0
        for a,b in zip(*raw_traces):
            if a!=b:break
            raw_common+=1
        require(oracle_cut(raw_traces[0][raw_common][0],op,r),'Raw Rocq boundary mismatch')
        require(any(x[2]for x in raw_traces[0][:raw_common]),'Raw prefix nonpositive')
        for s,t,m,k in raw_traces[0][:raw_common]:require(step(table,None,s)==(t,m,k),'Raw neutral mismatch')
        raw_cut=raw_traces[0][raw_common][0]
        factored_raw=execute(table,None,raw_start,lambda s:oracle_cut(s,op,r),step)
        require(factored_raw==(raw_cut,raw_traces[0][:raw_common]),'Raw explicit fork mismatch')
        for z,target,trace in zip((True,False),targets,raw_traces):
            tail=execute(table,(r,z),raw_cut,lambda s:matches(s,target),step,moved=True)
            require(tail is not None and tail[1]==trace[raw_common:],'Raw continuation mismatch')
        rocq_total+=sum(map(len,raw_traces));rocq_saved+=raw_common
        full_traces=[run_to(table,(r,z),raw_start,target,step_home)for z,target in zip((True,False),targets)]
        full_common=0
        for a,b in zip(*full_traces):
            if a!=b:break
            full_common+=1
        full_cut=full_traces[0][full_common][0]
        require(oracle_cut(full_cut,op,r),'Lean full-start oracle mismatch')
        require(execute(table,None,raw_start,lambda s:oracle_cut(s,op,r))==(full_cut,full_traces[0][:full_common]),'Lean full-start neutral mismatch')
        for z,target,trace in zip((True,False),targets,full_traces):
            tail=execute(table,(r,z),full_cut,lambda s:matches(s,target),moved=True)
            require(tail is not None and tail[1]==trace[full_common:],'Lean full-start suffix mismatch')
        lean_total+=sum(map(len,full_traces));lean_saved+=full_common
        uses.append({'lean_full_prefix_steps':full_common,'lean_full_baseline_steps':sum(map(len,full_traces)),'rocq_prefix_steps':raw_common,'rocq_baseline_steps':sum(map(len,raw_traces)),'site':i,'pc':pc,'physical_register':r,'prefix_steps':common,'zero_suffix_steps':len(traces[0])-common,'positive_suffix_steps':len(traces[1])-common,'prefix_homes':sum(x[3]=='home'for x in prefix),'cut':cut})
    summary={'status':'FINITE_ORACLE_CUT_PASS','revision':'cbf94cb552a3b49509e0eee80e7455d4eb5974c6','table_rows':len(table),'decrement_sites':len(uses),'decrement_outcomes':2*len(uses),'baseline_symbolic_steps':total,'factored_symbolic_steps':total-saved,'saved_symbolic_steps':saved,'saved_fraction':saved/total,'prefix_steps_min':min(u['prefix_steps']for u in uses),'prefix_steps_max':max(u['prefix_steps']for u in uses),'prefix_home_shortcuts':sum(u['prefix_homes']for u in uses),'physical_registers':dict(cut_counter),'rocq_whole_site_baseline_steps':rocq_total,'rocq_whole_site_factored_steps':rocq_total-rocq_saved,'rocq_whole_site_saved_steps':rocq_saved,'rocq_whole_site_saved_fraction':rocq_saved/rocq_total,'lean_whole_site_baseline_steps':lean_total,'lean_whole_site_factored_steps':lean_total-lean_saved,'lean_whole_site_saved_steps':lean_saved,'lean_whole_site_saved_fraction':lean_saved/lean_total,'scope':'New finite diagnostic, not compiled Lean or Rocq. Replays both complete decrement outcomes, isolates common prefix, and checks branch neutrality. Does not certify all-site coverage or endpoint.'}
    out={'summary':summary,'uses':uses}
    (D/'ORACLE_CUT_RESULT.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(summary,indent=2))

if __name__=='__main__':main()
