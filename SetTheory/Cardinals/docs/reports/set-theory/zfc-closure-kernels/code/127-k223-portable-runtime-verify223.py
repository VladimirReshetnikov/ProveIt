"""Fresh literal runtime/startup check of a source compiler's K-labelled candidate.

Inputs are snapshotted. This establishes the exact supplied source, not its
calculus adequacy. Runtime induction is inherited but freshly replayed.
"""
from pathlib import Path
import sys,json,hashlib,time
sys.dont_write_bytecode=True
H=Path(__file__).resolve().parent;P=H
sys.path.insert(0,str(P));import check224 as c
sys.path.insert(0,str(P/'vendor'));import symbolic_runtime as s

def need(x,msg):
    if not x:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,x):p.write_text(json.dumps(x,indent=2)+'\n')

need(__debug__,'Assertions must remain enabled')
src=Path(sys.argv[1])if len(sys.argv)>1 else H/'inputs';out=Path(sys.argv[2])if len(sys.argv)>2 else H/'results';out.mkdir(parents=True,exist_ok=True)
for name in ('candidate.tm','sites.json'):(out/name).write_bytes((src/name).read_bytes())
T,start,halt,Q=c.parse(out/'candidate.tm');need((start,halt)==(0,254),'Unexpected labels')
S,G,metrics=c.source_graph(out/'sites.json')
need(len(Q)==223 and len(T)==446,'Exact223 state census')
need(sha(out/'candidate.tm')=='614adb7d387a5ccdaebecd37d8896d62bb162a20fb8b93b73ec2bd80bd75d785','Exact223 table')
need(sha(out/'sites.json')=='b4e453a8801597124fd9b3ee1cd2db1cdf80c0bd904c2ffb59b79d95e91a6e96','Exact conditional source')
mp={int(q):z for q,z in json.loads((P/'reference/legacy_state_map.json').read_text())['k230_to_old'].items()}
mp[254]=254
for q in Q:
    if q not in mp or mp[q]==254:mp[q]=1000+q
mp={q:mp[q]for q in Q|{254}}
need(len(set(mp.values()))==len(mp),'Noninjective state map')
need((mp[0],mp[84],mp[254])==(95,96,254),'Mapped interfaces changed')
T={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in T.items()}
(out/'candidate.legacy.tm').write_text('#! start 95\n'+''.join(f'{q} {b} {w} {"R" if d==1 else "L"} {z}\n'for(q,b),(w,d,z)in sorted(T.items())))
dump(out/'legacy_mapping.json',mp)
R=dict(status='IN_PROGRESS',source_directory='inputs'if src.resolve()==(H/'inputs').resolve()else str(src),table_sha256=sha(out/'candidate.tm'),legacy_table_sha256=sha(out/'candidate.legacy.tm'),source_sha256=sha(out/'sites.json'),working_states=len(Q),rows=len(T),source_metrics=metrics,physical_map=s.r.PHY,engine_sha256=sha(Path(s.__file__)),helper_sha256=sha(Path(s.r.__file__)),driver_sha256=sha(Path(__file__)),scope='Exact supplied source with nine independent natural registers, every decrement guard, arbitrary natural extra gap, and arbitrary nonempty finite spare list. Executable ordinary induction, no new proof-assistant theorem. Changed-source adequacy is a separate premise.')
beg=time.monotonic();cases=[];used=set()
def save():R.update(seconds=time.monotonic()-beg,cases=len(cases));dump(out/'proof.json',R)
try:
    # A structurally clean root PC has no one between its marker and header.
    # Search is discovery; the resulting exact prefix is replayed independently.
    q=95;h=0;ones=set();boot=None
    for tick in range(2000001):
        if q==96 and ones and min(ones)==h-1:
            right=sorted(x for x in ones if x>=h)
            if right and right[0]>=h+64:
                hd=right[0];p=hd+1;vals=[];ok=True
                while p<=max(ones):
                    if p in ones:ok=False;break
                    p+=1;n=0
                    while p in ones:n+=1;p+=1
                    if not n:ok=False;break
                    vals.append(n-1)
                if ok and len(vals)>=10:
                    boot=dict(steps=tick,dispatcher=q,head=h,header=hd,extra_gap=hd-h-64,physical_registers=vals[:9],logical_seed=[vals[j]for j in s.r.PHY],spares=vals[9:],complete_one_cells=sorted(ones),all_other_cells=0);break
        if tick==2000000 or q==254:break
        w,d,q=T[q,int(h in ones)]
        if w:ones.add(h)
        else:ones.discard(h)
        h+=d
    need(boot is not None,('No structural root found within startup discovery bound',tick,q,h))
    org=boot['steps']+2;arr=bytearray(2*org+1);qq=95;hh=org
    for _ in range(boot['steps']):
        w,d,qq=T[qq,arr[hh]];arr[hh]=w;hh+=d
    need((qq,hh-org,{i-org for i,b in enumerate(arr)if b})==(q,h,ones),'Independent complete startup differs')
    expected={h-1,boot['header']};p=boot['header']+1
    for v in vals:p+=1;expected.update(range(p,p+v+1));p+=v+1
    need(ones==expected,'Startup support differs from full frame')
    R['startup']=boot;save();print('EXACT STARTUP',boot['steps'],boot['logical_seed'],flush=True)
    L,B=s.prove_blocks(T);R['blocks']=B
    for i,site in enumerate(S):
        for positive in ((False,True)if site[1]=='CD'else(False,)):
            ans=s.case(T,L,site,positive);used.update(ans.pop('rows'));ans.pop('trace');cases.append(dict(site_index=i,positive=positive,**ans))
            if len(cases)%1000==0:save();print('PROVED',len(cases),R['seconds'],flush=True)
    need(len(cases)==metrics['guarded_cases'],'Incomplete guard coverage')
    dump(out/'cases.json',cases)
    R.update(status='FULL_UNBOUNDED_RUNTIME_AND_EXACT_STARTUP_PASS',symbolic_steps=sum(a['symbolic_steps']for a in cases),all_rows_used=used==set(T),unused_rows=sorted(set(T)-used),minimum_actual_steps=min(a['duration'][0]for a in cases),cases_sha256=sha(out/'cases.json'))
    save();print(R['status'],len(cases),flush=True)
except Exception as e:
    R.update(status='NOT_PROVED',site_index=locals().get('i'),site=locals().get('site'),positive=locals().get('positive'),error=repr(e));save();raise
