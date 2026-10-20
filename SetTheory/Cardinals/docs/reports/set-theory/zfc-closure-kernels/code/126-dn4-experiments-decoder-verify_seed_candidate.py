#!/usr/bin/env python3
"""Complete literal runtime checking relative to an inductive source invariant.

The register masks are checked as a finite source invariant independently.
This driver proves all permitted instruction guards by literal steps and
reproved unary/list induction schemas on the supplied candidate table.
It is an executable ordinary mathematical certificate, not a kernel proof.
"""
from seed_runtime_windows import *
from collections import deque


def prove_mapped_blocks(table,phi):
    signatures=[(73,1,'B','B'),(95,1,'B','C'),(48,-1,'B','B'),(112,-1,'C','B')]
    lemmas={};certs=[];val=e.var(2)
    for oq,d,before,after in signatures:
        q=phi(oq);lc=('opaque','left');rc=('opaque','right')
        if d==1:
            st=e.State(q,[lc],e.block(val,before)+[rc]);target=e.State(q,e.rev(e.block(val,after))+[lc],[rc])
        else:
            st=e.State(q,e.rev(e.block(val,before))+[lc],[rc],-1);target=e.State(q,[lc],e.block(val,after)+[rc],-1)
        clock=motion=e.ZERO;trace=[]
        for _ in range(100):
            if st.key()==target.key():break
            clock,motion,event=st.step(table,{},clock,motion);trace.append(event)
        else:raise AssertionError(('mapped block failed',oq,q,d))
        assert e.nonnegative(e.add(clock,e.neg(e.add(val,e.num(2)))))
        assert motion==(e.add(val,e.num(2))if d==1 else e.neg(e.add(val,e.num(2))))
        # Macros may stutter, so their duration can differ from block width.
        # State.step's list rule assumes time equals width. A conservative
        # lower bound ofwidth is valid if every literal block ispositive.
        key=q,d,before,d==-1
        if key in lemmas:assert lemmas[key]==after
        lemmas[key]=after;certs.append(dict(old_entry=oq,entry=q,direction=d,before=before,after=after,duration=clock,trace=trace))
    return lemmas,certs


def main():
    ap=argparse.ArgumentParser();ap.add_argument('table',type=Path);ap.add_argument('--keep',type=int);ap.add_argument('--drop',type=int);ap.add_argument('--basis',type=Path,default=Path(__file__).parent/'full_dn4');ap.add_argument('--facts',type=Path,default=Path(__file__).parent/'facts/dn4_reachable_registers.json');ap.add_argument('--output',type=Path,required=True);ap.add_argument('--limit',type=int);a=ap.parse_args()
    tic=time.monotonic();norm,start=v.parse_table(a.table.read_bytes());basis=a.basis;mp={int(k):z for k,z in json.loads((basis/'state_map.json').read_text()).items()};mp[254]=254
    for q,b in norm:
        if q not in mp:mp[q]=q+300
    table={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in norm.items()};drop=None if a.drop is None else mp[a.drop];keep=None if a.keep is None else mp[a.keep];phi=lambda q:keep if q==drop else q
    sites=json.loads((basis/'sites225.json').read_text());info=json.loads(a.facts.read_text());assert info['source_sha256']==hashlib.sha256((basis/'sites225.json').read_bytes()).hexdigest()
    # Parse through the independent source checker used by the invariant.
    sys.path.insert(0,str(P/'verification'));import check225 as check
    _,graph,entry=check.source(basis/'sites225.json');C,M=info['cutoff'],info['modulus'];N=C+M
    def bucket(n):return n if n<C else C+n%M
    def reps(i):return [i]if i<C else[n for n in range(C,C+2*M)if bucket(n)==i]
    inc=[sum(1<<j for j in{bucket(n+1)for n in reps(i)})for i in range(N)];dec=[sum(1<<j for j in{bucket(n-1)for n in reps(i)if n>0})for i in range(N)]
    def tr(mask,tt):return sum(1<<j for j in range(N)if any((mask>>i&1)and(tt[i]>>j&1)for i in range(N)))
    assert entry==info['entry'];assert all(info['facts'][entry][i]>>bucket(n)&1 for i,n in enumerate(info['seed']))
    closure=0
    for i,vals in enumerate(info['facts']):
        if vals is None:continue
        op,arg,ss=graph[i];outs=[]
        if op=='CI':z=vals.copy();z[arg]=tr(z[arg],inc);outs=[(ss[0],z)]
        elif op=='CD':
            if vals[arg]&~1:z=vals.copy();z[arg]=tr(z[arg]&~1,dec);outs.append((ss[0],z))
            if vals[arg]&1:z=vals.copy();z[arg]=1;outs.append((ss[1],z))
        elif op!='CH':outs=[(ss[0],vals)]
        for j,z in outs:assert info['facts'][j]is not None and all(x&~y==0 for x,y in zip(z,info['facts'][j]));closure+=1
    # Dispatcher aliases are materialized only at the entry/target boundary;
    # all working transitions remain the literal supplied candidate table.
    # restricted_case currently names96. If it isfolded, cloneitsPythonfunction
    # replacing the literal boundary label, without changing a table row.
    import inspect
    source=inspect.getsource(restricted_case).replace('e.State(96,',f'e.State({phi(96)},')
    ns=globals().copy();exec(source,ns);run_case=ns['restricted_case']
    report=dict(status='RUNNING',states=len(norm)//2,table_sha256=hashlib.sha256(a.table.read_bytes()).hexdigest(),source_sha256=info['source_sha256'],register_invariant_closure_checks=closure,fold=dict(keep=a.keep,drop=a.drop))
    def save():report['seconds']=time.monotonic()-tic;c.dump(a.output,report)
    try:lemmas,blocks=prove_mapped_blocks(table,phi)
    except Exception as exc:report.update(status='NOT_PROVED',stage='blocks',reason=repr(exc));save();print(json.dumps(report),flush=True);return
    report['blocks']=blocks;count=steps=0;rows=set();cases=[]
    for i,site in enumerate(sites):
        masks=info['facts'][i]
        if masks is None:continue
        for pos in((False,True)if site[1]=='CD'else(False,)):
            values=initial_values(site,pos,masks,C,M)
            if values is None:continue
            try:n,rr=run_case(table,lemmas,site,pos,values)
            except Exception as exc:
                report.update(status='NOT_PROVED',stage='runtime',site_index=i,site=site,positive=pos,prior_cases=count,reason=repr(exc));save();print(json.dumps({k:z for k,z in report.items()if k!='blocks'}),flush=True);return
            count+=1;steps+=n;rows|=rr;cases.append([i,pos,n])
        if count and count%500<2:print('PROGRESS',i,count,steps,'secs',time.monotonic()-tic,flush=True)
        if a.limit and count>=a.limit:break
    boot=json.loads((basis/'startup.json').read_text());q=start;head=0;ones=set();wanted=boot['ones'];dispatch=a.keep if a.drop==84 else 84
    for step in range(2000001):
        if q==dispatch and head==boot['head']and len(ones)==len(wanted)and sorted(ones)==wanted:break
        if q==254:raise AssertionError(('boot halt',step))
        w,d,q=norm[q,int(head in ones)]
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d
    else:report.update(status='NOT_PROVED',stage='boot',prior_cases=count,reason='no complete seed frame within proof-construction limit');save();print(json.dumps({k:z for k,z in report.items()if k!='blocks'}),flush=True);return
    report.update(status='SEED_RESTRICTED_UNIVERSAL_MATHEMATICAL_PASS'if not a.limit else'PARTIAL_SEED_RESTRICTED_PASS',cases=count,symbolic_steps=steps,rows=len(rows),boot_steps=step,complete_seed_frame_equal=True,scope='Every guarded source configuration in a checked Cartesian overapproximation of the calibrated reachable source states. Exact candidate-table unary and finite-list schemas; all source contracts; exact whole blank-start frame. Ordinary mathematical evidence, not a formal proof-assistant theorem.')
    c.dump(a.output.with_name(a.output.stem+'_cases.json'),cases);save();print(json.dumps({k:z for k,z in report.items()if k!='blocks'},indent=2),flush=True)
if __name__=='__main__':main()
