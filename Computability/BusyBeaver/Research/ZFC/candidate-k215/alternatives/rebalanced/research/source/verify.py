#!/usr/bin/env python3
"""Verify the compact source supplement with Python's standard library.

Checks zero-run-five source equivalence, reconstructs the N/L exchange,
replays its literal blank halt, and checks the scanner's primary positive
control. --replay-all-starts independently replays every stored scanner result.
Neither mode reruns the optional full symbolic N/L runtime derivation.
"""
from pathlib import Path
from collections import Counter,defaultdict
import argparse,hashlib,json,sys

HERE=Path(__file__).resolve().parent
PACKET=HERE.parents[1]
sys.dont_write_bytecode=True
sys.path.insert(0,str(PACKET/'code/vendor'))
import source_language as s
import build221 as b

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def write(path,data):path.parent.mkdir(parents=True,exist_ok=True);path.write_text(json.dumps(data,indent=2,sort_keys=True)+'\n')
def seed(head,ones):
    if not ones or min(ones)!=head-1:return None
    order=sorted(ones)
    if len(order)<2 or order[1]<head+64:return None
    header=order[1];p=header+1;last=order[-1];values=[]
    while p<=last:
        if p in ones or p+1 not in ones:return None
        p+=1;n=0
        while p in ones:n+=1;p+=1
        values.append(n-1)
    if len(values)<10 or any(values[i]for i in(0,2,7)):return None
    phy=(6,2,0,4,3,7,8,5,1)
    return {'registers':[values[j]for j in phy],'spares':values[9:],'ones':order}
def run(T,start,limit):
    q=start;head=0;ones=set()
    for tick in range(limit+1):
        result={'start':start,'state':q,'head':head,'steps':tick}
        if q==84:
            frame=seed(head,ones)
            if frame is not None:return {'status':'SAFE_ROOT_SEED',**result,**frame}
        if q==254:return {'status':'HALT',**result,'one_cells':sorted(ones)}
        bit=int(head in ones)
        if(q,bit)not in T:return {'status':'UNDEFINED',**result}
        w,d,z=T[q,bit]
        if bit==0 and z==q and(not ones or(d>0 and head>max(ones))or(d<0 and head<min(ones))):return {'status':'EXACT_OUTWARD_RAY',**result}
        if tick==limit:return {'status':'BOUND_EXHAUSTED',**result}
        if w:ones.add(head)
        else:ones.discard(head)
        head+=d;q=z
    raise AssertionError('unreachable')
def compare_record(T,row,limit):
    actual=run(T,row['start'],limit)
    for key in('status','steps','state','head'):assert actual[key]==row[key],(row['start'],key,actual[key],row[key])
    if row['status']=='SAFE_ROOT_SEED':
        for key in('registers','spares','ones'):assert actual[key]==row[key]
    return actual
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path);ap.add_argument('--replay-all-starts',action='store_true');ap.add_argument('--write-component-audits',action='store_true');a=ap.parse_args()
    assert __debug__ and not sys.flags.optimize,'Run without -O'
    bp=PACKET/'baseline/sites215.json';bt=PACKET/'baseline/k215.native.tm';zp=HERE/'zero5/sites.json';np=HERE/'register-swap08/sites.json';nt=HERE/'register-swap08/candidate.native.tm'
    assert sha(bp)=='17af207195179b2508bf91154cd00739374f8862207ca21b9a3cb9098aa6f5ba'
    assert sha(bt)=='9683d6ed9628e6ce407c315b08f5da3d063da94e92706f275ca0f33e8272e4b2'
    assert sha(zp)=='855b2dc7befd1dd64414eec43caf3aa7378dd522c553fe9d9a4bbffc34052ef5'
    base=json.loads(bp.read_text());zero=json.loads(zp.read_text());old=s.tree(base);new=s.tree(zero);cfg=s.graph_intervals(base)
    assert [row[1:]for row in base]==[row[1:]for row in zero]
    assert cfg==s.graph_arithmetic(base)[0]==s.graph_intervals(zero)==s.graph_arithmetic(zero)[0]
    met=s.metrics(new);assert met=={'dag_nodes':205,'leaf_occurrences':4751,'maximum_depth':45,'maximum_zero_run':5}
    za={'status':'EXACT_SOURCE_EQUIVALENCE_PASS','baseline_sha256':sha(bp),'source_sha256':sha(zp),'metrics':met,'ordered_primitive_word_equal':True,'both_complete_guarded_CFGs_equal':True,'guarded_edges':sum(len(x[1])for x in cfg),'scope':'Source equivalence only; no binary implementation or state saving is asserted.'}
    T=b.read_table(bt.read_bytes());U=b.read_table(nt.read_bytes());N=json.loads(np.read_text());expected=[[p,op,8-arg if op in('CI','CD')and arg in(0,8)else arg]for p,op,arg in base]
    assert N==expected
    ng=s.graph_intervals(N);assert ng==s.graph_arithmetic(N)[0]
    for before,after in zip(cfg,ng):
        effect,targets=before;expected_effect=effect[:]
        if len(effect)==2 and effect[1]in(0,8):expected_effect[1]=8-effect[1]
        assert after==[expected_effect,targets]
    groups,_=b.decoder_map(T,old);defaults={};wanted=defaultdict(set)
    for q,nodes in groups.items():
        for n in nodes:
            for bit,ch in enumerate(n):
                if s.leaf(ch)and ch[0]in('CI','CD')and T[q,bit][:2]==(bit,1):
                    if ch in defaults:assert defaults[ch]==T[q,bit][2]
                    defaults[ch]=T[q,bit][2]
    for q,nodes in groups.items():
        for n in nodes:
            for bit,ch in enumerate(n):
                if s.leaf(ch)and ch[0]in('CI','CD')and ch[1]in(0,8):wanted[q,bit].add((bit,1,defaults[ch[0],8-ch[1]]))
    reconstructed=dict(T)
    for key,values in wanted.items():assert len(values)==1;reconstructed[key]=next(iter(values))
    assert reconstructed==U and b.table_bytes(U)==nt.read_bytes();b.decoder_map(U,s.tree(N))
    summary=json.loads((HERE/'register-swap08/runtime-summary.json').read_text());assert summary['runtime']=='PASS'and summary['cases']==6176 and summary['table_sha256']==sha(nt)and summary['source_sha256']==sha(np)
    halt=run(U,0,100000);assert(halt['status'],halt['steps'],halt['state'],halt['head'])==('HALT',15607,254,3)
    ra={'status':'REGISTER_PERMUTATION_AND_BLANK_HALT_PASS','swap':[0,8],'source_sha256':sha(np),'native_sha256':sha(nt),'working_states':len(U)//2,'table_rebuilt_from_baseline':True,'source_register_permutation_exact':True,'ordinal_control_targets_unchanged':True,'saved_runtime_summary':{'status':summary['runtime'],'cases':summary['cases'],'case_records_retained':False,'full_derivation_rerun_in_this_check':False},'blank_halt':halt,'scope':'This table is excluded: it halts from blank, despite its separately recorded universal interpreter runtime pass.'}
    sr=json.loads((HERE/'register-swap08/all-starts.json').read_text());control=json.loads((HERE/'all-starts-control.json').read_text());states={q for q,_ in U}
    assert sr['step_limit_per_start']==control['step_limit_per_start']==1000000
    assert {x['start']for x in sr['results']}==states and len(sr['results'])==len(states)==215
    counts=Counter(x['status']for x in sr['results']);assert counts=={'EXACT_OUTWARD_RAY':210,'HALT':3,'BOUND_EXHAUSTED':2}
    assert [x['start']for x in sr['results']if x['status']=='BOUND_EXHAUSTED']==[66,94]
    initial=next(x for x in control['results']if x['start']==0);compare_record(T,initial,1000000)
    assert initial['status']=='SAFE_ROOT_SEED'and initial['steps']==95714 and initial['registers']==[4,0,0,0,0,0,0,0,0]and initial['spares']==[1]*40
    if a.replay_all_starts:
        for row in sr['results']:compare_record(U,row,1000000)
        for row in control['results']:compare_record(T,row,1000000)
    starts={'stored_count':215,'step_limit_per_start':1000000,'status_counts':dict(counts),'unresolved_starts':[66,94],'safe_seed_found':False,'primary_start0_positive_control_replayed':True,'all_stored_runs_replayed':a.replay_all_starts,'scope':'The two bounded runs remain unresolved; no proof excluding every possible start is claimed.'}
    result={'status':'SOURCE_SUPPLEMENT_CHECK_PASS','zero5':za,'register_swap':ra,'all_starts':starts}
    if a.write_component_audits:
        write(HERE/'zero5/audit.json',za);write(HERE/'register-swap08/startup-halt.json',ra);write(HERE/'all-starts-review.json',starts)
    if a.output:write(a.output,result)
    print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
