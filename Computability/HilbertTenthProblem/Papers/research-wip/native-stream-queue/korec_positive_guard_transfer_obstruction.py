#!/usr/bin/env python3
"""Fresh symbolic trace and outer formulas; never execute any saved DAG."""
import argparse
import hashlib
import json
from pathlib import Path

PINS={
 'korec_packed_repunit376.json':'3500e3426afba2ac4f83093240f4bc2ccf89cac84df1cb592853e9485a3f3b1f',
 'korec_packed_repunit376.md':'cae83d590e277a43e45f9f8b5be514ea701aa59c98bba45586ab874004fb31a2',
 'korec_packed_zero_range397.md':'ae542cedc61c0231d797b2e5a2bb9ce0e9a639ece389b81618ba871fac5c4ed4',
 'korec_packed_positive_program410.md':'4e8c02aff21d80ad5d7cb6543743214ce0c33556bc0bb5f1bf30d20068eee13e',
 'korec_packed_counter_units.md':'02cd6d353cf66db83b88b616655f59c072bf64cea8e07dc5ad37b8fd3c553437',
 'korec_packed_counter_compiler.md':'834d5622ebe1acd46d201e5b4a561e285feb47ef3870bd9274b6dd99fca5477e',
 'residue_affine_packed_history.md':'0b6c533e8ef6c26b3ed5419dbb2baa44bc1509255c4bcf5226e5f85d37683882'}
# New literal transcription of the public instruction table; these are data.
TABLE=[['D',1,1,2],['I',7,0],['I',6,3],['D',5,2,4],['D',6,5,3],
       ['I',5,6],['D',7,7,8],['I',1,4],['T',6,9,0],['D',4,0,10],
       ['D',5,11,12],['D',5,13,14],['D',2,17,18],['D',5,15,16],
       ['D',3,17,19],['I',4,10],['I',2,20],['D',4,0,21],
       ['D',0,0,17],['I',0,0],['I',3,17]]
LABELS=[1,2,2,1,1,2,1,2,3,1,3,4,1,5,1,2,2,3,1,2,2]
LOOP=[0,1,0,1,0,2,3,4,5,6,7,4,5,6,7,4,3,2,3,2,3,4,5,6,8,9,10,11,14,19]

def check(ok,msg):
    if not ok: raise ValueError(msg)
def sha(data):return hashlib.sha256(data).hexdigest()
def c(n):return (n,0,0)
def shift(a,n):return (a[0]+n,a[1],a[2])
def positive(a):return a[1]>=0 and a[2]>=0 and sum(a)>=1
def nonnegative(a):return a[1]>=0 and a[2]>=0 and sum(a)>=0
def step(state,regs,forced_zero=False):
    check(0<=state<21,'not halt')
    ins=TABLE[state];op,r=ins[:2];after=list(regs)
    if op=='I':kind='I';target=ins[2];after[r]=shift(after[r],1)
    elif forced_zero:
        check(positive(regs[r]),'forced step must actually be false')
        kind='Z';target=ins[3]
    elif regs[r]==c(0):kind='Z';target=ins[3]
    else:
        check(positive(regs[r]),'unresolved symbolic branch')
        kind=op;target=ins[2]
        if op=='D':after[r]=shift(after[r],-1)
    check(all(nonnegative(a) for a in after),'counter positivity')
    return target,after,{'state':state,'target':target,'kind':kind,'register':r,
                          'before':regs,'after':after,'forced_false_zero':forced_zero}

def eval_aff(a,A=1,X=1):return a[0]+a[1]*A+a[2]*X
def summary_int(n):
    text=hex(n)
    return {'bit_length':n.bit_length(),'hex_sha256':sha(text.encode())}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,required=True)
    ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    deps={}
    for name,pin in PINS.items():
        b=(args.root/name).read_bytes();check(sha(b)==pin,'pin '+name)
        deps[name]={'sha256':pin,'bytes':len(b),'executed_or_imported':False}
    saved=json.loads((args.root/'korec_packed_repunit376.json').read_bytes())
    parent=next(p for p in saved['records'] if p['form']=='units' and not p['program_radix'])
    old=parent['source'];deleted=['counter_M_325','-','counter_digit_mask_92','Z_sum_146']
    check(deleted in old,'literal zero clearing')
    uses=[r[0] for r in old if 'counter_M_325' in r[2:]]
    check(uses==['range_mask_93'],'one consumer')
    proposed=[[r[0],r[1]]+[('counter_digit_mask_92' if x=='counter_M_325' else x) for x in r[2:]]
              for r in old if r!=deleted]
    # Structural accounting only; no numerical or symbolic DAG interpreter.
    known=set(parent['parameters']+parent['auxiliaries']);edges={}
    for name,op,a,b in proposed:
        check(name not in known and all(type(x) is int or x in known for x in (a,b)),'proposed topology')
        known.add(name);edges[name]=[x for x in (a,b) if type(x) is str]
    live=set();todo=[parent['output']]
    while todo:
        x=todo.pop()
        if x not in live:live.add(x);todo.extend(edges.get(x,[]))
    check(live==known,'proposed liveness')
    check(len(old)==376 and len(proposed)==375,'counts')
    check(sum(r[1]=='*' for r in proposed)==143,'M count')
    check(len(parent['auxiliaries'])==50,'witness count')
    zero=c(0);X=(0,0,1);A=(0,1,0)
    start=[zero,c(2),X,zero,zero,zero,zero,zero]
    state=0;regs=start;prefix=[]
    for _ in range(59):state,regs,row=step(state,regs);prefix.append(row)
    endpoint=[c(1),c(2),X,zero,zero,zero,c(1),zero]
    check(state==0 and regs==endpoint,'exact program2 prefix')
    loop_start=[A,c(2),X,zero,zero,zero,c(1),zero]
    state=0;regs=loop_start;cycle=[]
    for s in LOOP:
        check(state==s,'cycle state');state,regs,row=step(state,regs);cycle.append(row)
    loop_end=[shift(A,1),c(2),X,zero,zero,zero,c(1),zero]
    check(state==0 and regs==loop_end,'unbounded affine cycle')
    # Follow a genuine prefix of that loop, then exactly one false zero step.
    state=0;regs=endpoint;forged=list(prefix)
    for s in LOOP[:26]:
        check(state==s,'forged legal prefix');state,regs,row=step(state,regs);forged.append(row)
    check(state==10 and regs[4]==zero and regs[2]==X,'fork configuration')
    false_before=regs
    state,regs,row=step(state,regs,True);forged.append(row)
    check(state==12,'false zero target')
    state,regs,row=step(state,regs);forged.append(row);check(state==17,'input decrement target')
    state,regs,row=step(state,regs);forged.append(row);check(state==21,'halt')
    check(len(forged)==88 and sum(r['forced_false_zero'] for r in forged)==1,'unique false zero')
    # Fresh closed-form packing, independent of every saved source array.
    edges_data=[]
    for s,ins in enumerate(TABLE):
        op,r=ins[:2]
        if op=='I':edges_data.append((s,ins[2],r,'I'))
        else:edges_data += [(s,ins[2],r,op),(s,ins[3],r,'Z')]
    check(len(edges_data)==34,'edge count')
    h=16;D=2*h;B=D**8;T=len(forged);P=B**T;J=(P-1)//(B-1)
    Es=[0]*34;W=I=L=Z=0;current=following=0
    basepower=1
    for row in forged:
        b=[eval_aff(a) for a in row['before']];a=[eval_aff(v) for v in row['after']]
        k=row['register'];kind=row['kind'];post=list(b)
        if kind in ('D','T'):post[k]-=1
        check(min(post)>=0 and max(post)<=h-3,'strict counter margin')
        edge=edges_data.index((row['state'],row['target'],k,kind));Es[edge]+=basepower
        W+=sum(x*D**j for j,x in enumerate(post))*basepower
        if kind in ('I','T'):I+=D**k*basepower
        if kind in ('D','T'):L+=D**k*basepower
        if kind=='Z':Z+=D**k*basepower
        code=lambda s:0 if s==21 else LABELS[s]*D**TABLE[s][1]
        current+=code(row['state'])*basepower;following+=code(row['target'])*basepower
        expected_after=[post[j]+int(kind in ('I','T') and j==k) for j in range(8)]
        check(a==expected_after,'all counter transitions')
        basepower*=B
    Y=sum(eval_aff(a)*D**j for j,a in enumerate(regs));initial=2*D+D**2
    V=sum(D**j for j in range(8));R0=(h-1)*V*J;Rstar=(h-1)*(V*J-Z)
    gamma=R0-W-2
    check(sum(Es)==J and all(e&J==e for e in Es),'selector typing')
    check(W&R0==W and W&Rstar!=W,'precise missing zero guard')
    check(B*(W+I)+initial==W+L+P*Y,'counter transport')
    check(B*following+D==current,'control transport')
    check(gamma>0 and R0-(W+1+gamma)==1,'range unit')
    Cpack=sum(e*P**j for j,e in enumerate(Es));Cmask=J*sum(P**j for j in range(34))
    H=Cpack+P**34*W;M=Cmask+P**34*R0;Q=B*P**35
    check(0<=H<M<Q and H&M==H,'full relaxed AND')
    q=16*Q;fields=[16*(Q-M)-15,4,16*(M-H)+2,16*H+8]
    check(min(fields)>0 and sum(fields)==q-1,'positive complete native fields')
    check((q&(q-1))==0,'dyadic scale')
    lost=W-(W&Rstar);bad_value=eval_aff(false_before[5])
    check(lost==bad_value*D**5*B**85,'one missing zero cell')
    # Two legal local vector guards: zero then increment of a zero counter.
    # This is fresh scalar algebra, not any saved source evaluation.
    local_t=[-1,0];local_G=[0,2];test_radix=8
    check(all(t*g==0 for t,g in zip(local_t,local_G)),'valid componentwise guards')
    packed_t=sum(t*test_radix**j for j,t in enumerate(local_t))
    packed_G=sum(g*test_radix**j for j,g in enumerate(local_G))
    check(packed_t*packed_G==-16,'convolution obstruction')
    result={'schema':'korec-positive-guard-transfer-obstruction-v1','helper_sha256':sha(Path(__file__).read_bytes()),
      'dependencies':deps,'table':TABLE,'labels':LABELS,'edges':edges_data,
      'symbolic_basis':['constant','A','X'],'symbolic_domain':'A>=1, X>=1 integers',
      'true_prefix59':prefix,'cycle30':cycle,'cycle_start':loop_start,'cycle_end':loop_end,
      'forged_trace88':forged,'false_zero_before':false_before,'false_zero_time':85,
      'source_binding':{'parent_source_sha256_metadata':parent['source_sha256'],'removed_row':deleted,
          'consumer':uses,'replacement_range_row':next(r for r in proposed if r[0]=='range_mask_93'),
          'retained_Z_consumers':[r[0] for r in proposed if 'Z_sum_146' in r[2:]],
          'old_count':376,'rejected_count':375,'M':143,'A':232,'positive_witnesses':50,
          'all_retained_rows_ports_live':True,'arrays_evaluated':False},
      'outer':{'program':2,'input':1,'h':h,'height_slack':h-3,'D':D,'B':B,'T':T,
          'edge_hats':[hex(e+1) for e in Es],'W_hat':hex(W+1),'Y_hat':hex(Y+1),
          'global_slack':hex(gamma),'false_zero_counter':bad_value,'final_counters':[eval_aff(a) for a in regs],
          'large_values':{name:summary_int(v) for name,v in [('P',P),('J',J),('W',W),('R0',R0),('Rstar',Rstar),('H',H),('M',M),('Q',Q)]}},
      'checks':{'genuine_symbolic_steps':89,'forged_steps':88,'false_zero_steps':1,
          'counter_transport':True,'control_transport':True,'all_selector_lanes':True,'relaxed_range_lane':True,
          'original_zero_range_lane':False,'complete_relaxed_AND':True,'all_native_fields_positive':True},
      'direct_guard_word_product_counterexample':{'radix':test_radix,'t_digits':local_t,'G_digits':local_G,
          'each_digit_product':0,'word_product':-16,'legal_program':'zero-test zero counter, then increment it'},
      'scope':{'predecessor_execution_import':False,'saved_or_mutated_array_evaluation':False,
          'new_symbolic_interpreter_and_outer_formulas_only':True,'native_Pell_values_materialized':False,
          'native_extension':'mathematical theorem in companion note','valid_compiler_reduction':False,
          'counterexample_is_actual_U21':True},'status':'PASS_OBSTRUCTION'}
    with args.output.open('x',encoding='utf-8') as f:json.dump(result,f,sort_keys=True,indent=2);f.write('\n')
    print(json.dumps({'status':result['status'],'prefix':59,'cycle':30,'forged':88,
                      'false_counter':bad_value,'final_counters':result['outer']['final_counters'],
                      'rejected_source':375,'P_bits':P.bit_length(),'Q_bits':Q.bit_length()}))

if __name__=='__main__':main()
