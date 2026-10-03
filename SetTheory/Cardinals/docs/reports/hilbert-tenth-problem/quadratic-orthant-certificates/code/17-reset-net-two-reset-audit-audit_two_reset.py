#!/usr/bin/env python3
"""Independent finite audit. Never expands the enormous accepting microtrace.
Reads audited source exports, reconstructs all 8,408 prime-macro rows, checks
small literal cases including intermediate total mass, and replays 328 virtual
instructions with exact proved counts. All outputs remain beside this script.
"""
from pathlib import Path
from collections import Counter
import json, hashlib
OUT=Path(__file__).resolve().parent
SRC=OUT.parent/'two-counter'/'source'
def read(n): return json.loads((SRC/n).read_text())
def save(n,d): (OUT/n).write_text(json.dumps(d,indent=2)+'\n')
P=read('literal2.json'); V=read('virtual3.json'); C=read('macro_certificates.json'); EX=read('accepting_example.json')
pr=P['rows']; vr=V['rows']; expected={}; shapes=Counter()
resolve=lambda d: P['virtual_cuts'][d] if d!='HALT' else 'HALT'
for c in C['prime_macros']:
    lab=c['virtual_label']; op=c['op']; p=c['prime']; a=c['prefix']; ds=list(map(resolve,c['destinations']))
    assert vr[lab]==[op,(2,3,5).index(p),*c['destinations']]
    assert P['virtual_cuts'][lab]==a+('drain' if op=='ADD' else 'rem0')
    r={}
    if op=='ADD':
        r[a+'drain']=['SUB',0,a+'mul0',a+'restore']
        for j in range(p): r[a+f'mul{j}']=['ADD',1,a+(f'mul{j+1}' if j+1<p else 'drain')]
        r[a+'restore']=['SUB',1,a+'put',ds[0]]
        r[a+'put']=['ADD',0,a+'restore']
        assert len(r)==p+3
    else:
        for j in range(p):
            r[a+f'rem{j}']=['SUB',0,a+(f'rem{j+1}' if j+1<p else 'group'),a+('quo' if j==0 else f'r{j}_drain')]
        r[a+'group']=['ADD',1,a+'rem0']
        r[a+'quo']=['SUB',1,a+'qput',ds[0]]
        r[a+'qput']=['ADD',0,a+'quo']
        for j in range(1,p):
            b=a+f'r{j}_'
            r[b+'drain']=['SUB',1,b+'put0',b+'tail0']
            for k in range(p): r[b+f'put{k}']=['ADD',0,b+(f'put{k+1}' if k+1<p else 'drain')]
            for k in range(j): r[b+f'tail{k}']=['ADD',0,b+f'tail{k+1}' if k+1<j else ds[1]]
        assert len(r)==(3*p*p+p+4)//2
    assert not set(r)&set(expected)
    expected.update(r); shapes[(op,p)]+=1
assert expected==pr
assert set(P['virtual_cuts'])==set(vr)
assert len(pr)==8408 and P['entry']==P['virtual_cuts'][V['entry']]
ops=Counter(row[0] for row in pr.values()); reset_targets=Counter(row[1] for row in pr.values() if row[0]=='SUB')
assert ops=={'ADD':6068,'SUB':2340} and reset_targets=={0:1170,1:1170}

def macro_counts(op,p,N):
    Q,r=divmod(N,p)
    if op=='ADD': return (p*N,2*p*N,(p+1)*N,2,0)
    if r==0: return (Q,2*Q,N+Q,2,0)
    return (N,N+Q,N+Q,2,1)

# Supplementary small executions of the literal table, not an all-input claim.
reps={}
for c in C['prime_macros']: reps.setdefault((c['op'],c['prime']),c)
small_cases=small_steps=0
for (op,p),c in reps.items():
    for N in range(129):
        want,aa,sp,sz,arm=macro_counts(op,p,N)
        lab=P['virtual_cuts'][c['virtual_label']]; target=resolve(c['destinations'][arm]); A=N; B=0; n=0; counts=Counter(); peak=N
        while True:
            x,i,*ds=pr[lab]
            if x=='ADD':
                counts['ADD']+=1
                if i==0: A+=1
                else: B+=1
                lab=ds[0]
            elif (A,B)[i]:
                counts['SUB_positive']+=1
                if i==0:A-=1
                else:B-=1
                lab=ds[0]
            else: counts['SUB_zero']+=1; lab=ds[1]
            peak=max(peak,A+B);n+=1
            assert A+B<=max(N,want)
            if lab==target and B==0:break
            assert n<100000
        assert (A,B,n)==(want,0,aa+sp+sz)
        assert (counts['ADD'],counts['SUB_positive'],counts['SUB_zero'])==(aa,sp,sz)
        assert peak==max(N,want)
        small_cases+=1;small_steps+=n

# Exact 328-virtual-step replay, using the audited macro shapes and loop counts.
lab=V['entry']; regs=[6,0,0]; value=64; h=aa=sp=sz=0; peak=64; cuts=[]; aggregate={}
while lab!='HALT':
    op,i,*ds=vr[lab]; p=(2,3,5)[i]
    new,add,pos,zero,arm=macro_counts(op,p,value)
    if op=='SUB': assert arm==(0 if regs[i] else 1)
    cuts.append({'virtual_step':len(cuts),'label':lab,'registers_before':regs[:], 'A_before':value,'A_after':new,'physical_steps_before':h,'physical_step_count':add+pos+zero,'physical_ADD':add,'physical_SUB_positive':pos,'physical_SUB_zero':zero,'microstep_total_peak':max(value,new)})
    key=f'{op}_p{p}_arm{arm}'
    z=aggregate.setdefault(key,{'virtual_steps':0,'physical_steps':0,'ADD':0,'SUB_positive':0,'SUB_zero':0})
    for k,v in [('virtual_steps',1),('physical_steps',add+pos+zero),('ADD',add),('SUB_positive',pos),('SUB_zero',zero)]:z[k]+=v
    if op=='ADD': regs[i]+=1
    elif regs[i]: regs[i]-=1
    lab=ds[arm];value=new
    assert value==2**regs[0]*3**regs[1]*5**regs[2]
    h+=add+pos+zero;aa+=add;sp+=pos;sz+=zero;peak=max(peak,value)
    assert len(cuts)<=1000
F=value; initial_mass=64
assert (len(cuts),h,aa,sp,sz,peak,F)==(328,738579314485258247,369289657242717337,369289657242540254,656,59604644775390625,177147)
for k,v in [('physical_instructions',h),('physical_ADD',aa),('physical_SUB_positive',sp),('physical_SUB_zero',sz),('largest_A_at_virtual_cuts',peak)]:assert EX[k]==v
assert aa-sp==F-initial_mass
Nmin=h+F-initial_mass+2*peak+4
assert Nmin==857788604036216584
assert Nmin-h-3*F+initial_mass-2*(peak-F)-4==0
save('accepting_macro_trace.json',{'method':'328 virtual steps only; exact physical counts and intermediate-mass bounds from fully audited literal macro shapes','raw_A':64,'steps':cuts,'operation_aggregates':aggregate})

# Exact positive-domain boundary: raw zero loops on two failed tests forever.
l=P['entry']; zero_cycle=[]
for _ in range(2):
    op,i,*ds=pr[l];assert op=='SUB';zero_cycle.append(l);l=ds[1]
assert l==P['entry']

# Literal, finite reset net. Unit arcs represented by place IDs, no compression.
controls=list(pr)+['HALT']; places=[{'id':j,'kind':'source_control','label':q} for j,q in enumerate(controls)]
pids={q:j for j,q in enumerate(controls)}
def addplace(label,kind):
    q=len(places);places.append({'id':q,'kind':kind,'label':label});return q
X=[addplace(f'counter_{i+1}','counter') for i in range(2)]
reserve=addplace('reserve','resource');budget=addplace('budget','resource');start=addplace('START','control')
clean=[pids['HALT'],addplace('CLEAN_2','control')];drain=addplace('DRAIN','control');done=addplace('DONE','control')
trans=[]
def t(label,ins,outs,resets=()):
    assert len(ins)==len(set(ins)) and len(outs)==len(set(outs))
    trans.append({'id':len(trans),'label':label,'input':ins,'output':outs,'reset':list(resets)})
t('pump',[start],[start,reserve,budget]);t('enter',[start],[pids[P['entry']]])
for q,(op,i,*ds) in pr.items():
    if op=='ADD':t(q+':ADD',[pids[q],reserve],[pids[ds[0]],X[i]])
    else:
        t(q+':positive',[pids[q],X[i]],[pids[ds[0]],reserve]);t(q+':zero',[pids[q]],[pids[ds[1]]],[X[i]])
for i in range(2):
    t(f'cleanup_{i+1}',[clean[i],X[i]],[clean[i],reserve]);t(f'advance_{i+1}',[clean[i]],[clean[i+1] if i+1<2 else drain])
t('drain',[drain,reserve,budget],[drain]);t('finish',[drain],[done])
ledger={'source_instruction_rows':len(pr),'source_ADD':ops['ADD'],'source_SUB':ops['SUB'],'source_branches':ops['ADD']+2*ops['SUB'],'places':len(places),'transitions':len(trans),'ordinary_input_arcs':sum(len(z['input']) for z in trans),'ordinary_output_arcs':sum(len(z['output']) for z in trans),'reset_arcs':sum(len(z['reset']) for z in trans),'distinct_resettable_places':len({p for z in trans for p in z['reset']})}
ledger['ordinary_arcs']=ledger['ordinary_input_arcs']+ledger['ordinary_output_arcs']
assert ledger=={'source_instruction_rows':8408,'source_ADD':6068,'source_SUB':2340,'source_branches':10748,'places':8417,'transitions':10756,'ordinary_input_arcs':19168,'ordinary_output_arcs':19168,'reset_arcs':2340,'distinct_resettable_places':2,'ordinary_arcs':38336}
assert all(not set(z['reset'])&(set(z['input'])|set(z['output'])) for z in trans)
save('two_reset_net.json',{'semantics':'Unit ordinary arcs; reset arcs clear listed counter places. Target is exactly one DONE token and zero everywhere else.','places':places,'transitions':trans,'initial_marking':{'parameter':'raw_A','domain':'natural; positive values have the universal decoding interface','fixed_tokens':[[start,1]],'parameter_tokens':[[X[0],'raw_A'],[budget,'raw_A']]},'target_marking':[[done,1]],'ledger':ledger})
receipt={'status':'passed','source_hashes':{n:hashlib.sha256((SRC/n).read_bytes()).hexdigest() for n in ['literal2.json','virtual3.json','PROOF.md','macro_certificates.json','accepting_example.json']},'literal_rows_exactly_reconstructed':len(expected),'prime_macro_count':sum(shapes.values()),'prime_macro_shapes':{f'{op}_p{p}':n for (op,p),n in sorted(shapes.items())},'supplementary_literal_cases':small_cases,'supplementary_literal_steps':small_steps,'net_ledger':ledger,'accepting_example':{'raw_A':64,'source_virtual_steps':len(cuts),'source_physical_steps_h':h,'source_ADD_steps':aa,'source_positive_SUB_steps':sp,'source_zero_SUB_steps':sz,'initial_mass_B':initial_mass,'final_mass_F':F,'peak_total_mass_M':peak,'minimum_pumps':peak-initial_mass,'terminal_peak_slack':peak-F,'minimum_net_duration':Nmin,'possible_durations':'857788604036216584 + 2q, q any natural'},'raw_zero':{'accepted':False,'physical_period':2,'cycle':zero_cycle,'registers':[0,0]},'canonical_minimum_certificate':{'external_time_parameter':'h >= 1 counts physical source instructions','witnesses':'29906*h','affine_squares':'5*h+2','nonnegative_quadratic_products':'10749*h','degree':2,'duration_row':'N-h-3F+raw_A-2v_h-4'},'limitations':['No complete A=64 physical microtrace is replayed or materialized.','No huge fixed-time polynomial is instantiated.','No fixed-arity unknown-time Diophantine equation or MRDP novelty is claimed.']}
save('audit_receipt.json',receipt)
print(json.dumps(receipt,indent=2))
