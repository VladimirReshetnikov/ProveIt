from pathlib import Path
import sys,json,gzip,hashlib
R=Path('/home/codex/.codex/worktrees/ec20/Proofs')
sys.path.insert(0,str(R/'Computability/BusyBeaver/Research/ZFC/k218-quantifier-stability/pricing'))
import source_language as s
import build221 as b
P=Path(__file__).resolve().parent;O=P/'run2';O.mkdir(exist_ok=False)
C=R/'Computability/BusyBeaver/Research/ZFC/candidate-k217';B=R/'Computability/BusyBeaver/Research/ZFC/candidate-k219'
H=R/'SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/intake192-fresh'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();load=lambda p:json.loads(p.read_text())
assert sha(C/'k217.native.tm')=='b235f7d0403460ff00d274d7d030fec6ba3562127035165e3ead555237c83088'
assert load(H/'actual-review.json')['status']=='INDEPENDENT_FRESH_RECORD_REVIEW_PASS'
T=b.read_table((C/'k217.native.tm').read_bytes());oldrows=load(C/'sites217.json');old=s.tree(oldrows);base=s.tree(load(B/'sites219.json'))
root='111111';previous=s.subtree(old,root);assert previous==s.subtree(base,'111111')
assert len(s.sites(previous))==26 and s.boundary(previous)==(0,0,False)
newnode=(('CD',4),(('CI',5),('CC',2)));assert s.boundary(newnode)==(0,0,False)
new=s.replace(old,root,newnode);nr=s.sites(new);N=dict(T);assert N[164,1]==(1,1,98);N[164,1]=(1,1,130)
og,op=b.decoder_map(T,old);ng,np=b.decoder_map(N,new)
oldstates={p:q for q,ps in op.items()for p in ps};newstates={p:q for q,ps in np.items()for p in ps}
assert op[164]==['11111']
assert newnode in og[130];reference=next(p for p in op[130]if s.subtree(old,p)==newnode)
prior=lambda p:reference+p[len(root):]if p.startswith(root)else p
for p,q in newstates.items():assert oldstates[prior(p)]==q,(p,q,prior(p))
oldleaves={p:(o,a)for p,o,a in oldrows}
for p,o,a in nr:
 p0=prior(p);assert oldleaves[p0]==(o,a)
 assert N[newstates[p[:-1]],int(p[-1])]==T[oldstates[p0[:-1]],int(p0[-1])]
indices=[i for i,(p,o,a)in enumerate(oldrows)if p.startswith(root)];lo,hi=min(indices),max(indices)+1
assert indices==list(range(lo,hi))and hi-lo==26
assert nr[lo:lo+3]==s.sites(newnode,root)
g0=s.graph_arithmetic(oldrows)[0];g1=s.graph_arithmetic(nr)[0];assert g0==s.graph_intervals(oldrows)and g1==s.graph_intervals(nr)
def target(i):
 if lo<=i<hi:assert i==lo;return lo
 return i if i<lo else i-23
edges=0
for i,(effect,targets)in enumerate(g0):
 if lo<=i<hi:continue
 j=i if i<lo else i-23;assert g1[j]==[effect,[target(t)for t in targets]],(i,j);edges+=len(targets)
boot=json.loads(gzip.decompress((H/'runtime/startup.json.gz').read_bytes()));q=h=0;ones=set()
for tq,th,rd,w,d,z in boot['trace']:
 assert(tq,th,rd)==(q,h,int(h in ones));assert T[q,rd]==N[q,rd]==(w,d,z)
 if w:ones.add(h)
 else:ones.discard(h)
 q,h=z,h+d
assert len(boot['trace'])==312617 and(q,h,sorted(ones))==(boot['state'],boot['head'],boot['one_cells'])
assert len(N)==434 and len({q for q,bit in N})==217
(O/'candidate.native.tm').write_bytes(b.table_bytes(N));(O/'sites.json').write_bytes(s.compact(nr))
result={'status':'CACHE_RETURN_217_SOURCE_AND_STARTUP_PASS','parent_table_sha256':sha(C/'k217.native.tm'),'table_sha256':sha(O/'candidate.native.tm'),'source_sha256':sha(O/'sites.json'),'working_states':217,'rows':434,'metrics':s.metrics(new),'guards':sum(2 if o=='CD'else 1 for p,o,a in nr),'changed_row':{'row':[164,1],'old':T[164,1],'new':N[164,1]},'source_replacement':{'path':root,'old_leaves':26,'new_leaves':3,'old_interval':[lo,hi],'existing_new_role':130,'reference_path':reference},'expected_decoder_bindings':len(newstates),'complete_leaf_action_bindings':len(nr),'all_retained_CFG_edges':edges,'decoder_states_before':len(og),'decoder_states_after':len(ng),'startup_steps':len(boot['trace']),'entire_startup_trace_unchanged':True,'scope':'Exact source replacement, whole retained CFG and expected decoder/leaf bindings, complete prior blank trace. Cache-return command contract and compiler transfer are separate ordinary proofs. No new full runtime, <=216 table, or kernel claim.'}
(O/'composition.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
