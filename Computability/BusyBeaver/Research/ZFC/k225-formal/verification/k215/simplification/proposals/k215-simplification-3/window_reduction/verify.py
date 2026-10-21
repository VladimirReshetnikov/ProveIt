"""Independent standard-library checker for finite local-window certificates.
Checks pins, all initial windows, inductive closure, and exact leastness by a
separate BFS. Window successors are defined as explicit lists of tape bits,
not by the C++ generator's integer-shift formulas.
"""
from pathlib import Path
import collections,hashlib,json
if not __debug__:raise SystemExit('Run without -O or -OO: checks are mandatory.')
D=Path(__file__).resolve().parent

def require(p,message):
 if not p:raise ValueError(message)

def parse(raw):
 rows={};start=None
 for line in raw.decode().splitlines():
  if line.startswith('#! start '):start=int(line.split()[-1])
  if not line or line.startswith('#'):continue
  q,b,w,d,z=line.split();q,b,w,z=map(int,(q,b,w,z))
  require((q,b)not in rows and b in (0,1)and w in (0,1)and d in ('L','R'),'malformed row')
  rows[q,b]=w,d,z
 return rows,start

successors={}
for r in range(1,6):
 W=2**(2*r+1);cache={}
 for v in range(W):
  window=[(v//(2**i))%2 for i in range(2*r+1)]
  for write in (0,1):
   for direction in ('L','R'):
    changed=window.copy();changed[r]=write
    out=[]
    for exterior in (0,1):
     shifted=changed[1:]+[exterior]if direction=='R'else[exterior]+changed[:-1]
     out.append(sum(bit*2**i for i,bit in enumerate(shifted)))
    cache[v,write,direction]=tuple(out)
 successors[r]=cache

meta=json.loads((D/'inputs.json').read_text());summaries=[];merges={}
for name,m in meta.items():
 raw=(D/'inputs'/f'{name}.native.tm').read_bytes()
 require(hashlib.sha256(raw).hexdigest()==m['sha256'],'table pin')
 table,start=parse(raw);labels=sorted({q for q,b in table});index={q:i for i,q in enumerate(labels)}
 require(labels==m['native_labels']and start==m['start_native']==0,'state binding')
 require(len(labels)==215 and len(table)==430 and all((q,b)in table for q in labels for b in(0,1)),'table census')
 require({z for w,d,z in table.values()}-set(labels)=={254},'halt census')
 for r in range(1,6):
  W=2**(2*r+1);N=len(labels)*W;cache=successors[r]
  for arbitrary in (0,1):
   stem=D/name/f'r{r}_a{arbitrary}';receipt=json.loads(stem.with_suffix('.json').read_text());rawbits=stem.with_suffix('.bits').read_bytes()
   require(len(rawbits)==(N+7)//8,'bitset size')
   seen=bytearray((rawbits[i//8]>>(i%8))&1 for i in range(N))
   initial=[index[start]*W+v for v in(range(W)if arbitrary else(0,))]
   require(all(seen[i]for i in initial),'initial inclusion')
   edgecount=0;halt=False
   for ident,live in enumerate(seen):
    if not live:continue
    qi,v=divmod(ident,W);w,d,z=table[labels[qi],(v//2**r)%2]
    if z==254:halt=True;continue
    for nv in cache[v,w,d]:require(seen[index[z]*W+nv],'inductive closure');edgecount+=1
   # Independent exact reachability proves the supplied closed set is least.
   found=bytearray(N);queue=[]
   for i in initial:found[i]=1;queue.append(i)
   for ident in queue:
    qi,v=divmod(ident,W);w,d,z=table[labels[qi],(v//2**r)%2]
    if z==254:continue
    for nv in cache[v,w,d]:
     nid=index[z]*W+nv
     if not found[nid]:found[nid]=1;queue.append(nid)
   require(found==seen,'certificate is not exact least fixed point')
   statecounts=[];deadstates=[];deadrows=[]
   for qi,q in enumerate(labels):
    live=[v for v in range(W)if seen[qi*W+v]];statecounts.append(len(live))
    if not live:deadstates.append(q)
    for b in (0,1):
     if not any((v//2**r)%2==b for v in live):deadrows.append([q,b])
   require(receipt['reachable_abstract_configurations']==len(queue)and receipt['state_window_counts']==statecounts,'census mismatch')
   require(receipt['reachable_state_count']==215-len(deadstates)and receipt['reachable_read_row_count']==430-len(deadrows),'row/state census')
   require(receipt['dead_states_dense']==[index[q]for q in deadstates]and receipt['dead_rows_dense']==[[index[q],b]for q,b in deadrows],'dead rows mismatch')
   require(receipt['halt_may_be_reached']==halt,'halt abstract coverage')
   summaries.append({'machine':name,'radius':r,'initial_mode':'arbitrary_window'if arbitrary else'blank_window','domain':N,'reachable_configurations':len(queue),'reachable_states':215-len(deadstates),'reachable_read_rows':430-len(deadrows),'dead_states':deadstates,'dead_rows':deadrows,'closure_edges_checked':edgecount,'certificate_sha256':hashlib.sha256(rawbits).hexdigest()})
 # With every row live, safe pair merging must respect both literal actions.
 compatible=[]
 for i,q in enumerate(labels):
  for p in labels[i+1:]:
   def action(s,b):
    w,d,z=table[s,b];return w,d,q if z==p else z
   if all(action(q,b)==action(p,b)for b in(0,1)):compatible.append([q,p])
 # More general exact step-for-step state bisimulation by partition refinement.
 groups={q:0 for q in labels};groups[254]=-1;rounds=0
 while True:
  classes={};new={254:-1}
  for q in labels:
   sig=tuple((table[q,b][0],table[q,b][1],groups[table[q,b][2]])for b in(0,1))
   if sig not in classes:classes[sig]=len(classes)
   new[q]=classes[sig]
  rounds+=1
  if all(new[q]==groups[q]for q in labels):break
  groups=new
 partition=collections.defaultdict(list)
 for q in labels:partition[new[q]].append(q)
 merges[name]={'safe_single_pair_merges':compatible,'bisimulation_classes':len(partition),'nontrivial_bisimulation_classes':[v for v in partition.values()if len(v)>1],'refinement_rounds':rounds}
 print(name,'PASS: 10 exact least fixed points,',len(compatible),'pair merges,',len(partition),'bisimulation classes',flush=True)
report={'status':'INDEPENDENT_INDUCTIVE_CLOSURE_AND_LEASTNESS_PASS','machines':len(meta),'certificates_checked':len(summaries),'window_radii':[1,2,3,4,5],'unknown_exterior_bits':'Both0 and1 at every shift, without assuming virgin or previously unseen cells are zero.','domains':summaries,'row_compatible_merge_checks':merges,'interpretation':'Finite abstract reachability, not bounded concrete execution. Each certificate includes all initial windows and is closed under both nondeterministic exterior choices. Independent BFS proves leastness in the specified finite domain. No assertion of reachability of any concrete machine configuration follows from abstract membership.'}
(D/'verification.json').write_text(json.dumps(report,indent=2)+'\n')
print('ALL CERTIFICATES PASS',flush=True)
