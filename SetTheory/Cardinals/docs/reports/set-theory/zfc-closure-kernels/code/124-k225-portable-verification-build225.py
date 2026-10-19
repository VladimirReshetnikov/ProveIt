from pathlib import Path
import sys,json,hashlib,collections
ROOT=Path(__file__).resolve().parents[1];P=ROOT/'baseline226';Q=ROOT/'tools';sys.path.insert(0,str(P/'verification'));import reconstruct227 as c
sys.path.insert(0,str(Q));import verify_state_fold as v
import argparse
ap=argparse.ArgumentParser(description='Replay the exact source-aware K226 to K225 composition.');ap.add_argument('--output-dir',type=Path,required=True);args=ap.parse_args();OUT=args.output_dir;OUT.mkdir(parents=True,exist_ok=True)
mp={int(k):x for k,x in json.loads((P/'source/legacy_state_map.json').read_text())['k230_to_old'].items()};mp[254]=254
mi={v:k for k,v in mp.items()};mi[254]=254
c.require(c.sha((P/'machines/k226_old.tm').read_bytes())=='30082fe31158b8ae049a1bf15f56acffaae71f9031642e6fa7ab75555e466be4','Pinned226 table mismatch')
c.require(c.sha((P/'source/sites226.json').read_bytes())=='200cfe32d7b16587bd56667650e5eb192c9e392a3f4764b3ec4ca4705a074f89','Pinned226 source mismatch')
old=c.read_table((P/'machines/k226_old.tm').read_bytes());t={(mi[q],b):(w,d,mi[z])for(q,b),(w,d,z)in old.items()}
root=c.tree(json.loads((P/'source/sites226.json').read_text()));basegraph,source_checks=c.graph_arithmetic(c.sites(root));history=[]

def mapping(t,root):
 qs=collections.defaultdict(set);paths=collections.defaultdict(list)
 def walk(n,p,q):
  if c.leaf(n):return
  qs[q].add(n);paths[q].append(p)
  for b in (0,1):
   if c.leaf(n[b]):continue
   mem={i:int(x)for i,x in enumerate(p+str(b))};mem[-1]=1;orig=mem.copy();h=len(p);state=q
   for k in range(100):
    if h==len(p)+1:break
    c.require(h in mem,'decoder outside known path')
    w,d,state=t[state,mem[h]];mem[h]=w;h+=d
   c.require(mem==orig and h==len(p)+1,'prefix decoder mismatch')
   walk(n[b],p+str(b),state)
 walk(root,'',84)
 return qs,paths

for q,r,direction in [(169,136,'right'),(170,169,'right'),(169,154,'left'),(159,118,'right')]:
 qs,paths=mapping(t,root);c.require(len(qs[q])==len(qs[r])==1,'ambiguous source role');n=next(iter(qs[q]));npaths=paths[q]
 bit=0 if direction=='right'else 1;c.require(qs[r]=={n[bit]},'wrong source child');c.require(c.ports(t,r)==[(q,bit,bit,1)],'shared rotation inner')
 c.require(all(t[s,b][:2]==(b,1)for s in(q,r)for b in(0,1)),'nonpure rotation')
 before={str((s,b)):t[s,b]for s in(q,r)for b in(0,1)}
 if direction=='right':
  (a,b),cc=n;nn=(a,(b,cc));ra=t[r,0][2];rb=t[r,1][2];qc=t[q,1][2]
  t[q,0]=(0,1,ra);t[q,1]=(1,1,r);t[r,0]=(0,1,rb);t[r,1]=(1,1,qc)
 else:
  a,(b,cc)=n;nn=((a,b),cc);qa=t[q,0][2];rb=t[r,0][2];rc=t[r,1][2]
  t[q,0]=(0,1,r);t[q,1]=(1,1,rc);t[r,0]=(0,1,qa);t[r,1]=(1,1,rb)
 c.require(all(c.boundary(k)==(0,0,False)for k in(a,b,cc)),'unclosed chunk')
 for p in npaths:root=c.replace(root,p,nn)
 rows=c.sites(root);c.require(c.graph_arithmetic(rows)[0]==basegraph==c.graph_intervals(rows),'source graph changed')
 history.append(dict(outer=q,inner=r,direction=direction,paths=npaths,before=before,after={str((s,b)):t[s,b]for s in(q,r)for b in(0,1)},metrics=c.metrics(root),closed_chunk_sizes=[len(c.sites(x))for x in(a,b,cc)]))
# Merging zero-tag229 into one-tag152 remains valid even though152 has a
# left-moving caller: inductive bit facts establish its preceding one.
facts,checks=v.bit_invariant(t,0,8)
c.require(facts[229].get(-1)==0 and facts[152].get(-1)==1,'context tags absent')
keep,drop,h0,h1=152,229,159,170
for read,h in [(0,h0),(1,h1)]:
 for tag,q in [(0,drop),(1,keep)]:
  w,d,z=t[h,tag];c.require((w,d)==(tag,1) and t[z,read]==t[q,read],'helper macro mismatch')
final={(q,b):(w,d,keep if z==drop else z)for(q,b),(w,d,z)in t.items()if q!=drop};final[keep,0]=(0,-1,h0);final[keep,1]=(1,-1,h1)
c.require(len(final)==450,'state count');c.require(c.metrics(root)['maximum_zero_run']==6,'zero-run bound')
legacy={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in final.items()};rotlegacy={(mp[q],b):(w,d,mp[z])for(q,b),(w,d,z)in t.items()}
c.require(c.sha(c.encode(legacy))=='6aab1f0f98b3764ba43c05bd6aad0d6d77a7dbac576ab733c8b02664b4b04fc2','Pinned225 output table mismatch')
c.require(c.sha(c.compact(c.sites(root)))=='86b28af08e646eb7da8b822f63a03173ef5182e5a2ebc0404008e1b2af41b55b','Pinned225 output source mismatch')
labels=sorted({q for q,b in final});renumber={q:n for n,q in enumerate(labels)};renumber[254]=225
canonical={(renumber[q],b):(w,d,renumber[z])for(q,b),(w,d,z)in final.items()}
(OUT/'k225.tm').write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(canonical.items())))
c.dump(OUT/'renumbering225.json',dict(k_to_canonical=renumber,canonical_to_k=labels+[254],start=0,halt=225,dispatcher=renumber[84],deleted_original_k_labels=sorted(set(range(230))-set(labels))))
(OUT/'rotated226.tm').write_bytes(c.encode(rotlegacy));(OUT/'candidate225.tm').write_bytes(c.encode(legacy));(OUT/'sites225.json').write_bytes(c.compact(c.sites(root)))
(OUT/'candidate225.klabels.tm').write_text('#! start 0\n'+''.join(f'{q} {b} {w} {"R"if d==1 else"L"} {z}\n'for(q,b),(w,d,z)in sorted(final.items())))
c.dump(OUT/'construction.json',dict(status='EXACT_SOURCE_COMPOSITION_AND_LOCAL_HELPERS_PASS',working_states=225,rows=450,source_metrics=c.metrics(root),source_no_stray_checks=source_checks,guarded_cases=sum(2 if op=='CD' else 1 for p,op,arg in c.sites(root)),local_invariant_row_checks=checks,rotations=history,fold=dict(keep=keep,drop=drop,helper0=h0,helper1=h1,zero_tag_state=drop,one_tag_state=keep,zero_tag_fact=facts[drop],one_tag_fact=facts[keep]),source_sha256=c.sha((OUT/'sites225.json').read_bytes()),table_sha256=c.sha((OUT/'candidate225.tm').read_bytes()),input_table_sha256=c.sha((P/'machines/k226_old.tm').read_bytes()),input_source_sha256=c.sha((P/'source/sites226.json').read_bytes()),proof_scope='Source CFG and exact helper identities; full runtime and startup independent.'))
b1=c.boot(old,409835);b2=c.boot(legacy,409835);c.require(b1['one_cells']==b2['one_cells'],'startup complete tape mismatch');c.dump(OUT/'startup225.json',dict(status='EXACT_COMPLETE_STARTUP_PASS',baseline=b1,candidate=b2))
proof=v.prove(rotlegacy,legacy,95,95,mp[keep],mp[drop],0,None,8,65,20000);c.dump(OUT/'local_fold225.json',proof);print(json.dumps(dict(states=225,metrics=c.metrics(root),fold_status=proof['status'],table_sha256=c.sha(c.encode(legacy))),indent=2),flush=True)
