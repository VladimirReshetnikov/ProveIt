#!/usr/bin/env python3
from pathlib import Path
import sys,itertools,json,hashlib
if not __debug__:raise RuntimeError('Assertions required')
OUT=Path(__file__).resolve().parent;D=OUT.parent/'arithmetic_core';sys.path.insert(0,str(D));sys.path.insert(0,str(OUT.parent/'native_copier'))
import compare_biased_counter as C,compare_biased_counter27 as V,biased_reference_copy18 as F,biased_reference_copy19 as B

def parse(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();t[int(q),int(b)]=int(w),d,int(n)
 return t
old,os,op,oi,_,_=C.compile_compare(False);new,ns,np,ni,alias,_=C.compile_compare(True)
f={i:ni[alias.get(n,n)]for n,i in oi.items()}|{v:np[n]for n,v in op.items()}
excluded={(oi['erase_first'],0),(oi['erase_second'],0),(oi['return_neq'],1),(oi['restore_counter'],1)}
for(q,b),(w,d,n)in old.items():
 if(q,b)not in excluded:assert new[f[q],b]==(w,d,f[n])
assert len(ni)==29 and parse(D/'compare_biased_counter_29.tm')==new
variant,vs,vp,vi=V.compile_compare();assert len(vi)==27 and parse(D/'compare_biased_counter_27.tm')==variant
saved=json.loads((D/'compare_biased_counter_guards.json').read_text());guard29={int(q):set(bs)for q,bs in saved['valid_reads_by_state'].items()}
r27=json.loads((D/'compare_biased_counter27_results.json').read_text());guard27={int(q):set(bs)for q,bs in r27['valid_reads_by_state'].items()}
counts={};maximum=0
headers=['10','111110','1011110','1101110','1110110','1111010','110101110']
for variant_name,T,start,ports,guards,gaps in [('29',old,os,op,guard29,(2,5)),('27',variant,vs,vp,guard27,(3,5))]:
 count=0
 for a,b,numprev,header,gap in itertools.product(range(6),range(6),range(3),headers,gaps):
  c=-7;anchor=c+a+gap+1;tape=set(range(c,c+a+1))|{anchor+j for j,x in enumerate(header)if x=='1'};p=anchor+len(header)
  for v in(1,4,2)[:numprev]:tape.update(range(p,p+v));p+=v+1
  source=p;delimiter=p+b+3;tape.update(range(source+1,delimiter));tape|={c-2,c-6,delimiter+1,delimiter+7}
  expected=(tape-set(range(c+1,c+a+1)))|{source};q=start;h=source;steps=0
  while q not in ports.values():
   bit=int(h in tape);assert c-1<=h<=delimiter
   if variant_name=='29':
    assert(q,bit)not in excluded;assert bit in guards[f[q]]
    w,d,n=T[q,bit];assert new[f[q],bit]==(w,d,f[n])
   else:assert bit in guards[q];w,d,n=T[q,bit]
   if w:tape.add(h)
   else:tape.discard(h)
   h+=1 if d=='R'else-1;q=n;steps+=1;assert steps<1000000
  assert tape==expected and h==c and q==ports['EQ'if a==b else'NEQ']
  count+=1;maximum=max(maximum,steps)
 counts[variant_name]=count
# The copier18 identification is an unconditional all-row quotient.
a,as_,ar,ai=B.compile_copy(variable_anchor=True);z,zs,zr,zi=F.compile_copy();proj={i:zi[n]for n,i in ai.items()}|{ar:zr}
for(q,b),(w,d,n)in a.items():assert z[proj[q],b]==(w,d,proj[n])
assert zr==18 and parse(D/'biased_reference_copy_18.tm')==z
result={'status':'PASS','comparator_states':[29,27],'whole_tape_cases':counts,'maximum_steps':maximum,'four_excluded_prefold_pairs_checked':True,'all_prefold_nonexcluded_row_projections_checked':True,'all_saved_comparator_guards_respected':True,'copy18_all_row_quotient_checked':True,'port_warning':'EQ and NEQ remain separate. Variant27 requires gap>=3; variant29 needs gap>=2.',
 'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in[D/'compare_biased_counter_29.tm',D/'compare_biased_counter_27.tm',D/'biased_reference_copy_18.tm']}}
(OUT/'comparators_and_copy18_independent_audit.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
for size,path,states,guards,ports in [(29,D/'compare_biased_counter_29.tm',ni,guard29,np),(27,D/'compare_biased_counter_27.tm',vi,guard27,vp)]:
 r={'table':str(path.relative_to(OUT.parent)),'table_sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'working_states':size,'start':states['init'],'ports':ports,'reject':states['reject'],'allowed_reads':{str(q):sorted(bs)for q,bs in guards.items()},'forced_zero':[q for q,bs in guards.items()if bs=={0}],'forced_one':[], 'status':'Ordinary proof reviewed independently; exact pre-fold row projection and independent arbitrary-header whole-tape checks supplement it.','required_gap':3 if size==27 else 2,'entry_precondition':'Counter1^(a+1), zero immediately left; indicated minimum gap; header is finite nonempty positive-one runs separated by single zeros; selected field1^(b+3) has first1 erased; preceding fields nonempty; start on erased first1.','proof':'comparators_and_copy18_review.md','terminal_warning':'Preserve both EQ/NEQ ports and their meanings until explicitly linked. Invariant-failure sink retains both symbols.'}
 (OUT/f'compare_biased_counter_{size}_guards_reviewed.json').write_text(json.dumps(r,indent=2)+'\n')
