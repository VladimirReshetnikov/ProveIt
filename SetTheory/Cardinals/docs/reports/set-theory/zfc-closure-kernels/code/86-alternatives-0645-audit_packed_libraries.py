#!/usr/bin/env python3
"""Independent literal-row check, without importing the packing producer."""
if not __debug__: raise RuntimeError('Assertions required')
from pathlib import Path
import json,hashlib,sys
V=Path(__file__).resolve().parent;R=V.parent;P=R/'machine_encoding/component_packing'
def parse(p):
 t={}
 for l in p.read_text().splitlines():
  if not l or l.startswith('#'):continue
  q,b,w,d,z=l.split();q,b,w,z=map(int,(q,b,w,z));assert(q,b)not in t and b in (0,1) and w in (0,1) and d in ('L','R');t[q,b]=(w,d,z)
 return t
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
spec={
 'native':('architectures/encoded_native_edge_68.tm','encoded_native_edge_68_guards_reviewed.json',68,54,{'fetch':55},[68]),
 'query':('architectures/retained_template_query_133.tm','retained_template_query_133_guards_reviewed.json',133,18,{'start':0},[133]),
 'compare':('arithmetic_core/compare_biased_counter_29.tm','compare_biased_counter_29_guards_reviewed.json',29,28,{'start':0},[29,30]),
 'writer':('native_copier/anchor_mode_writer_11.tm',None,11,10,{f'mode_{k}':k for k in range(1,5)},[11])}
def audit(name,components,universal=False):
 p=P/name;m=json.loads((p/'manifest.json').read_text());tab=parse(p/'library.tm');pi=m['projection'];n=m['working_states'];rows={};domains={};entries={};ports=[];sinks=[];hashes={}
 assert sha(p/'library.tm')==m['sha256'];assert set(tab)=={(q,b)for q in range(n)for b in (0,1)}
 for pref in components:
  file,gfile,size,sink,ent,outs=spec[pref];file=R/file;t=parse(file);hashes[pref]=sha(file);assert set(t)=={(q,b)for q in range(size)for b in (0,1)}
  if gfile:
   cert=json.loads((V/gfile).read_text());assert cert['table_sha256']==sha(file);g={int(q):bs for q,bs in cert['allowed_reads'].items()}
  else:
   assert sha(file)=='6d3c5387b7f8dc5b14138337b09462a75e6739ebb6f9071127aa8c299666525f';g={q:([1]if q in (4,5,6,7)else[0,1])for q in range(size)}
  key=lambda q:f'{pref}:{q}'
  domains.update({key(q):([0,1]if universal else g[q])for q in range(size)})
  rows.update({(key(q),b):(w,d,key(z))for(q,b),(w,d,z)in t.items()})
  entries.update({f'{pref}.{k}':key(q)for k,q in ent.items()});ports.extend(key(q)for q in outs);sinks.append(key(sink))
 if name.startswith('final_'):
  reach=set(entries.values());todo=list(reach)
  while todo:
   q=todo.pop()
   for b in domains.get(q,[]):
    z=rows[q,b][2]
    if z not in reach:reach.add(z);todo.append(z)
  assert 'query:127' not in reach
  c=json.loads((p/'unreachable_certificate.json').read_text())
  assert set(c['entry_states'])==set(entries.values()) and set(c['reachable_states'])==reach
  incoming=[[q,b,b in domains[q]]for(q,b),(_,_,z)in rows.items()if z=='query:127']
  assert incoming==c['all_incoming_rows']==[['query:124',0,False]]
  domains['query:127']=[]
 assert m['domains']==domains;assert set(pi)==set(domains)|set(ports)
 assert sorted(q for g in m['classes']for q in g)==sorted(domains)
 for i,g in enumerate(m['classes']):assert g and all(pi[q]==i for q in g)
 assert m['entries']=={k:pi[q]for k,q in entries.items()}
 assert set(m['ports'])==set(ports) and all(m['ports'][q]==pi[q]for q in ports)
 assert set(pi[q]for q in ports)==set(range(n,n+len(ports)))
 for q in sinks:assert m['classes'][pi[q]]==[q]
 assert len({pi[q]for q in sinks})==len(sinks)
 checked=[]
 for(q,b),(w,d,z)in rows.items():
  if b in domains[q]:
   assert tab[pi[q],b]==(w,d,pi[z]),(name,q,b)
   checked.append([q,b,pi[q],w,d,pi[z]])
 c=json.loads((p/'row_projection_certificate.json').read_text());assert c['checked_allowed_rows']==len(checked)
 assert sorted(c['rows'])==sorted(checked)
 assert all(z<n+len(ports)for w,d,z in tab.values())
 # Verify claimed full-two-symbol universal classes separately, prior to guarded packing.
 uc=m['universal_classes'];up={q:i for i,g in enumerate(uc)for q in g};up.update({q:len(uc)+i for i,q in enumerate(ports)})
 assert sorted(q for g in uc for q in g)==sorted(domains)
 for g in uc:
  for b in (0,1):assert len({(rows[q,b][0],rows[q,b][1],up[rows[q,b][2]])for q in g})==1
 for q in sinks:assert uc[up[q]]==[q]
 report={'status':'PASS','library':name,'working_states':n,'rows':len(tab),'admitted_source_rows':len(checked),'source_states':len(domains),'ports':m['ports'],'distinct_failure_states':[pi[q]for q in sinks],'source_hashes':hashes,'library_sha256':sha(p/'library.tm'),'universal_nontrivial_classes':[g for g in uc if len(g)>1]}
 return report
out=[audit('final_with_compare',['native','query','writer','compare']),audit('final_without_compare',['native','query','writer']),audit('guarded_reviewed',['native','query','writer','compare']),audit('guarded_without_compare',['native','query','writer']),audit('native62',['native'],True)]
# Comparator wrappers: admitted rows checked against reviewer guards rather than producer trace guards.
sys.path.insert(0,str(R/'arithmetic_core'))
import fold_comparator_entries as F
for gap,size,parent in [(2,28,29),(3,24,27)]:
 nt,s,ports,ids,ng,cert,(old,os,op,pi)=F.compile_compare(gap)
 g=json.loads((V/f'compare_biased_counter_{parent}_guards_reviewed.json').read_text())
 assert parse(R/f'arithmetic_core/compare_biased_counter_{parent}.tm')==old
 assert parse(R/f'arithmetic_core/compare_biased_counter_{size}.tm')==nt
 assert len(nt)==2*size and s==pi[os] and all(ports[k]==pi[q]for k,q in op.items())
 checks=0
 for(q,b),(w,d,z)in old.items():
  if b in g['allowed_reads'][str(q)]:assert nt[pi[q],b]==(w,d,pi[z]);checks+=1
 out.append({'status':'PASS','library':f'comparator{parent}_to_{size}','admitted_source_rows':checks,'minimum_loaded_gap':gap,'working_states':size,'ports':ports,'sha256':sha(R/f'arithmetic_core/compare_biased_counter_{size}.tm')})
(V/'packed_libraries_independent_audit.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
