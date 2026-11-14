"""Independent rooted labeled-graph census of the ProveIt U208 submissions."""
from pathlib import Path
import hashlib,json,collections
ROOT=Path(__file__).parent
B=ROOT.parent/'reference/proveit'
FILES=[
 ('Plain','U208_ConPA_2026-10-29/machine/u208.native.tm'),
 ('Conditional primary','u208_conpa_2026-10-29/machine/u208.native.tm'),
 ('Conditional alternative','u208_conpa_2026-10-29/alternative/u208.native.tm'),
 ('Entry primary','u208_conpa_entry_context_2026-10-29/machine/u208.native.tm'),
 ('Entry alternative','u208_conpa_entry_context_2026-10-29/machine/u208_compatibility.native.tm'),
 ('History primary','U208_ConPA_History_2026-10-29/machine/u208.native.tm'),
 ('History alternative','U208_ConPA_History_2026-10-29/machine/compatibility_variant/u208.native.tm'),
 ('Research primary','u208_research_2026-10-29/machine/u208.native.tm'),
 ('Research plain','u208_research_2026-10-29/machine/variant_plain/u208.native.tm')]
def parse(p):
 t={}
 for line in p.read_text().splitlines():
  if not line or line.startswith('#'):continue
  q,b,w,d,n=line.split();q,b,w,n=map(int,(q,b,w,n))
  assert (q,b) not in t and b in(0,1)and w in(0,1)and d in('L','R')
  t[q,b]=(w,d,n)
 return t
def canonical(t,start=0,halt=254):
 states={q for q,b in t};assert set(t)=={(q,b) for q in states for b in (0,1)}
 assert {z for w,d,z in t.values()}-states=={halt}
 mapping={start:0};todo=[start];rows=[]
 for q in todo:
  for b in (0,1):
   w,d,z=t[q,b]
   if z==halt:n=-1
   else:
    if z not in mapping:mapping[z]=len(todo);todo.append(z)
    n=mapping[z]
   rows.append((mapping[q],b,w,d,n))
 assert set(todo)==states
 data=json.dumps(rows,separators=(',',':')).encode()
 return hashlib.sha256(data).hexdigest(),mapping,rows
def main():
 out=[];graphs={}
 for name,path in FILES:
  p=B/path;t=parse(p);c,m,g=canonical(t)
  group=graphs.setdefault(c,chr(65+len(graphs)))
  out.append({'name':name,'path':path,'states':len(t)//2,'rows':len(t),
   'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'canonical_sha256':c,'class':group,
   'canonical_map':{str(k):v for k,v in sorted(m.items())}})
 result={'proveit_commit':'239b7a406e24405d464edc526e09d402abce5bc5',
  'presentations':9,'classes':len(graphs),'tables':out}
 (ROOT/'proveit_comparison.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({'classes':len(graphs),'tables':[{k:v for k,v in d.items() if k!='canonical_map'}for d in out]},indent=2))
if __name__=='__main__':main()
