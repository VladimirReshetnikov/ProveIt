"""Independent structural certificate audit, not proof-assistant verification."""
import json,re,collections,sys
from pathlib import Path
sys.setrecursionlimit(20000)
B=Path(__file__).parent
js=json.loads((B/'trees.json').read_text());ls=json.loads((B/'leaves.json').read_text())
def walk(t,p):
 q='';i=0
 while t[0]=='node':
  b=p[i] if i<len(p) else '0';q+=b;i+=1;t=t[1+int(b)]
 return q,tuple(t[1])
def inc(p):
 r=list(p);i=len(r)-1
 while i>=0 and r[i]=='1':r[i]='0';i-=1
 if i>=0:r[i]='1'  # incRev []=[]: wrap all-ones; do not extend
 return ''.join(r)
# Exhaustive finite regression against literal recursive incRev semantics.
def inc_rev_spec(bs):
 if not bs:return []
 if bs[0]=='0':return ['1']+bs[1:]
 return ['0']+inc_rev_spec(bs[1:])
for width in range(11):
 for n in range(1<<width):
  bits=format(n,f'0{width}b') if width else ''
  expected=''.join(reversed(inc_rev_spec(list(reversed(bits)))))
  assert inc(bits)==expected
assert inc('')=='' and inc('111')=='000'
def strip(p,b,k):
 while k and p:
  if p[-1]==b:k-=1
  p=p[:-1]
 return p
def dest(p,e,br=None):
 if e[0]=='inc' or (e[0]=='decnz' and br=='nz'):return inc(p)
 if e[0]=='brk' or (e[0]=='decnz' and br=='z'):return inc(strip(p,'0',e[1] if e[0]=='brk' else 1))
 if e[0]=='cont':return strip(p,'1',e[1])
 raise ValueError(e)
ix={k:{p:i for i,(p,e) in enumerate(ls[k])} for k in js}
def segment(k,p,raw=False):
 counts=collections.Counter();visited=set();trace=[]
 while True:
  q,e=walk(js[k],p);o=ix[k][q]
  if e[0] in ('decnz','halt'):
   result=(o,tuple(sorted(counts.items())),trace)
   return result+(p,) if raw else result
  assert q not in visited,('silent cycle',k,q);visited.add(q);trace.append(o)
  if e[0]=='inc':counts[e[1]]+=1
  p=dest(q,e)
def graph(k):
 out={}
 for o,(q,e) in enumerate(ls[k]):
  e=tuple(e)
  if e[0]=='halt':out[o]={'op':e,'successors':[]}
  if e[0]=='decnz':out[o]={'op':e,'successors':[segment(k,dest(q,e,b))[:2] for b in ['nz','z']]}
 return out
A=graph('source');D=graph('reference');assert A==D
assert segment('source','')[:2]==segment('reference','')[:2]
s=(Path(__file__).resolve().parent/'upstream'/'KSource215Data.lean').read_text();s=s[s.index('def fwd0'):s.index('def bwd0')]
rs=[tuple(map(int,m)) for m in re.findall(r'\.leaf \((\d+), (\d+), \((-?\d+) : Int\), (\d+), (\d+)\)',s)]
mapping=[]
for a,b,z,j,k in rs:
 q1,e1=walk(js['source'],bin(a)[3:]);q2,e2=walk(js['reference'],bin(b)[3:]);o1=ix['source'][q1];o2=ix['reference'][q2]
 assert o1==o2 and e1==e2; mapping.append(o1)
print('testgraph vertices',len(A),'certificate entries',len(mapping),'unique mapped vertices',len(set(mapping)))
print('all certificate pairs map to identical ordinal',True)
res={'testgraph_equal':True,'initial_segment_equal':True,'testgraph_vertices':len(A),'certificate_entries':len(mapping),'certificate_unique_ordinals':len(set(mapping)), 'mapping_is_identity_on_ordinal':True,'duplicate_checkpoint_aliases':len(mapping)-len(set(mapping)), 'verification':'Independent Python structural check, not Lean/Rocq verification.', 'incPath_regression_cases':2047, 'incPath_overflow':'Exact incRev wrap semantics, including empty->empty' }
(B/'ORDINAL_GRAPH_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n')
(B/'ordinal_graph.json').write_text(json.dumps(A))
# Build canonical data for a PROPOSED normalization-aware checker.
# This is not accepted by the current literal-pointer checker without a new sound normalization lemma.
# Canonical pointers are the full consumed leaf paths, one per test/halt ordinal.
ords=sorted(A);ind={o:i for i,o in enumerate(ords)}
assert segment('source','')[0]==ords[0]
def encode(q):return int('1'+q,2)
small=[]
for o in ords:
 q1=ls['source'][o][0];q2=ls['reference'][o][0]
 succ=A[o]['successors']
 j,k=(ind[succ[0][0]],ind[succ[1][0]]) if succ else (0,0)
 small.append((encode(q1),encode(q2),0,j,k))
# Re-evaluate every branch of the generated certificate against full path semantics,
# comparing to the paths encoded by its actual successor-index records.
for a,b,z,j,k in small:
 q1,e1=walk(js['source'],bin(a)[3:]);q2,e2=walk(js['reference'],bin(b)[3:])
 assert e1==e2 and z==0
 if e1[0]=='decnz':
  for br,n in [('nz',j),('z',k)]:
   o1,c1,_=segment('source',dest(q1,e1,br));o2,c2,_=segment('reference',dest(q2,e2,br))
   aa,bb,_,_,_=small[n]
   assert c1==c2 and ls['source'][o1][0]==bin(aa)[3:] and ls['reference'][o2][0]==bin(bb)[3:]
 else:assert e1[0]=='halt'
def otree(rows):
 if len(rows)==1:
  a,b,z,j,k=rows[0];return f'.leaf ({a}, {b}, (0 : Int), {j}, {k})'
 n=len(rows)//2
 return f'.branch {n} ({otree(rows[:n])})\n  ({otree(rows[n:])})'
out='''import BusyBeaver.ZFC.KSource215Data
/-! UNCOMPILED DATA for a PROPOSED normalization-aware checker, NOT the existing
    literal-pointer checker. Independent canonical-path checks passed. A sound
    normalization lemma and kernel check remain required. No endpoint is claimed. -/
namespace SetTheory.BusyBeaver.ZFC.KSource215Canonical
open RegisterPath RMBisim RMOffsetBisim KSource215
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
def canonicalCert : OTree :=\n  '''+otree(small)+'''\n
-- Compile this in suitably sized batches before connecting it to the endpoint.
-- Existing obranchOk is NOT suitable: seg preserves raw pointer aliases.
-- First define canonical stop-pointer normalization, prove it sound using
-- step_tsite, then check this table with that normalized checker.
end SetTheory.BusyBeaver.ZFC.KSource215Canonical
'''
(B/'CanonicalCert215.lean').write_text(out)
res.update({'canonical_certificate_entries':len(small),'canonical_certificate_bytes':len(out.encode()),'canonical_certificate_path_checker_passed':True,'records_removed':len(rs)-len(small)})
(B/'ORDINAL_GRAPH_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n')
print('canonical cert bytes',len(out.encode()))
stats={}
for side in ['source','reference']:
 traces=[]
 for o,(q,e) in enumerate(ls[side]):
  if e[0]=='decnz':
   traces.extend(segment(side,dest(q,tuple(e),br))[2] for br in ['nz','z'])
 init=segment(side,'')
 stats[side]={'vertices':len(graph(side)), 'edges':len(traces),'max_segment_transitions':max(map(len,traces)), 'sum_segment_transitions':sum(map(len,traces)), 'initial_segment_transitions':len(init[2]),'path_max_bits':max(len(p) for p,e in ls[side])}
res['segment_stats']=stats
(B/'ORDINAL_GRAPH_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n')
print(json.dumps(stats,indent=2))

raw_bad=0
for o in ords:
 if A[o]['op'][0]=='decnz':
  for br in ['nz','z']:
   for side in ['source','reference']:
    q,e=ls[side][o];d=segment(side,dest(q,tuple(e),br),raw=True)
    if d[3]!=ls[side][d[0]][0]:raw_bad+=1
res['literal_raw_pointer_mismatches_in_canonical_table']=raw_bad
res['canonical_table_requires_normalizing_checker']=True
(B/'ORDINAL_GRAPH_AUDIT.json').write_text(json.dumps(res,indent=2)+'\n')
print('raw-pointer comparisons requiring normalization',raw_bad)
