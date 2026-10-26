#!/usr/bin/env python3
"""Read-only finite audit; not a Lean proof or replacement for one.
Reconstruct the exact Core row formulas using parsed authenticated Data caches.
The caller supplies the repository root and an output path.
"""
from pathlib import Path
import re,json,hashlib,argparse,collections
p=argparse.ArgumentParser();p.add_argument('repo',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
base=a.repo/'Computability/DiophantineConsistency/Lean/DiophantineConsistency'
data_path=base/'WangTiles942Data.lean'; core_path=base/'WangTiles942Core.lean'
s=data_path.read_text()
chunk=s.split('def actionCache : Array Action := #[',1)[1].split('\n ]',1)[0]
actions=[(w=='true',d=='true',int(q)) for w,d,q in re.findall(r'\((true|false),\s*(true|false),\s*(\d+)\)',chunk)]
assert len(actions)==430
chunk=s.split('def targetList (d : Bool) : List ℕ :=',1)[1].split('\ndef targets',1)[0]
right,left=re.findall(r'\[([^\]]*)\]',chunk)
targets={False:list(map(int,left.split(','))),True:list(map(int,right.split(',')))}
for d in [False,True]:
    assert targets[d]==sorted({q for _,dd,q in actions if dd==d})
chunk=s.split('def railCache (d : Bool) : Array ℕ :=',1)[1].split('\ntheorem targetList_nodup',1)[0]
right,left=re.findall(r'#\[([^\]]*)\]',chunk)
rails={False:list(map(int,left.split(','))),True:list(map(int,right.split(',')))}
for d in [False,True]:
    assert len(rails[d])==216
    assert rails[d]==[205-199*int(d)+sum(t<q for t in targets[d]) for q in range(216)]
def rail(d,q): return rails[d][q]
def hc(q,b): return 2*q+b+2
rows=[]
def add(i,f,w,n,e,ss): rows.append({'index':i,'family':f,'west':w,'north':n,'east':e,'south':ss})
add(0,'start',2,435,3,1)
for j,(w,d,q) in enumerate(actions):
    add(j+1,'transition',(1-int(d))*rail(False,q),hc(j//2,j%2),int(d)*rail(True,q),int(w))
for k in [0,1]:
    for b in range(2): add(433-2*k+b,'pass',0,432*k+b,0,432*k+b)
for d in [False,True]:
    for q in targets[d]:
        for b in range(2): add(423+2*rail(d,q)+b,'receive',int(d)*rail(d,q),b,(1-int(d))*rail(d,q),hc(q,b))
for k in range(2):
    for b in range(2): add(923+2*k+b,'finish',0,432*k+b,0,438)
for i,w,n,e,ss in [(927,2,434,2,0),(928,3,436,4,4),(929,4,436,4,0)]: add(i,'initializer',w,n,e,ss)
for ss in [434,435,436]: add(496+ss,'reset',1,438,1,ss)
for aa in range(3):
    for b in range(3): add(933+3*aa+b,'seam',aa**2,437,b,437)
rows.sort(key=lambda r:r['index'])
assert [r['index'] for r in rows]==list(range(942))
assert len({(r['west'],r['north'],r['east'],r['south']) for r in rows})==942

def fibers(rs):
    out=collections.defaultdict(list)
    for r in rs: out[(r['west'],r['north'],r['east'])].append(r)
    return out
bad=[{'key':key,'rows':value} for key,value in fibers(rows).items() if len(value)>1]
nonreset_nonfinish=[r for r in rows if r['north']!=438 and r['south']!=438]
operating_north_nonfinish=[r for r in rows if r['north']<=433 and r['south']!=438]
assert len(fibers(nonreset_nonfinish))==len(nonreset_nonfinish)
assert len(fibers(operating_north_nonfinish))==len(operating_north_nonfinish)
result={
 'scope':'Python reconstruction of literal Core row formulas with parsed Data caches; not a Lean theorem',
 'files':{str(x.relative_to(a.repo)):hashlib.sha256(x.read_bytes()).hexdigest() for x in [data_path,core_path]},
 'actions':len(actions),'target_counts':{'left':len(targets[False]),'right':len(targets[True])},
 'rail_cache_checks':'All 432 cache entries equal the parsed-target cardinality formula',
 'rows':len(rows),'distinct_tiles':942,'distinct_WNE_keys':len(fibers(rows)),
 'family_counts':dict(collections.Counter(r['family'] for r in rows)),
 'unrestricted_ambiguous_key_count':len(bad),
 'unrestricted_unequal_unordered_pairs':sum(len(v['rows'])*(len(v['rows'])-1)//2 for v in bad),
 'all_ambiguous_fibers':bad,
 'nonreset_nonfinish':{'rows':len(nonreset_nonfinish),'distinct_WNE_keys':len(fibers(nonreset_nonfinish)),'counterexample_pairs':0},
 'north_le_433_nonfinish':{'rows':len(operating_north_nonfinish),'distinct_WNE_keys':len(fibers(operating_north_nonfinish)),'counterexample_pairs':0},
 'halt_receiver_rows':[r['index'] for r in rows if r['family']=='receive' and r['south'] in [432,433]]}
a.output.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
