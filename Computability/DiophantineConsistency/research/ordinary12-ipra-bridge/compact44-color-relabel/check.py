#!/usr/bin/env python3
"""Externally compare the exact finite 942 and compact44 943 tile tables."""
import hashlib,json,re,sys
from pathlib import Path
if not __debug__ or sys.flags.optimize:
    raise RuntimeError('optimized Python is unsupported')
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
FILES={
 'old_data':(BASE/'Lean/DiophantineConsistency/WangTiles942Data.lean','afea682c7a961f9cc30015be3d12469835a6ace52e9104b054c7ccb6d182d9de'),
 'old_table':(BASE/'Lean/DiophantineConsistency/WangTiles942TableData.lean','0d2bf996f4e7e19acba82d5d3f1805a71c17cb1a9bcdc959e67453da14697a2c'),
 'machine':(BASE/'Lean/DiophantineConsistency/DecimalMachine215.lean','00e46d6917bb18090027bece970a7ad1bc6eb691bd35c682d4be1a5332f82f80'),
 'tiles':(BASE/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json','66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'),
 'dense':(BASE/'candidates/free-j-polarized-positive/source/positive/coefficients/recipe/k215_transitions.json','880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755')}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def need(x,m):
 if not x:raise ValueError(m)
def body(text,start,end):
 need(text.count(start)==1,'nonunique opening '+start)
 tail=text.split(start,1)[1];need(end in tail,'missing terminator');return tail.split(end,1)[0]
def main():
 for key,(path,h) in FILES.items():need(digest(path)==h,'source drift '+key)
 old=FILES['old_data'][0].read_text();machine=FILES['machine'][0].read_text()
 fragment=body(old,'def actionCache : Array Action := #[',']')
 pat=re.compile(r'\((true|false), (true|false), (\d+)\)')
 matches=pat.findall(fragment)
 need(len(matches)==430 and not re.sub(r'[\s,]','',pat.sub('',fragment)),'old action literal syntax')
 actions=[(int(w=='true'),int(d=='true'),int(q)) for w,d,q in matches]
 fragment=body(machine,'def toDenseList : List ℕ := [',']')
 need(not re.sub(r'[\s,\d]','',fragment),'state permutation literal syntax')
 sigma=list(map(int,re.findall(r'\d+',fragment)))
 need(len(sigma)==215 and sorted(sigma)==list(range(215)) and sigma[0]==0 and sigma[1]==93,'state permutation')
 state=sigma+[215]
 dense=json.loads(FILES['dense'][0].read_text())['transitions']
 need(len(dense)==430 and len({(r[0],r[1]) for r in dense})==430,'dense action domain')
 lut={(q,b):(w,1 if d==1 else 0,t) for q,b,w,d,t in dense}
 need(all(lut[(sigma[j//2],j%2)]==(w,d,state[q]) for j,(w,d,q) in enumerate(actions)),'action conjugacy')
 targets=[sorted({q for _,d,q in actions if d==direction}) for direction in (0,1)]
 dense_targets=[sorted(state[q] for q in side) for side in targets]
 need([len(x) for x in targets]==[45,199] and [len(set(x)) for x in dense_targets]==[45,199],'rail targets')
 def rail(d,q):return 205-199*d+sum(t<q for t in targets[d])
 h={i:i for i in range(6)}
 for d in (0,1):
  for q in targets[d]:h[rail(d,q)]=205-199*d+dense_targets[d].index(state[q])
 need(sorted(h)==list(range(250)) and sorted(h.values())==list(range(250)),'horizontal permutation')
 def vmap(x):
  if 2<=x<=431:
   q,b=divmod(x-2,2);return 2+2*state[q]+b
  return x
 vertical=[vmap(x) for x in range(439)]
 need(sorted(vertical)==list(range(439)),'vertical permutation')
 def hc(q,b):return 2*q+b+2
 indexed=[(0,(2,435,3,1))]
 for j,(w,d,q) in enumerate(actions):indexed.append((j+1,((1-d)*rail(0,q),hc(j//2,j%2),d*rail(1,q),w)))
 for a in (1,0):
  for b in (0,1):indexed.append((433-2*a+b,(0,432*a+b,0,432*a+b)))
 for d in (1,0):
  for q in targets[d]:
   for b in (0,1):indexed.append((423+2*rail(d,q)+b,(d*rail(d,q),b,(1-d)*rail(d,q),hc(q,b))))
 for a in (0,1):
  for b in (0,1):indexed.append((923+2*a+b,(0,432*a+b,0,438)))
 indexed += [(927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))]
 indexed += [(496+t,(1,438,1,t)) for t in (434,435,436)]
 indexed += [(933+3*a+b,(a*a,437,b,437)) for a in range(3) for b in range(3)]
 need(len(indexed)==942 and [i for i,_ in indexed]==list(range(942)),'old table order')
 oldrows=[r for _,r in indexed];new=[tuple(r) for r in json.loads(FILES['tiles'][0].read_text())]
 need(len(new)==943 and len(set(new))==943 and len(set(oldrows))==942,'row cardinalities')
 def translate(t):w,n,e,s=t;return (h[w],vmap(n),h[e],vmap(s))
 mapped=[translate(t) for t in oldrows]
 lookup={r:i for i,r in enumerate(new)}
 need(all(r in lookup for r in mapped),'translated row absent')
 indices=[lookup[r] for r in mapped]
 need(sorted(indices)==[0]+list(range(2,943)),'row bijection and sole extra index')
 need(new[1]==(5,0,0,0) and new[0]==translate(oldrows[0]),'extra and start')
 need([i for i,t in enumerate(new) if t[0]==5]==[1] and not any(t[2]==5 for t in new),'west-five/east-five exclusion')
 # Negative controls are separate from the stated mathematical conclusion.
 badh=dict(h);badh[6],badh[7]=badh[7],badh[6]
 need(any((badh[t[0]],vmap(t[1]),badh[t[2]],vmap(t[3])) not in lookup for t in oldrows),'horizontal mutation')
 badv=vertical.copy();badv[2],badv[4]=badv[4],badv[2]
 need(any((h[t[0]],badv[t[1]],h[t[2]],badv[t[3]]) not in lookup for t in oldrows),'vertical mutation')
 result={'status':'PASS_FINITE_942_TO_943_COLOR_RELABEL','input_sha256':{k:v[1] for k,v in FILES.items()},'checker_sha256':digest(Path(__file__)),'state_old_to_dense':sigma,'horizontal_old_to_compact':[h[i] for i in range(250)],'vertical_old_to_compact':vertical,'old_row_to_compact_index':indices,'extra_compact_index':1,'extra_tile':[5,0,0,0],'start_preserved':True,'sole_west_five_index':1,'east_five_indices':[],'action_conjugacy_checked':430,'negative_controls':['swap_horizontal_6_7','swap_vertical_2_4'],'scope':'Finite external source-data calculation only. It does not prove Lean table identity, exclude or interpret the extra tile in a model, transport tilings, establish all-model machine simulation, or prove an iPRA endpoint.'}
 print(json.dumps(result,indent=2,sort_keys=True))
if __name__=='__main__':main()
