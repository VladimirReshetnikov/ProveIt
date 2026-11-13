#!/usr/bin/env python3
"""Independent reconstruction from pinned old caches and row formulas."""
import hashlib,json,re,subprocess,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]
BASE=ROOT/'Computability/DiophantineConsistency'
PKG=BASE/'research/ordinary12-ipra-bridge/compact44-color-relabel'
FILES={
 'old_data':(BASE/'Lean/DiophantineConsistency/WangTiles942Data.lean','afea682c7a961f9cc30015be3d12469835a6ace52e9104b054c7ccb6d182d9de'),
 'old_table':(BASE/'Lean/DiophantineConsistency/WangTiles942TableData.lean','0d2bf996f4e7e19acba82d5d3f1805a71c17cb1a9bcdc959e67453da14697a2c'),
 'machine':(BASE/'Lean/DiophantineConsistency/DecimalMachine215.lean','00e46d6917bb18090027bece970a7ad1bc6eb691bd35c682d4be1a5332f82f80'),
 'tiles':(BASE/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json','66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f'),
 'dense':(BASE/'candidates/free-j-polarized-positive/source/positive/coefficients/recipe/k215_transitions.json','880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755'),
 'check':(PKG/'check.py','9d870a271ac5f03c0b6122728bd9a7c031ae3a227fc8ef50a184d5ca41b4b20b'),
 'receipt':(PKG/'receipt.json','2600b91d7cdc5f51a06ef7788e57d4164170d264777d037933231671ca32ef54')}
def need(b,m):
 if not b:raise ValueError(m)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def literal_section(s,start,stop):
 need(s.count(start)==1,'unique anchor '+start)
 x=s.split(start,1)[1];need(stop in x,'terminator');return x.split(stop,1)[0]
def numbers(s):
 need(not re.sub(r'[\s,0-9]','',s),'non-numeric literal');return [int(x) for x in re.findall(r'\d+',s)]
def main():
 for name,(p,h) in FILES.items():need(sha(p)==h,'pin '+name)
 old=FILES['old_data'][0].read_text();mach=FILES['machine'][0].read_text()
 action_text=literal_section(old,'def actionCache : Array Action := #[',']')
 pattern=r'\((true|false), (true|false), (\d+)\)'
 actions=re.findall(pattern,action_text)
 need(len(actions)==430 and not re.sub(r'[\s,]','',re.sub(pattern,'',action_text)),'action cache syntax')
 actions=[(int(a=='true'),int(b=='true'),int(c)) for a,b,c in actions]
 sigma=numbers(literal_section(mach,'def toDenseList : List ℕ := [',']'))
 need(len(sigma)==215 and sorted(sigma)==list(range(215)) and sigma[0]==0 and sigma[1]==93,'state permutation')
 mapping=sigma+[215]
 # Directly read both target and rail caches from old Lean source, rather than
 # obtaining ranks from the reconstructed action set as the author checker does.
 t=literal_section(old,'def targetList (d : Bool) : List ℕ :=','def targets (d : Bool)')
 match=re.fullmatch(r'\s*if d then \[([^]]*)\] else \[([^]]*)\]\s*',t)
 need(match is not None,'target list syntax')
 targets={1:numbers(match[1]),0:numbers(match[2])}
 c=literal_section(old,'def railCache (d : Bool) : Array ℕ :=','theorem targetList_nodup')
 match=re.fullmatch(r'\s*if d then #\[([^]]*)\] else #\[([^]]*)\]\s*',c)
 need(match is not None,'rail cache syntax')
 rails={1:numbers(match[1]),0:numbers(match[2])}
 for d in (0,1):
  need(targets[d]==sorted({q for _,direction,q in actions if direction==d}),'literal target/action agreement')
  need(len(rails[d])==216 and rails[d]==[205-199*d+sum(x<q for x in targets[d]) for q in range(216)],'rail cache formula')
 dense=json.loads(FILES['dense'][0].read_text())['transitions']
 need(len(dense)==430 and len({(q,b) for q,b,_,_,_ in dense})==430,'dense actions')
 dense_lut={(q,b):(w,1 if direction==1 else 0,t) for q,b,w,direction,t in dense}
 need(all(dense_lut[(sigma[j//2],j%2)]==(write,direction,mapping[target]) for j,(write,direction,target) in enumerate(actions)),'430 action conjugacies')
 # Implement orderedRows directly from the pinned Lean definitions; this is a
 # manually transcribed semantics, not a Lean parser or internal proof.
 head=lambda q,b:2*q+b+2
 ordered=[(0,(2,435,3,1))]
 for j,(write,direction,target) in enumerate(actions):
  ordered.append((j+1,((1-direction)*rails[0][target],head(j//2,j%2),direction*rails[1][target],write)))
 for a in (1,0):
  for b in range(2):ordered.append((433-2*a+b,(0,432*a+b,0,432*a+b)))
 for d in (1,0):
  for target in targets[d]:
   for b in range(2):
    rail=rails[d][target];ordered.append((423+2*rail+b,(d*rail,b,(1-d)*rail,head(target,b))))
 for a in range(2):
  for b in range(2):ordered.append((923+2*a+b,(0,432*a+b,0,438)))
 ordered.extend([(927,(2,434,2,0)),(928,(3,436,4,4)),(929,(4,436,4,0))])
 ordered.extend((496+t,(1,438,1,t)) for t in (434,435,436))
 ordered.extend((933+3*a+b,(a*a,437,b,437)) for a in range(3) for b in range(3))
 need(len(ordered)==942 and [i for i,_ in ordered]==list(range(942)),'ordered old table')
 horizontal=list(range(250))
 for d in (0,1):
  dense_targets=sorted(mapping[q] for q in targets[d])
  for q in targets[d]:horizontal[rails[d][q]]=205-199*d+dense_targets.index(mapping[q])
 vertical=list(range(439))
 for q in range(215):
  for b in range(2):vertical[head(q,b)]=head(mapping[q],b)
 need(sorted(horizontal)==list(range(250)) and sorted(vertical)==list(range(439)),'color bijections')
 tiles=[tuple(r) for r in json.loads(FILES['tiles'][0].read_bytes())]
 need(len(tiles)==943 and len(set(tiles))==943,'compact rows')
 lookup={r:i for i,r in enumerate(tiles)}
 mapped=[]
 for _,(w,n,e,s) in ordered:
  row=(horizontal[w],vertical[n],horizontal[e],vertical[s]);need(row in lookup,'unmatched old row');mapped.append(lookup[row])
 need(sorted(mapped)==[0]+list(range(2,943)),'exact row correspondence')
 need(tiles[0]==(2,435,3,1) and tiles[1]==(5,0,0,0),'start and extra')
 need([i for i,t in enumerate(tiles) if t[0]==5]==[1] and not any(t[2]==5 for t in tiles),'local five exclusion')
 receipt=json.loads(FILES['receipt'][0].read_bytes())
 need(receipt['state_old_to_dense']==sigma and receipt['horizontal_old_to_compact']==horizontal and receipt['vertical_old_to_compact']==vertical and receipt['old_row_to_compact_index']==mapped,'complete permutation receipt')
 normal=subprocess.run([sys.executable,'-I','-S',str(PKG/'check.py')],capture_output=True,timeout=60)
 optimized=subprocess.run([sys.executable,'-O','-I','-S',str(PKG/'check.py')],capture_output=True,timeout=60)
 need(normal.returncode==0 and not normal.stderr and json.loads(normal.stdout)==receipt,'author normal')
 need(optimized.returncode!=0 and b'optimized Python is unsupported' in optimized.stderr,'author optimized fail closed')
 for name,(p,h) in FILES.items():need(sha(p)==h,'post-check drift '+name)
 print(json.dumps({'status':'PASS_INDEPENDENT_COMPACT44_RELABEL_FINITE','action_conjugacies':430,'old_rows':len(ordered),'compact_rows':len(tiles),'horizontal_colors':len(horizontal),'vertical_colors':len(vertical),'extra_index':1,'author_normal_exit':normal.returncode,'author_optimized_exit':optimized.returncode,'scope':'Finite external reconstruction with manually transcribed pinned Lean row formulas; no internal correspondence, arbitrary-model left-neighbor existence, graph calibration or iPRA theorem.'},indent=2))
if __name__=='__main__':main()
