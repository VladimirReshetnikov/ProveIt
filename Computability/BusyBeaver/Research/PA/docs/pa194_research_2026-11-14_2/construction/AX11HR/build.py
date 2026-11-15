from pathlib import Path
import argparse,json,hashlib,shutil
if not __debug__:
 raise SystemExit('Run without Python -O; assertions are certificate checks.')
ROOT=Path(__file__).resolve().parent
SRC=ROOT/'inputs/base'
parser=argparse.ArgumentParser(description='Rebuild the exact PA194AX11HR table and check its whole blank startup.')
parser.add_argument('--output',type=Path,default=ROOT/'machine')
OUT=parser.parse_args().output;OUT.mkdir(parents=True,exist_ok=True)
assert hashlib.sha256((SRC/'machine.tm').read_bytes()).hexdigest()=='c5dfe1026d077d3e062eca11edb789597bfbbced4f6040f8828ae5d467b1167a'
perm=[5,3,1,4,7,0,6,8,2]
oldphy=[6,2,0,4,3,7,8,5,1];phy=[perm[x]for x in oldphy]
sk=[51,36,25,48,32,33,22,55,60]
boxes={0,1,2,3,16,22,25,32,33,36,40,48,51,54,55,60,64,66,74,94,97,113,198}
base={}
for l in (SRC/'machine.native.tm').read_text().splitlines():
 q,b,w,d,n=l.split();base[int(q),int(b)]=(int(w),d,int(n))
rows=base.copy()
for k,(w,d,n)in base.items():
 if k[0]not in boxes and n in sk:rows[k]=(w,d,sk[perm[sk.index(n)]])
def text(rs):return ''.join(f'{q} {b} {w} {d} {n}\n'for(q,b),(w,d,n)in sorted(rs.items()))
qs={q for q,_ in rows};assert len(qs)==194
order=[74];ix={74:0}
for q in order:
 for b in (0,1):
  n=rows[q,b][2]
  if n!=254 and n not in ix:ix[n]=len(order);order.append(n)
assert len(order)==194
dense={(ix[q],b):(w,d,194 if n==254 else ix[n])for(q,b),(w,d,n)in rows.items()}
(OUT/'machine.native.tm').write_text(text(rows));(OUT/'machine.tm').write_text(text(dense))
(OUT/'labels.json').write_text(json.dumps(order+[254])+'\n')
for name in ('sites.json','instructions.json'):shutil.copyfile(SRC/name,OUT/name)
sites=json.loads((OUT/'sites.json').read_text());path=sites[25][0]
if not isinstance(path,str):path=''.join(map(str,path))
expected={-3,46};expected.update(-2+i for i,x in enumerate(path)if x=='1')
values=[0]*9;values[phy[0]]=2;values += [1]*26
p=47
for v in values:p+=1;expected.update(range(p,p+v+1));p+=v+1
q=74;head=0;ones=set();used={k:0 for k in rows if rows[k]!=base[k]};boot=None
for t in range(1,100001):
 k=q,int(head in ones)
 if k in used:used[k]+=1
 w,d,q=rows[k];(ones.add if w else ones.discard)(head);head+=1 if d=='R'else -1
 if q==84 and head==-2 and ones==expected:
  boot=t;break
 if q==254:break
assert boot==48320,(boot,q,head,len(ones))
assert all(n>0 for n in used.values())
assert hashlib.sha256(text(dense).encode()).hexdigest()=='b3c07bf7a750e1e9529929ef392fc0543645ccc34a7a39c3360ec41201f0e980'
receipt={'family':'PA194AX11HR','working_states':194,'transitions':388,'logical_to_physical':phy,'physical_permutation':perm,'source_sites':len(sites),'startup_steps':boot,'base_startup_steps':57922,'changed_rows':[{'state':k[0],'read':k[1],'old':base[k],'new':rows[k],'startup_uses':used[k]}for k in used],'dense_sha256':hashlib.sha256(text(dense).encode()).hexdigest(),'native_sha256':hashlib.sha256(text(rows).encode()).hexdigest(),'base_dense_sha256':hashlib.sha256((SRC/'machine.tm').read_bytes()).hexdigest(),'source_start_site':25,'complete_startup_tape':sorted(ones),'startup_head':head,'startup_native_state':q}
(OUT/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
