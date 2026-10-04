"""Build coefficient-ready static profiles using own JSON-only finite scans.
Bits0..399 encode local y50..449. Positive and negative correction masks are disjoint.
Never imports/executes upstream code or accesses a schedule decoder.
"""
import argparse,json,hashlib,struct
from pathlib import Path
from verify_profiles import H,B,F,S,maps,union,shift,black
parser=argparse.ArgumentParser();parser.add_argument('--out',required=True);args=parser.parse_args()
OUT=Path(args.out);OUT.mkdir(exist_ok=False)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def masks(parts):
 cols={}
 for label,d,dx in parts:
  for (x,y),c in d.items():
   assert 50<=y<450
   if c==1:
    x=(x+dx)%S
    cols[x]=cols.get(x,0)|(1<<(y-50))
 return cols
summary={'format':'400-bit black-column masks with x modulo576000; bitb means y=50+b','S':S,'height':400,'profiles':{},'corrections':{}}
for name,parts in [('H',H),('B',B),('F',F)]:
 cols=masks(parts);unique=[0];index={0:0};ids=[]
 for x in range(S):
  m=cols.get(x,0)
  if m not in index:index[m]=len(unique);unique.append(m)
  ids.append(index[m])
 assert len(unique)<65536
 binary=OUT/f'{name}.u16le';binary.write_bytes(struct.pack('<'+'H'*len(ids),*ids))
 dictionary=OUT/f'{name}.masks.json';dictionary.write_text(json.dumps({'y0':50,'height':400,'mask_hex_by_id':[format(v,'x') for v in unique]},separators=(',',':'))+'\n')
 summary['profiles'][name]={'column_ids_file':binary.name,'column_ids_encoding':'little-endian uint16;576000 entries','dictionary_file':dictionary.name,'unique_profiles_including_zero':len(unique),'nonzero_columns':len(cols),'black_cells':sum(v.bit_count() for v in cols.values()),'column_ids_sha256':sha(binary),'dictionary_sha256':sha(dictionary)}
base=black(union(maps['DELAY'],shift(maps['DELAY'],600)))
for kind in ['DUP','MOVE_LEFT','MOVE_RIGHT','NAND']:
 target=black(maps[kind]);plus=target-base;minus=base-target
 pc={};mc={}
 for source,dest in [(plus,pc),(minus,mc)]:
  for x,y in source:
   assert 0<=x<1200 and 50<=y<450
   dest[x]=dest.get(x,0)|(1<<(y-50))
 unique=[(0,0)];index={(0,0):0};ids=[]
 for x in range(1200):
  m=(pc.get(x,0),mc.get(x,0));assert not(m[0]&m[1])
  if m not in index:index[m]=len(unique);unique.append(m)
  ids.append(index[m])
 p=OUT/f'Q_{kind}.json';p.write_text(json.dumps({'x0':0,'width':1200,'y0':50,'height':400,'signed_masks_by_id':[[format(a,'x'),format(b,'x')]for a,b in unique],'profile_id_by_dx':ids},separators=(',',':'))+'\n')
 summary['corrections'][kind]={'file':p.name,'sha256':sha(p),'plus_cells':len(plus),'minus_cells':len(minus),'unique_profiles_including_zero':len(unique),'nonzero_columns':len(set(pc)|set(mc))}
p=OUT/'MANIFEST.json';p.write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
