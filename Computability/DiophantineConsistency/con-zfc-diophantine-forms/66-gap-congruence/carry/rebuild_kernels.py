"""Rebuild all frozen kernels from source polynomials and positional certificates."""
from pathlib import Path
import json,hashlib,collections
ROOT=Path(__file__).resolve().parent

def rebuild(name,sourcefile):
 cp=ROOT/(name+'_code.json');sp=ROOT/'../source'/sourcefile;code=json.loads(cp.read_text());source=json.loads(sp.read_text())
 sha=hashlib.sha256(sp.read_bytes()).hexdigest()
 if sha!=code['source_sha256']:raise ValueError('Source digest mismatch')
 w=code['weights'];q=code['targets_by_row'];out=[[] for _ in range(3)]
 for j,row in enumerate(source['equations']):
  groups={}
  for t in row['terms']:groups.setdefault(tuple(t['powers'][:31]),[]).append((t['powers'][31:],t['coefficient']))
  for a,coeffs in groups.items():
   d=sum(a);e=q[j]-sum(i*v for i,v in zip(a,w));scale=(2 if d<2 or max(a)==2 else 1)*code['row_orientations'][j]
   out[d].append({'exponent':e,'coefficient':[{'powers':p,'coefficient':scale*c} for p,c in coeffs]})
 data={'variables_count':31,'ports':['beta','K0','MC','MF'],'source_sha256':sha,'formula':'G(B,U)=D2(B)*U^2+D1(B)*U+D0(B)','kernels':[{'degree':d,'terms':sorted(out[d],key=lambda t:t['exponent'])} for d in range(3)],'code_sha256':hashlib.sha256(cp.read_bytes()).hexdigest()}
 return (json.dumps(data,indent=2)+'\n').encode()

def main():
 receipt=[]
 for item in json.loads((ROOT/'CERTIFICATES.json').read_text()):
  name=item['name'];sf='gapNq85_source.json' if name.startswith('gapNq') else 'gapN86_source.json';data=rebuild(name,sf);path=ROOT/(name+'_kernels.json')
  if data!=path.read_bytes():raise ValueError('Kernel rebuild differs: '+name)
  receipt.append({'name':name,'sha256':hashlib.sha256(data).hexdigest(),'status':'BYTE_IDENTICAL'})
 print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
