"""A finite discovery contract preserving the proved START/reset interface.

For contract a_lt_c, only whole AX gate inputs a<c may leave D4 arbitrary.
For the broader c_positive contract, c=0 still requires D4=0, while c>0
may leave D4 arbitrary. At an unequal MP comparison exit D4 may also be
arbitrary. Every other field keeps its previous required value.
A concrete hit needs a separate unbounded runtime and completeness proof.
"""
from pathlib import Path
import argparse,json,struct,shutil
R=Path(__file__).resolve().parent
PACKET=R.parent;PACKAGED=(PACKET/'fixtures/combined').is_dir()
ap=argparse.ArgumentParser(description=__doc__)
ap.add_argument('--input',type=Path,default=PACKET/'fixtures/combined' if PACKAGED else R/'whole_primitive/k219_gate_combined')
ap.add_argument('--output',type=Path,default=PACKET/'regenerated/gate_dead_d' if PACKAGED else R/'whole_primitive/k219_gate_dead_d')
ap.add_argument('--contract',choices=['a_lt_c','c_positive'],default='a_lt_c')
args=ap.parse_args();P=args.input;O=args.output;O.mkdir(parents=True,exist_ok=True)
data=bytearray((P/'frames.bin').read_bytes());nf,sz,off=struct.unpack_from('<3i',data);stride=20+2*sz
meta=json.loads((P/'frame_metadata.json').read_text());changed={'gate_relaxed':0,'unequal_mp':0}
for k,m in enumerate(meta):
    flags=struct.unpack_from('<i',data,12+k*stride+4)[0];mask=511
    gate_relaxed=m.get('macro')==0 and(m['a']<m['c']if args.contract=='a_lt_c'else m['c']>0)
    if gate_relaxed:mask^=1<<4;changed['gate_relaxed']+=1
    if m.get('macro')==2 and not m['equal']:mask^=1<<4;changed['unequal_mp']+=1
    struct.pack_into('<i',data,12+k*stride+4,flags|(mask<<6));m['live_register_mask']=mask
(O/'frames.bin').write_bytes(data)
(O/'frame_metadata.json').write_text(json.dumps(meta,separators=(',',':'))+'\n')
for n in['witnesses.txt','macros.txt','intervals.txt']:shutil.copyfile(P/n,O/n)
condition='a<c'if args.contract=='a_lt_c'else'c>0'
rec=dict(scope='Finite discovery oracle with proof-level reset-preserving D4 relaxation; no mutant correctness claim.',contract=args.contract,total_frames=nf,relaxed_frames=changed,required_condition=f'Whole gate D4 may vary only if {condition}; MP D4 may vary only on inequality. All remaining primary fields strict.')
(O/'receipt.json').write_text(json.dumps(rec,indent=2)+'\n');print(json.dumps(rec))
