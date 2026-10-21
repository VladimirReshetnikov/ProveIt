#!/usr/bin/env python3
"""Unpack and bind the saved physical-search inputs; writes only to --out."""
from pathlib import Path
import argparse,gzip,hashlib,json
from local_invariants import read

def digest(raw):return hashlib.sha256(raw).hexdigest()
def need(ok,message):
    if not ok:raise ValueError(message)
def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--out',type=Path,required=True);a=p.parse_args()
    here=Path(__file__).resolve().parent;root=here.parents[1]
    meta=json.loads((here/'inputs.json').read_text());need(meta['format']=='gc215_physical_search_inputs_v1','Input format')
    a.out.mkdir(parents=True,exist_ok=True);results={}
    for name,item in meta['inputs'].items():
        table_path=root/item['table'];need(digest(table_path.read_bytes())==item['table_sha256'],'Table hash')
        packed=(here/item['compressed_file']).read_bytes();need(digest(packed)==item['compressed_sha256'],'Compressed hash')
        raw=gzip.decompress(packed);need(digest(raw)==item['uncompressed_sha256'],'Invariant hash')
        inv=json.loads(raw);need(inv['radius']==5 and inv['blank_window']is False,'Invariant domain')
        need(sum(map(len,inv['masks'].values()))==inv['configs']==item['configurations'],'Configuration census')
        need(inv['unreachable_rows']==item['absent_rows']==[],'Absent rows')
        need(len(inv['distinguishable_pairs'])==item['conditional_pairs']==31,'Conditional pair census')
        (a.out/f'{name}.invariant5.json').write_bytes(raw)
        T,start=read(table_path);states=sorted(map(int,inv['masks']))
        need(states==sorted({q for q,b in T})and start==0,'Table controls')
        need({z for w,d,z in T.values()}-set(states)=={254},'Native halt convention')
        need(all(0<=q<1000 for q in states),'C++ state-array limit')
        lines=[f'5 {start} {len(states)}']
        for q in states:
            masks=inv['masks'][str(q)]
            lines.append(' '.join(map(str,[q,*T[q,0],*T[q,1],len(masks),*masks])))
        cpp_raw=('\n'.join(lines)+'\n').encode('ascii')
        if 'cpp_input_sha256'in item:need(digest(cpp_raw)==item['cpp_input_sha256'],'Original C++ input hash')
        (a.out/f'{name}.invariant5.txt').write_bytes(cpp_raw)
        results[name]={'table_sha256':item['table_sha256'],'invariant_sha256':digest(raw),
                       'cpp_input_sha256':digest(cpp_raw),'configurations':inv['configs']}
    receipt={'status':'PHYSICAL_INPUT_PREPARATION_PASS','inputs':results}
    (a.out/'prepared.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2))
if __name__=='__main__':main()
