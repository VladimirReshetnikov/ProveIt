#!/usr/bin/env python3
"""Compose a certified incoming AX override with the coupled LM backend.

This is a syntactic input constructor. The incoming DNE change and the clean
constructor interface both need their separate logical correctness arguments.
"""
from pathlib import Path
import argparse, json

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--backend',type=Path,required=True)
    p.add_argument('--inherited',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();a.output.mkdir(parents=True,exist_ok=True)
    meta=json.loads((a.backend/'backend.json').read_text())
    inherited=json.loads(a.inherited.read_text())['source_override']
    assert inherited['state']==76 and inherited['original_word']==meta['old_names']['76']
    def contract(w):
        result=w.replace('LNPQMVQPW','LMPW')
        assert 'LNPQM' not in result,'AX prefix contraction needs its own interface proof'
        return result
    old=meta['names']['76'];new=contract(inherited['new_word'])
    assert old==contract(inherited['original_word'])
    meta['source_override']=dict(state=76,original_word=old,new_word=new,inherited_fine_override=inherited)
    meta['names']['76']=new;meta['roots']=[new if w==old else w for w in meta['roots']]
    (a.output/'backend.json').write_text(json.dumps(meta,indent=2)+'\n')
    for name in ('grammar.txt','constraints.txt'):
        text=(a.backend/name).read_text()
        text=text.replace('\n'+old+'\n','\n'+new+'\n').replace('W '+old+'\n','W '+new+'\n')
        (a.output/name).write_text(text)
    (a.output/'locks.txt').write_bytes((a.backend/'locks.txt').read_bytes())
    print(json.dumps(dict(status='COMPOSED_LM_AX_INPUT',old_tokens=len(old),new_tokens=len(new),inherited_mask=inherited.get('mask'))))

if __name__=='__main__':main()
