#!/usr/bin/env python3
"""Three targeted negative controls for the independent pipeline checker."""
from pathlib import Path
import argparse, copy, json
from check_affine import require
from check_pipeline import read, check_mutation, check_factorization, check_projection, digest_object

def run(parent_path,stage):
    parent=read(parent_path);raw=read(stage/'raw_source.json');mutation=read(stage/'mutation.json')
    factored=read(stage/'factored_source.json');fc=read(stage/'factorization_certificate.json')
    projected=read(stage/'projected.json');pc=read(stage/'projection_certificate.json')
    results=[]
    def rejects(label,callback):
        try:
            callback()
        except ValueError as e:
            results.append({'control':label,'rejected':True,'reason':str(e)})
        else:
            raise ValueError('Corruption accepted: '+label)
    # Mutate the exact C=2c interface, while keeping a coherent edit record.
    bad=copy.deepcopy(raw);bm=copy.deepcopy(mutation)
    row=next(r for r in bad['residuals'] if r['label']=='crt.reciprocal_index_congruence')
    term=next(t for t in row['terms'] if t[0]==2 and len(t[1])==1)
    term[0]=1
    edit=next(e for e in bm['edits'] if e['new']['label']=='crt.reciprocal_index_congruence')
    edit['new']=copy.deepcopy(row)
    rejects('C=2c silently weakened to C=c, with edited delta record',lambda:check_mutation(parent,bad,bm))
    # Update the declared digest, so rejection must come from coefficient replay.
    bad=copy.deepcopy(factored);bc=copy.deepcopy(fc)
    bad['residuals'][-1]['terms'][0][0]-=1
    bc['output_sha256']=digest_object(bad)
    rejects('Horn output coefficient changed, with matching output hash',lambda:check_factorization(raw,bad,bc))
    bad=copy.deepcopy(pc)
    term=next(t for t in bad['steps'][0]['restoration'] if t[1]==[])
    term[0]+=1
    if term[0]==0:
        bad['steps'][0]['restoration'].remove(term)
    rejects('First monic restoration changed by one',lambda:check_projection(factored,projected,bad))
    require(len(results)==3,'three targeted controls')
    return {'all_rejected':True,'controls':results}
if __name__=='__main__':
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('parent',type=Path);ap.add_argument('stage',type=Path);ap.add_argument('--receipt',type=Path)
    args=ap.parse_args();result=run(args.parent,args.stage);raw=(json.dumps(result,sort_keys=True,indent=2)+'\n').encode()
    if args.receipt:args.receipt.write_bytes(raw)
    print(raw.decode(),end='')
