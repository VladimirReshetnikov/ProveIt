#!/usr/bin/env python3
"""Restore the independent macro proof obligations after affine-only folds."""
import argparse,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'sources/context246/zfc-context246'
sys.path.insert(0,str(BASE/'code'))
import check_macro_inductions as macro
import rebuild_machines as rebuild

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--restricted',action='store_true')
    args=ap.parse_args()
    if not __debug__:ap.error('Assertions must be enabled.')
    original=rebuild.build()
    if args.restricted:
        data=json.loads((HERE/'invariant_merge_survivors.json').read_text())
        recipes=[(kind,int(q),int(r)) for kind,rows in data.items() for q,r in rows]
        output='invariant_macro_audit.json'
    else:
        recipes=[('blend',int(q),int(r)) for q,r in json.loads((HERE/'blended_survivors.json').read_text())]
        output='blended_macro_audit.json'
    survivors=[];rejected=[]
    for kind,q,r in recipes:
        table={key:(w,d,r if t==q else t) for key,(w,d,t) in original.items() if key[0]!=q}
        if kind=='blend':
            w,d,t=original[q,0];table[r,0]=(w,d,r if t==q else t)
        macro.TABLE=table;macro.DERIVED.clear();macro.BLOCK_PROOFS.clear();macro.WORD_IDENTITY_PROVED=False
        try:
            macro.prove_blocks();macro.prove_word_identity();macro.prove_macros();macro.prove_marks()
        except (AssertionError,KeyError) as exc:
            rejected.append(dict(kind=kind,remove=q,retain=r,detail=str(exc)))
        else:survivors.append(dict(kind=kind,remove=q,retain=r))
    result=dict(status='COMPLETE',recipes=len(recipes),survivors=survivors,rejected=rejected,
        baseline_old_sha256=rebuild.OLD_FINAL_SHA256,
        scope='Replay the existing exact block/macro/mark induction templates. Rejection alone need not refute every possible different macro contract.')
    (HERE/output).write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='rejected'},indent=2))

if __name__=='__main__':main()
