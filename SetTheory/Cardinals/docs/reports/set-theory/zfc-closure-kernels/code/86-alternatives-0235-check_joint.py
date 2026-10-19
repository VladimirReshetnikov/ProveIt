from pathlib import Path
import sys, json, time, hashlib
R=Path(__file__).resolve().parents[1]
P=R/'context_folds/recovered/67/research'
sys.path.insert(0,str(P/'agent_logic'))
import verify_rotated246 as v
B=P/'sources/context246/zfc-context246'
sys.path.insert(0,str(B/'code'))
base,start,halt=v.read_tm(B/'machine/zfc_prefix246_old.tm')
rot,_,_=v.read_tm(P/'agent_state/rebracket/unshared246.tm')
det,_,_=v.read_tm(R/'context_folds/recovered/64/experiments/decoder/detector8-context246.tm')
rd={k:a for k,a in rot.items() if a!=base[k]}
dd={k:a for k,a in det.items() if a!=base[k]}
assert not(rd.keys() & dd.keys()), (rd,dd)
table=base|rd|dd
out=Path(__file__).parent
(out/'joint246_old.tm').write_text(v.encode_tm(table,start))
print('changes',len(rd),len(dd),flush=True)
macro=v.load_module(B/'code/check_macro_inductions.py','joint_macros')
proofs,support=v.replay_inductions(macro,table)
assert all(table[k]==base[k] for k in support)
affine=v.load_module(B/'sources/prior/prefix_affine.py','joint_affine')
nodes,root,_=v.read_json(P/'root_search/rebracket202_minimal.json')
source=v.Decoder(nodes,root)
t=time.time()
instructions,used=v.check_instructions(affine,table,source)
print('instructions passed',time.time()-t,flush=True)
boot=v.dense_boot(table,start,halt,96,steps=409449)
result={'status':'PASS','states':len(table)//2,'sha256':hashlib.sha256((out/'joint246_old.tm').read_bytes()).hexdigest(),'instructions':instructions,'bootstrap':boot,'changes':[[*k,*a] for k,a in sorted((rd|dd).items())],'macro_support':sorted(support),'seconds':time.time()-t}
(out/'joint246_check.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
