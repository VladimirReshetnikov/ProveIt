from map_nodes import *
from split_v import grammar,expanded,word,inc,w
# Guarded splitter: after ordinary guard, drop the leaked V when the top is zero.
# We can simply omit its placeholder: compiler selectors can depend on known guard.
# Wrap first conditional branch so break2 exits the whole conditional.
dec1=('leaf','dec',1);dec6=('leaf','dec',6);cc1=('leaf','continueTo',1);cb2=('leaf','breakTo',1)
clearX='node146'
# Drop leaked top head; leave no placeholder, so failed AX has nine pushes, enabled eleven.
drop=('node17',clearX)
helper=((dec1,(inc,cb2)),drop)
# Shape the extra sequence after the original guard without disrupting original word sharing.
# Delete occurrence at ordinal183 then substitute original final guard macro by (guard,helper).
def edit(t,pos=0):
 if not c.isnode(t):
  if pos==183:return None,pos+1
  if pos==188:return (t,helper),pos+1
  return t,pos+1
 l,k=edit(t[0],pos);r,k=edit(t[1],k)
 return (r if l is None else l if r is None else (l,r)),k
ng,_=edit(expanded(grammar))
# Native table for the original unfolded201 (preserve generic runtime rows).
raw=c.machine()[0]
# All fixed subtrees are available for reuse, but keep only q<1300.
mac=dict(c.MACROS);mac['node17']=105;mac['node146']=196
mac[inc]=61
# Increment-pair shortcuts remain in use.
mac[(inc,inc)]=99;mac[((inc,inc),(inc,inc))]=190
fixed={k:v for k,v in raw.items() if k[0]<1300}
# Break2 scanner consumes first left zero then jumps through existing break1 scanner.
# Existing break1 scanner suffices.
idx={};sh={};rows=fixed.copy()
def state(t):
 if t in mac:return mac[t]
 if t in idx:return idx[t]
 assert c.isnode(t),t
 q=2000+len(idx);idx[t]=q;sh[q]=t
 for b,ch in enumerate(t):
  if ch==cc1:rows[q,b]=(0,False,1)
  elif ch==('leaf','breakTo',1):rows[q,b]=(0,False,302)
  elif ch==cb2:rows[q,b]=(0,False,350)
  elif ch==dec1:rows[q,b]=(b,True,41)
  elif ch==dec6:rows[q,b]=(b,True,21)
  else:rows[q,b]=(b,True,state(ch))
 return q
root=state(ng);rows[101,1]=(1,True,root)
ops=c.opportunities_fast(rows,sh);matching=c.max_matching(ops)
print('PRICE',{'raw':len(rows)//2,'new_readers':len(idx),'fold_upper_bound':len(matching),'count_lower_bound':len(rows)//2-len(matching),'helper_subtrees':len({helper,helper[0],helper[0][1],drop})})
# Source effects of helper alone.
for t in [0,4]:
 regs=[0,t,32,0,0,0,0,0,0]
 try:print('HELPER',regs,run(helper,regs))
 except Exception as e:print('ERROR',str(e))
# Whole-source universal physical contract check. Need modify c.MACROS only, not raw nodes.
sites,ins,cs=c.source(ng)
print('SOURCE',len(sites),len(cs));res=c.validate(rows,cs);print(res)
if not res['ok']:
 site=res['failed'][0];print('FAILINS',site,sites[site],ins[site]);print('MAX',max(len(p) for p,o,a in sites),max(len(z) for p,o,a in sites for z in ''.join(map(str,p)).split('1')))
receipt = {
    'status': 'rejected_source_runtime_contract',
    'pinned_revision': EXPECTED_REVISION,
    'raw_states': len(rows)//2,
    'new_readers': len(idx),
    'fold_upper_bound': len(matching),
    'nominal_state_score': len(rows)//2-len(matching),
    'matching': matching,
    'source_sites': len(sites),
    'contracts': len(cs),
    'runtime_validation': res,
    'physical_machine_validated': False,
    'folded_machine_constructed': False,
}
if not res['ok']:
    bad_site=res['failed'][0]
    receipt['failed_site']=bad_site
    receipt['failed_source']=sites[bad_site]
    receipt['failed_instruction']=ins[bad_site]
    receipt['max_path_length']=max(len(path) for path,op,arg in sites)
    receipt['max_consecutive_zeros']=max(len(part) for path,op,arg in sites for part in ''.join(map(str,path)).split('1'))
(BUNDLE/'split_price.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
