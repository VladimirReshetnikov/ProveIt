"""Bounded continuation audit: do not overstate instruction-segment rejection."""
import json
import independent_runtime as r
T=r.table(r.OUT/'candidates/candidate_reassociation244_old.tm')
site=['111010010010000000','CD',1];regs=[0]*9
wanted=r.expected(site,regs,[1])[0];ones=r.frame(site[0],regs,[1]);q=96;h=0;seen={};frame_count=0
report=None
for tick in range(2000001):
 if q==96:
  if tick and (q,h,ones)==wanted:
   report={'status':'REQUIRED_TARGET_EVENTUALLY_REACHED','steps':tick,'clean_frames':frame_count};break
  if r.clean_dispatch(q,h,ones):
   frame_count+=1;k=(q,h,tuple(sorted(ones)))
   if k in seen:
    report={'status':'EXACT_CYCLE_WITHOUT_REQUIRED_TARGET','steps':tick,'cycle_start':seen[k],'period':tick-seen[k],'clean_frames':frame_count};break
   seen[k]=tick
 b=int(h in ones)
 if (q,b) not in T:
  report={'status':'HALTED_WITHOUT_REQUIRED_TARGET','steps':tick,'state':q,'head':h,'clean_frames':frame_count};break
 w,d,q=T[q,b]
 if w:ones.add(h)
 else:ones.discard(h)
 h+=d
else:report={'status':'NO_REQUIRED_TARGET_WITHIN_BOUND','bound':2000000,'state':q,'head':h,'clean_frames':frame_count,'not_a_nonreachability_proof':True}
(r.OUT/'obvious244_witness_continuation.json').write_text(json.dumps(report,indent=2)+'\n');print(report)
