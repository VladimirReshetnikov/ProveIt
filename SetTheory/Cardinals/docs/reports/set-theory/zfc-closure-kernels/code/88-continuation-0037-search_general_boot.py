#!/usr/bin/env python3
"""Literal search for an empty-root canonical frame under dirty calibration.

This is finite evidence. Every represented one is checked and the entire
outside tape remains zero by the literal finite-support representation.
"""
from pathlib import Path
import argparse,json,time
import check_candidate_boot as boot
PHYSICAL=(6,2,0,4,3,7,8,5,1)
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--table',type=Path,required=True);ap.add_argument('--moves',type=int,default=20000000);ap.add_argument('--output',type=Path,required=True);a=ap.parse_args()
 T=boot.table(a.table);q=95;h=0;ones=set();frames=[];found=None;lo=hi=0;start=time.monotonic()
 for step in range(a.moves):
  if q==254:break
  w,d,q=T[q,int(h in ones)];(ones.add if w else ones.discard)(h);h+=d;lo=min(lo,h);hi=max(hi,h)
  if q!=96 or h-1 not in ones or min(ones)!=h-1:continue
  right=sorted(p for p in ones if p>=h)
  if not right or right[0]-h<64:continue
  header=right[0];values=[];pos=header+1;end=right[-1];valid=True
  while pos<end:
   if pos in ones or pos+1 not in ones:valid=False;break
   j=pos+1
   while j in ones:j+=1
   values.append(j-pos-2);pos=j
  if not valid or len(values)<10:continue
  logical=[values[i] for i in PHYSICAL]
  f=dict(step=step+1,head=h,header_distance=header-h,primaries=values[:9],logical_primaries=logical,spares_count=len(values)-9)
  if len(frames)<100:frames.append(f)
  if logical[1]==logical[2]==logical[5]==0:
   found=dict(f,ones=sorted(ones),spares=values[9:]);break
 result=dict(found_frame=found,examined_moves=step+1,first_empty_pc_frames=frames,halted=q==254,head_range=[lo,hi],seconds=time.monotonic()-start,calibration='T=H=W=0; six other logical primaries arbitrary; nonempty natural spares; gap>=64; pc empty')
 a.output.write_text(json.dumps(result,indent=2)+'\n');print({k:v for k,v in result.items() if k!='first_empty_pc_frames'});print('empty_root_frames',len(frames))
if __name__=='__main__':main()
