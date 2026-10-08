import json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]; sys.path.insert(0,str(ROOT/'src'))
from graded_scan import scan,Limits

def run():
 rows=[]
 cases=[(f'torus4_{m}',4,[1,2,3]*m) for m in (1,2,3,4,6,8,12,16)]
 cases += [('mixed_blocks',4,[1,2,3]*4+[-2]+[-3,-2,-1]*3+[2,1]),
           ('weaving4_3',4,[1,-2,3]*3),('weaving4_4',4,[1,-2,3]*4)]
 for name,s,w in cases:
  try:
   r=scan(s,w,limits=Limits(seconds=12))
   row=dict(name=name,strands=s,word=w,crossings=len(w),status='COMPLETE',seconds=r['seconds'],
            homology=r['bigraded_homology'],rank=r['unreduced_rank'],trace=r['trace'])
  except (TimeoutError,MemoryError) as exc:
   row=dict(name=name,strands=s,word=w,crossings=len(w),status='NO_VERDICT',error=str(exc))
  rows.append(row); (ROOT/'results'/'growth.json').write_text(json.dumps({'results':rows},indent=2)+'\n')
  print(name,row['status'],row.get('seconds'),flush=True)
if __name__=='__main__':run()
