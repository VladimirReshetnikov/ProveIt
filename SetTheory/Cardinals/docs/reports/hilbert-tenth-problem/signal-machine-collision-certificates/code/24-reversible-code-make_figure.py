#!/usr/bin/env python3
"""New figure generator. Only the inspected candidate checker is imported.
Run with Python 3; matplotlib is required only for PDF figure regeneration.
"""
import csv, hashlib, importlib.util, json, os, sys
from pathlib import Path
sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[1]
src = ROOT/'frozen/candidate/check_reversible_clock.py'
spec = importlib.util.spec_from_file_location('report49_checked_rule',src)
r = importlib.util.module_from_spec(spec);sys.modules[spec.name]=r;spec.loader.exec_module(r)
def trace():
 s=r.section(13);records=[];hits=[]
 for t in range(55):
  k=max(k for k in range(7) if k*k+3*k<=t);D=13+k;local=t-(k*k+3*k)
  r.require(s==r.phase(D,local),'figure orbit formula')
  h=r.hit(s)
  if h:hits.append(t)
  r.require(len(s)==4,'figure particle count')
  records.append([t,*sorted(s),int(h)])
  s=r.forward(s)
 r.require(hits==[0,4,10,18,28,40,54],'figure hit times')
 return records,hits

def main():
 import argparse
 p=argparse.ArgumentParser();p.add_argument('--output-dir',type=Path,default=ROOT/'figures');p.add_argument('--trace-only',action='store_true');a=p.parse_args()
 a.output_dir.mkdir(parents=True,exist_ok=True);records,hits=trace()
 with (a.output_dir/'clock-spacetime.csv').open('w',newline='') as f:
  w=csv.writer(f,lineterminator='\n');w.writerow(['time','particle_1','particle_2','particle_3','particle_4','exact_hit']);w.writerows(records)
 receipt={'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'steps':54,'observations':55,'hits':hits,'particle_count':4,'generation':'Literal guarded rule; formula used only as independent comparison'}
 (a.output_dir/'figure-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n')
 if a.trace_only:return
 import matplotlib;matplotlib.use('Agg')
 import matplotlib.pyplot as plt
 plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'pdf.fonttype':42,'axes.spines.top':False,'axes.spines.right':False})
 fig,(ax,bx)=plt.subplots(1,2,figsize=(7.1,4.65),gridspec_kw={'width_ratios':[3.4,1.35]})
 for i in range(6):
  ax.axhspan(hits[i]-.45,hits[i+1]-.45,color=('#eef3f6' if i%2==0 else '#ffffff'),zorder=0)
 for rec in records:
  t,*rest=rec;pts=rest[:4]
  ax.scatter(pts,[t]*4,s=13,marker='s',c=['#7a8790','#14749d','#14749d','#ba6a27'],linewidths=0,zorder=3)
 for h in hits:ax.axhline(h,color='#8da3b0',ls=(0,(2,3)),lw=.6,zorder=1)
 ax.set_xlim(-.8,20);ax.set_ylim(55.2,-1.2);ax.set_xticks([0,5,10,15,19]);ax.set_yticks([0,10,20,30,40,50,54]);ax.set_xlabel('Site');ax.set_ylabel('Time');ax.set_title('Four particles under the literal rule',loc='left',fontsize=11,pad=11)
 bx.set_axis_off();bx.set_title('Exact anchored hits',loc='left',fontsize=11,pad=11)
 bx.text(.05,.95,'k      time      next gap',va='top',fontsize=9,color='#485661')
 for k,h in enumerate(hits):bx.text(.05,.85-k*.10,f'{k:<7}{h:<10}{2*k+4}',va='top',fontsize=11,fontfamily='DejaVu Sans Mono')
 bx.text(.05,.06,'Word: 1000011\nSites: 0 through 6\nInitial right marker: 13',va='bottom',fontsize=9,linespacing=1.7,color='#485661')
 fig.tight_layout(w_pad=2)
 fig.savefig(a.output_dir/'clock-spacetime.pdf',metadata={'Creator':'Report49 make_figure.py','CreationDate':None,'ModDate':None})
 plt.close(fig)
if __name__=='__main__':main()
