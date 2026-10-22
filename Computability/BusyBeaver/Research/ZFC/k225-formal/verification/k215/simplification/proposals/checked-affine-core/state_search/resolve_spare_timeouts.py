#!/usr/bin/env python3
"""Resolve bounded failures using full finite-tape translation cycles.

A repeated (control, sorted set of one-cell positions relative to the head)
is exact equality up to tape translation, including the infinite zero
exterior. Determinism and translation equivariance prove divergence if no
halt occurred between repetitions. Outward blank rays are also exact.
"""
from search_existential_spares import parse,frame,decode,expect
from pathlib import Path
import argparse,json,time,hashlib

def resolve(t,c,witness,cap):
    site=witness['site'];regs=witness['registers'];one=frame(site[0],regs,witness['spares'],witness['gap']);q=83;h=0;want=expect(site,regs);mut=(tuple(c['incoming']),tuple(c['replacement']));seen={};beg=time.time()
    for tick in range(cap+1):
        if q==215:return {'kind':'halt','steps':tick,'expected_halt':want is None}
        if tick and q==83:
            got=decode(h,one)
            if got is not None:
                good=want is not None and got[0]=={i for i,b in enumerate(want[0]) if b=='1'} and got[1]==want[1]
                return {'kind':'decoded_frame','steps':tick,'head':h,'matches':good,'pc_one_positions':sorted(got[0]),'registers':got[1],'spares':got[2],'gap':got[3]}
        key=(q,tuple(sorted(x-h for x in one)))
        if key in seen:
            start,oldh=seen[key]
            return {'kind':'exact_translation_cycle','first_step':start,'second_step':tick,'period':tick-start,'head_displacement':h-oldh,'state':q,'relative_one_cells':list(key[1]),'seconds':time.time()-beg}
        seen[key]=(tick,h)
        if tick==cap:break
        b=int(h in one);w,d,z=mut[1] if (q,b)==mut[0] else t[q,b]
        if not b and z==q and ((d>0 and h>max(one)) or(d<0 and h<min(one))):
            return {'kind':'exact_outward_blank_ray','steps':tick,'state':q,'head':h,'direction':d,'write':w,'one_cells':sorted(one)}
        if w:one.add(h)
        else:one.discard(h)
        q=z;h+=d
    return {'kind':'unresolved_bound','steps':cap,'one_count':len(one),'seconds':time.time()-beg}

def main():
    ap=argparse.ArgumentParser();ap.add_argument('table');ap.add_argument('refinement');ap.add_argument('--cap',type=int,default=200000);ap.add_argument('--out',default='existential_spare_timeout_resolution.json');a=ap.parse_args();t=parse(a.table);xx=json.loads(Path(a.refinement).read_text());rr=[]
    for c in xx['rejections']:
        if 'bound' not in c['witness']['actual']:continue
        v=resolve(t,c,c['witness'],a.cap);rr.append({'candidate':{k:c[k]for k in ['removed','incoming','replacement']},'input':{k:c['witness'][k]for k in ['site_index','site','registers','spares','gap']},'result':v});print(c['removed'],c['replacement'],v['kind'],v.get('steps',v.get('second_step')),flush=True)
    result={'table_sha256':hashlib.sha256(Path(a.table).read_bytes()).hexdigest(),'refinement_sha256':hashlib.sha256(Path(a.refinement).read_bytes()).hexdigest(),'maximum_steps':a.cap,'resolutions':rr};Path(a.out).write_text(json.dumps(result,indent=2)+'\n')
if __name__=='__main__':main()
