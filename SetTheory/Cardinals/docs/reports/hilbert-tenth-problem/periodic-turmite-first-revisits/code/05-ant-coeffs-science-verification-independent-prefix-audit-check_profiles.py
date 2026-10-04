#!/usr/bin/env python3
"""Independent finite-set audit of canonical profiles.

The upstream atlas is not imported or executed. We independently project finite
geometric motif placements onto three synthetic macro windows (R=2); every
retained window has the same symbolic neighbors for the true R>=2. In contrast
to the proposed profile builder, no special header/footer overlap is omitted by
hand: all intersecting placements are unioned and checked for color conflicts.
"""
import hashlib
import json
import struct
from pathlib import Path

ROOT=Path('/workspace/shared/report44-recovery-20261004/certificate/dependencies/recipe_assets')
PROFILES=Path('/workspace/shared/ant-motif-overlap/profiles')
HERE=Path(__file__).resolve().parent

def need(ok,why):
    if not ok:raise ValueError(why)

def read(rel):return json.loads((ROOT/rel).read_text())
def blackmap(rel):return {(x,y):c for x,y,c in read(rel)['board']}
def shift(m,dx=0,dy=0):return {(x+dx,y+dy):c for (x,y),c in m.items()}

def run():
    data=read('ca/physical_program.json')
    S=data['CA_macro_width'];slots=data['tile_slots'];stride=data['selected_slot_stride']
    need(S==600*slots,'Slot width')
    hm=1+12*stride;rm=1+23*stride
    maps={name:blackmap(rel) for name,rel in {
        'N':'not/normalized_not.json','C':'copy/normalized_copy.json',
        'D':'copy/delayed_copy.json','LM':'copy/marker_left_start.json',
        'RM':'copy/marker_right_stop.json'}.items()}
    routes=read('strip/periodic_benchmark.json')['right_and_left_turn_routes']
    maps['RT']={(x-1200,y):c for x,y,c in routes[0]['cells']}
    maps['LT']={(x,y):c for x,y,c in routes[1]['cells']}
    primitive=read('common/primitive_maps.json')
    maps['EN']={(x,y):c for x,y,c in primitive['cable_c']['cell_map']}
    maps['NE']={(y,-x):c for x,y,c in primitive['cable_b']['cell_map']}
    # Synthetic geometry preserves every finite overlap at any actual R>=2.
    R=2;V=400*(R+2);F=400*(R+1);edge=600*(slots-1)
    placements=[]
    for phase in (-1,0,1):
        oy=phase*V;ox=(phase%2)*(S//2)
        for k in range(1,slots-1):
            if k!=hm:placements.append(('N',ox+600*k,oy))
            placements.append(('C',ox+600*k,oy+200))
            for r in range(1,R+1):placements.append(('D',ox+600*k,oy+400*r))
            if k!=rm:placements.append(('N',ox+600*k,oy+F))
        for r in range(R+1):
            placements.append(('LT',ox+600,oy+400*r))
            placements.append(('RT',ox+edge,oy+400*r))
        for k in range(slots):
            if k==1:placements.append(('LM',ox+600*k,oy+F))
            elif k==rm:placements.append(('RM',ox+600*k,oy+F))
            else:placements.append(('C',ox+600*k,oy+F+200))
        placements.append(('EN',ox+edge+170,oy+F+70))
        placements.append(('NE',ox+edge+174,oy+79))
        maps['EAST']= {(t,b-1):b for t in range(170) for b in (0,1)}
        maps['TOP']= {(t,b-1):b for t in range(1020) for b in (0,1)}
        maps['UP']= {(b-1,t):b for t in range(80,F+70) for b in (0,1)}
        placements.append(('EAST',ox+edge,oy+F+75))
        placements.append(('TOP',ox+edge+180,oy+75))
        placements.append(('UP',ox+edge+175,oy))
    bounds={name:(min(y for x,y in m),max(y for x,y in m)) for name,m in maps.items()}
    result={};computed={}
    for name,start in (('H',50),('B',450),('B_last',850),('F',F+50)):
        white=[0]*S;black=[0]*S;cache={};used=0
        for key,dx,dy in placements:
            ymin,ymax=bounds[key]
            if dy+ymax<start or dy+ymin>=start+400:continue
            used+=1
            relative=dy-start;cachekey=key,relative
            if cachekey not in cache:
                cols={}
                for (x,y),c in maps[key].items():
                    b=y+relative
                    if 0<=b<400:
                        if x not in cols:cols[x]=[0,0]
                        cols[x][c]|=1<<b
                cache[cachekey]=cols
            for x,(w,b) in cache[cachekey].items():
                a=(x+dx)%S
                need(not (white[a]&b or black[a]&w),('Color conflict',name,key,a,relative))
                white[a]|=w;black[a]|=b
        file_name='B' if name=='B_last' else name
        source=json.loads((PROFILES/f'{file_name}.masks.json').read_text())
        dictionary=[int(v,16) for v in source['mask_hex_by_id']]
        ids=list(struct.unpack('<'+'H'*S,(PROFILES/f'{file_name}.u16le').read_bytes()))
        need(len(black)==len(ids),'Wrong column count')
        mismatch=[x for x in range(S) if black[x]!=dictionary[ids[x]]]
        need(not mismatch,('Profile mismatch',name,mismatch[:20]))
        result[name]=dict(all_columns_equal=True,columns=S,black_cells=sum(x.bit_count() for x in black),
                          colored_cells=sum(x.bit_count()+y.bit_count() for x,y in zip(white,black)),
                          distinct_masks=len(set(black)),nonzero_columns=sum(x!=0 for x in black),
                          intersecting_placements=used,conflicts=0)
        computed[name]=black
    # Audit the shared Horner cache count independently from concrete profile data.
    keys={(400,v,0) for a in computed.values() for v in a if v}
    keys|={(25,v&((1<<25)-1),0) for v in computed['H'] if v&((1<<25)-1)}
    keys|={(375,v>>25,0) for v in computed['H'] if v>>25}
    correction_columns={}
    for kind in ('DUP','NAND','MOVE_LEFT','MOVE_RIGHT'):
        q=json.loads((PROFILES/f'Q_{kind}.json').read_text())
        pairs=[(int(a,16),int(b,16)) for a,b in q['signed_masks_by_id']]
        keys|={(400,a,b) for a,b in pairs if a or b}
        ids=q['profile_id_by_dx'];correction_columns[kind]=sum(bool(pairs[i][0] or pairs[i][1]) for i in ids)
    width_count={w:sum(k[0]==w for k in keys) for w in (25,375,400)}
    cost=sum(w-1 for w,a,b in keys)
    result['cache']=dict(distinct_by_width=width_count,profiles=len(keys),Horner_M=cost,Horner_A=cost,correction_columns=correction_columns)
    result['method']='Finite geometric projections only; no upstream modules, row decoder, saved schedule, ant dynamics or color queries were executed'
    result['synthetic_R']=R
    result['checker_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (HERE/'profiles-receipt.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':run()
