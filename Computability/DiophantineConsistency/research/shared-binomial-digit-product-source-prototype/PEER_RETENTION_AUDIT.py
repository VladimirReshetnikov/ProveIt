#!/usr/bin/env python3
"""Independent complete old/new retained-coordinate and row census; no engine imports."""
import argparse,json,sys
from collections import Counter
from hashlib import sha256
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
OLD=ROOT/'research/shared-remainder-product-source-prototype'
def need(ok,why):
    if not ok:raise ValueError(why)
def load(p):return json.loads(p.read_bytes())
def digest(p):return sha256(p.read_bytes()).hexdigest()
def main():
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--output',type=Path,required=True);args=ap.parse_args()
    pins=load(HERE/'SOURCE_PINS.json')['files']
    for n,h in pins.items():need(digest(ROOT/n)==h,'whole immutable input '+n)
    for n,h in load(OLD/'MANIFEST.json')['files'].items():need(digest(OLD/n)==h,'whole frozen557 member '+n)
    for n,h in load(HERE/'BUILD.json')['files'].items():need(digest(HERE/n)==h,'whole new generated member '+n)
    cuts=load(HERE/'CUTS.json');vm=dict(cuts['retained_old_variable_map']);rm=dict(cuts['retained_parent_rows'])
    need(len(vm)==len(set(vm.values())) and len(rm)==len(set(rm.values())),'injective full parent maps')
    need(set(range(1436))-set(vm)=={1319,1320,1321,1358,1359,1360},'only six old auxiliaries unmapped')
    need(set(range(1242))-set(rm)=={1203,1216},'only two old guard rows unmapped')
    census=load(HERE/'CENSUS.json');oldc=load(OLD/'CENSUS.json');profiles={};classes=Counter()
    need(set(census)==set(oldc) and len(census)==24,'all24 paired profiles')
    for name in sorted(census):
        old=load(OLD/name/'projection.json');new=load(HERE/name/'projection.json')
        ov=set(old['retained_original_variables']);nv=set(new['retained_original_variables']);orr=set(old['retained_original_rows']);nr=set(new['retained_original_rows'])
        mappedv={vm[v] for v in ov if v in vm};mappedr={rm[r] for r in orr if r in rm}
        lostv=sorted(mappedv-nv);lostr=sorted(mappedr-nr);unmappedv=sorted(ov-set(vm));unmappedr=sorted(orr-set(rm));extrav=sorted(nv-mappedv);extrar=sorted(nr-mappedr)
        need(not lostv and not lostr,'no other mapped retained coordinate or row loss '+name)
        need(unmappedv==[1319,1320,1321,1358,1359,1360],'all six removed auxiliary coordinates previously retained '+name)
        affine2=name.split('/')[1] in ['support4_affine2','support8_affine2','support16_affine2','support32_affine2']
        need(extrav==([564,1319,1320,1321] if affine2 else [1319,1320,1321]),'complete extra retained variables '+name)
        need(unmappedr==([1203] if affine2 else [1203,1216]) and extrar==[1203],'complete guard row changes '+name)
        a,b=oldc[name]['metrics'],census[name]['metrics'];keys=['variables','quadratic_rows','expanded_monomials','max_abs_expanded_coefficient'];delta=tuple(b[k]-a[k] for k in keys);classes[delta]+=1
        need(b['variables']==len(nv) and b['quadratic_rows']==len(nr),'actual full retained dimensions '+name)
        profiles[name]=dict(unmapped_old_retained_variables=unmappedv,mapped_retained_variables_lost=lostv,new_retained_variables=extrav,unmapped_old_retained_rows=unmappedr,mapped_retained_rows_lost=lostr,new_retained_rows=extrar,delta=dict(zip(keys,delta)))
    need(classes==Counter({(-3,-1,-13,0):6,(-2,0,-16,0):8,(-3,-1,-10,0):10}),'all24 actual delta classes')
    report=dict(status='PASS',optimized_python=bool(sys.flags.optimize),profiles=profiles,whole24_profiles=True,optimizer_or_parent_checker_imported=False,audit_sha256=digest(Path(__file__).resolve()))
    text=json.dumps(report,indent=2,sort_keys=True)+'\n';need(not args.output.exists() or args.output.read_text()==text,'no changed receipt overwrite');args.output.write_text(text)
    print(json.dumps(dict(status='PASS',profiles=24,delta_classes=3),sort_keys=True))
if __name__=='__main__':main()
