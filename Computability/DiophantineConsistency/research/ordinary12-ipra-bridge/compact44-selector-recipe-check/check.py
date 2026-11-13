#!/usr/bin/env python3
"""Check retained compact44 selector/copy recipe values against the table."""
import argparse
import ast
import hashlib
import gzip
import importlib.util
import json
import os
import sys
from pathlib import Path
if not __debug__ or os.environ.get('PYTHONOPTIMIZE'):
    raise RuntimeError('optimized Python rejected')
HERE=Path(__file__).resolve().parent;BASE=HERE.parent;ROOT=HERE.parents[2]
RECIPE=ROOT/'candidates/free-j-polarized-positive/source/positive/coefficients/recipe'
BUILDER=RECIPE/'build_coefficients.py';TRANSITIONS=RECIPE/'k215_transitions.json';BINDING=RECIPE/'COEFFICIENT_BINDING.json'
JSON=ROOT/'con-zfc-diophantine-forms/36-small-tuple/coefficients/wang943_tiles.json'
TILE=BASE/'compact44-tile-payload-prototype/CompactTilePayload.lean'
MCFILE=ROOT/'candidates/ten-positive-shifted-strong/coefficients/MC.bin.gz'
KFILE=ROOT/'candidates/ten-positive-shifted-strong/coefficients/K.bin.gz'
BETAFILE=ROOT/'candidates/ten-positive-shifted-strong/coefficients/beta.bin.gz'
MFFILE=ROOT/'candidates/ten-positive-shifted-strong/coefficients/MF_source.bin.gz'
PINS={BUILDER:'a003f26c5ef2dc1782e37be2a91abe25e59e5ff39f12bd142f2d6c1d4d8cf82b',
 TRANSITIONS:'880741dcb49494aab7c1f7d7e453764d573f9704882502b5849f1e3a84b81755',
 BINDING:'0599543212b8d2bbed2db018a29d6826702e1877faa5c8a1861d041998cb1783',
 JSON:'66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f',
 TILE:'05f1cc02e25fe2d44a5b2fd65859c03677b86e0ddcfa0d4c807d413986fb5410',
 MCFILE:'271fabccdd555bda2c54c4c3a7379cc02eeba4893c07178bfd557a7683b74d5e',
 KFILE:'b70752bb38570b1e93d480469c63ace9ed4b4552f94eb89d96bc600b1e2a4b6a',
 BETAFILE:'466796f146d60db9929fa0f0f62d70d5e6afbcea9940342764571f1ca6bea87c',
 MFFILE:'935cd87f8b23f24a20fd742c48d2a9cbca6afd494b6b074445df72c98b0c6e3b'}
H=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def verify_coefficients(rows,slots,coefficients):
    for i,(w,n,e,s) in enumerate(rows):
        value=w+2**8*n+2**17*e+2**25*s+127*2**34
        if not 0<value<2**41 or coefficients[i]!=1+2**10*(2**41-value):raise ValueError(('selector coefficient mismatch',i))
    for j,pos in enumerate(slots):
        if coefficients[pos]!=2**(10+j):raise ValueError(('copy coefficient mismatch',j,pos))

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--negative-controls',action='store_true');args=ap.parse_args()
    for path,digest in PINS.items():
        if H(path)!=digest:raise ValueError(('input drift',str(path)))
    rows=json.loads(JSON.read_text());binding=json.loads(BINDING.read_text())
    if not isinstance(rows,list) or len(rows)!=943 or any(not isinstance(r,list) or len(r)!=4 or any(type(x) is not int or x<0 for x in r) for r in rows):raise ValueError('bad ordered tile data')
    if rows[0]!=[2,435,3,1] or rows[1]!=[5,0,0,0]:raise ValueError('unexpected start or forbidden row')
    if binding.get('transition_json_sha256')!=PINS[TRANSITIONS]:raise ValueError('transition binding mismatch')
    expected='def value (w n e s : V) : V := w+256*n+131072*e+33554432*s+127*17179869184'
    if TILE.read_text().splitlines().count(expected)!=1:raise ValueError('tile-value source shape mismatch')
    constants={}
    for node in ast.parse(BUILDER.read_text()).body:
        if isinstance(node,ast.Assign):
            for target in node.targets:
                if isinstance(target,ast.Name) and target.id in ('OFFSETS','WIDTHS','ANCHORS'):
                    if target.id in constants:raise ValueError(('duplicate constant',target.id))
                    constants[target.id]=ast.literal_eval(node.value)
    if set(constants)!={'OFFSETS','WIDTHS','ANCHORS'}:raise ValueError('missing recipe constants')
    offsets,widths,anchors=(constants[k] for k in ('OFFSETS','WIDTHS','ANCHORS'))
    if list(widths)!=binding['port_widths'] or list(anchors)!=binding['anchors'] or len(binding['binary_positions'])!=4:raise ValueError('binding shape mismatch')
    slots=[None]*41
    for field,positions in enumerate(binding['binary_positions']):
        if len(positions)!=widths[field]:raise ValueError(('field width mismatch',field))
        for j,k in enumerate(positions):
            if type(k) is not int or not 0<=k<41 or slots[k] is not None:raise ValueError(('payload index',k))
            slots[k]=offsets[field]+j
    if len(binding['anchor_positions'])!=len(anchors):raise ValueError('anchor shape mismatch')
    for k,pos in zip(binding['anchor_positions'],anchors):
        if type(k) is not int or not 0<=k<41 or slots[k] is not None:raise ValueError(('anchor bit index',k))
        slots[k]=pos
    if len(set(slots))!=41 or not all(type(x) is int and 0<=x<binding['L'] for x in slots):raise ValueError('bad slot list')
    sys.dont_write_bytecode=True
    spec=importlib.util.spec_from_file_location('retained_compact44_recipe',BUILDER);module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
    data=module.recipe()
    if data['source_hash']!=PINS[TRANSITIONS] or [list(t) for t in data['tiles']]!=rows:raise ValueError('builder ordered tiles mismatch')
    verify_coefficients(rows,slots,data['ce'])
    if set(slots)&{1063,1064}:raise ValueError('copy slots include a dummy')
    if len(data['E'])!=986 or not {1,1063,1064}.issubset(data['E']):raise ValueError('bad support or missing special low-mask positions')
    if data['ce'][1063]!=0 or data['ce'][1064]!=0:raise ValueError('dummy has nonzero local coefficient')
    rho=1<<67;B=1<<590069
    MC=B-1-sum(1<<(67*e) for e in data['E'] if e!=1)-(2<<(67*1063))
    raw=gzip.decompress(MCFILE.read_bytes())
    if len(raw)!=73759 or hashlib.sha256(raw).hexdigest()!='6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4' or int.from_bytes(raw,'little')!=MC:
        raise ValueError('retained MC does not match recipe')
    DC=sum(c<<(67*e) for e,c in data['dc'].items())
    K=DC+B*(1<<(67*42));kraw=gzip.decompress(KFILE.read_bytes())
    if len(kraw)!=74111 or hashlib.sha256(kraw).hexdigest()!='c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e' or int.from_bytes(kraw,'little')!=K:
        raise ValueError('retained K does not match recipe')
    beta=B-1
    MF_native=4+sum(data['mu']<<(67*t) for t in (4393,5495))
    MF_native+=sum(1<<(67*t) for t,*_ in data['targets'])
    MF_native+=sum(c<<(67*e) for e,c in data['padding'].items())
    MF_source=MF_native+beta
    beta_raw=gzip.decompress(BETAFILE.read_bytes());mf_raw=gzip.decompress(MFFILE.read_bytes())
    if len(beta_raw)!=73759 or hashlib.sha256(beta_raw).hexdigest()!='0664a868cbfef9869ea05c40a1c445563f685ff857092594c1c1223bc4b21f9d' or int.from_bytes(beta_raw,'little')!=beta:
        raise ValueError('retained beta does not match recipe')
    if len(mf_raw)!=73759 or hashlib.sha256(mf_raw).hexdigest()!='48333b0d30a4edeb8579f44286cb59806c5622cb42b367f5b5f9ee827711c737' or int.from_bytes(mf_raw,'little')!=MF_source:
        raise ValueError('retained shifted MF does not match recipe')
    if not 0<MC<beta<MF_source<2*beta or MC.bit_count()!=590069-986 or MF_native.bit_count()!=986:
        raise ValueError('tuple bounds or mask population mismatch')
    high={0:4}
    for t in (4393,5495):high[t]=high.get(t,0)+data['mu']
    for t,*_ in data['targets']:high[t]=high.get(t,0)+1
    for e,c in data['padding'].items():high[e]=high.get(e,0)+c
    if any(not 0<=value<rho for value in high.values()):raise ValueError('high-mask coefficient exceeds radix')
    for pos in range(binding['L']):
        if ((MF_native>>(67*pos))&(rho-1))!=high.get(pos,0):raise ValueError(('full MF native digit mismatch',pos))
    if high.get(0)!=4 or high.get(4393)!=data['mu'] or high.get(5495)!=data['mu']:
        raise ValueError('unexpected high-mask target/origin digit')
    digit=lambda j:(MC>>(67*j))&(rho-1)
    if digit(1)!=rho-1 or digit(1063)!=rho-4 or digit(1064)!=rho-2:
        raise ValueError('special low-mask digit mismatch')
    if any(digit(i)!=rho-2 for i in range(943) if i!=1):raise ValueError('ordinary selector mask digit mismatch')
    if any(digit(pos)!=rho-2 for pos in slots):raise ValueError('copy slot mask digit mismatch')
    for pos in range(binding['L']):
        expected=rho-1-int(pos in data['E'] and pos!=1)-(2 if pos==1063 else 0)
        if digit(pos)!=expected:raise ValueError(('full MC digit mismatch',pos))
    support=lambda t:{(t-e)%binding['L'] for e in data['E']}
    if support(4393)&support(5495) or support(2195)&support(3296)!={0}:
        raise ValueError('unexpected support intersections')
    if support(4392)&support(5494) or support(4392)&support(5495) or support(4393)&support(5494)!={2198}:
        raise ValueError('unexpected target/predecessor intersections')
    if (4393-2198)%binding['L']!=2195 or (5494-2198)%binding['L']!=3296:
        raise ValueError('unexpected exceptional anchor sources')
    choices=[0,0]
    for phase in range(binding['L']):
        possible=[i for i,t in enumerate((4393,5495))
            if (t-phase)%binding['L'] not in data['E'] and (t-1-phase)%binding['L']!=1063]
        if not possible:raise ValueError(('no clean target and safe predecessor',phase))
        choices[possible[0]]+=1
    mass=sum(data['ce'].values());M=(len(data['E'])+2)*(2*mass+6)
    if rho!=147573952589676412928 or M!=29613572795083482608 or not 4*M+8<rho or not 12*M+8>rho:
        raise ValueError('unexpected carry-slack calculation')
    mu=(1<<51)-2;local=(1<<51)-(1<<10);temporal=1<<10;combined=local+temporal
    if combined!=(1<<51) or combined&mu or not (local&mu):raise ValueError('unexpected clean-temporal counterexample')
    if args.negative_controls:
        for name,key in (('selector',0),('copy',slots[0])):
            changed=dict(data['ce']);changed[key]+=1
            try:verify_coefficients(rows,slots,changed)
            except ValueError as exc:
                if name not in str(exc):raise
                print('PASS_REJECTED_MUTATED_'+name.upper())
            else:raise ValueError(('negative control accepted',name))
    for path,digest in PINS.items():
        if H(path)!=digest:raise ValueError(('input changed during check',str(path)))
    print('PASS_COMPACT44_SELECTOR_RECIPE',len(rows),len(slots),PINS[JSON],PINS[BUILDER],PINS[TILE])
    print('PASS_RETAINED_BETA_AND_SHIFTED_MF_RECIPE_MATCH','once_shifted',True,'population_balance',MC.bit_count()+MF_native.bit_count())
    print('PASS_RETAINED_K_RECIPE_MATCH','raw_sha256','c6d523bd32af8dd0345db843cdadf6932bfcad186912a6d112314b60657c554e')
    print('PASS_RETAINED_MC_RECIPE_MATCH','raw_sha256','6007cabd5f5228618e8fb613f386d8fc3692a24520d6e4cd72af0262aae1ade4')
    print('PASS_ALL_8807_MF_NATIVE_DIGITS','origin=4','both_clause_digits=mu')
    print('PASS_ALL_8807_MC_DIGITS','forbidden=1:rho-1','dummy1063:rho-4','dummy1064:rho-2','copy_slots_exclude_dummies')
    print('PASS_SUPPORT_INTERSECTIONS','clause=empty','anchor=[0]','predecessor_exception=[2198]')
    print('PASS_FINITE_CLEAN_TARGET_SELECTION','phases',binding['L'],'chosen_first',choices[0],'chosen_second',choices[1])
    print('PASS_CLEAN_TEMPORAL_COUNTEREXAMPLE','output_disjoint','local_not_disjoint')
    print('PASS_CARRY_SLACK_COMPARISON','rho',rho,'M',M,'4M+8',4*M+8,'12M+8',12*M+8)
if __name__=='__main__':main()
