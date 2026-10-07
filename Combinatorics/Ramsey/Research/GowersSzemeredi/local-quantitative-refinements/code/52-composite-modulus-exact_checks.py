#!/usr/bin/env python3
"""Bounded exact diagnostics for Report280.

This read-only standard-library program does not construct the astronomical
witnesses or evaluate the displayed exponent towers. It checks finite models,
small exponent arithmetic, symbolic identities, and curated source bytes.
It is not a Lean proof or a proof of the arbitrary-parameter theorems.
"""
from __future__ import annotations
import sys
sys.dont_write_bytecode = True
import argparse
from collections import Counter
import hashlib
import importlib.util
import json
from math import gcd
from pathlib import Path
import re

ROOT = Path(__file__).absolute().parents[1]
MAX_MODULUS = 1024
MAX_POINTS = 32
MAX_ORDER = 9
MAX_JOINT_STATES = 65536
MAX_SOURCE_SNAPSHOT_BYTES = 1024 * 1024


def require(condition, message):
    if not condition:
        raise RuntimeError(message)


def bounded(value, name, minimum, maximum):
    if type(value) is not int or not minimum <= value <= maximum:
        raise ValueError(f'{name} must be an integer in [{minimum}, {maximum}]')
    return value


def pow2_small(exponent):
    bounded(exponent, 'small exponent', 0, 30)
    return 1 << exponent


def symbolic_constants():
    return dict(alpha='2^(-4)',delta='2^(-939)',lambda_='2^(-1072)',
        epsilon='2^(-1892)',K13='2^1394',Q13='2^9437184',
        c='2^(-2532*2^1394-1)',beta='2^(-13*2^9437184)',
        base_k='939*2^1892+5',unit_k='940*2^1892+4',
        theta='2^(-130)',theta1='2^(-1363892)',K0='2^128',q='2^130+2',
        U='16*(2^130+2)*2^(2*1363892)',genuine_k='(1363892+10)*U')


def exponent_diagnostics():
    delta = 43+4*224; lam = 48+4*256; eps = 100+4*448
    t = 1882+130*10477
    facts = dict(delta=delta,lambda_=lam,epsilon=eps,K13_log2=114+4*320,
        Q13_log2=pow2_small(20)+4*pow2_small(21),zeta_multiplier=228+4*576,
        t=t,Q134_log2=1882+130*10479,genuine_k_lower_power=2*t+4,
        base_gap_coefficient=pow2_small(11)-939,unit_gap_coefficient=pow2_small(11)-940)
    require(facts == dict(delta=939,lambda_=1072,epsilon=1892,K13_log2=1394,
        Q13_log2=9437184,zeta_multiplier=2532,t=1363892,Q134_log2=1364152,
        genuine_k_lower_power=2727788,base_gap_coefficient=1109,unit_gap_coefficient=1108),
        'exponent identities')
    # Symbolic coefficient identities, without constructing 2^128 or larger.
    require(1+1+128 == 130, 'q=2(2*2^128+1)=2^130+2')
    require(130+1 == 131 and 131 <= t+260, 'q <= 2^131 <= Q134')
    require(2+128 == 130 and 130-1 == 129, 'theta/alias cutoffs')
    require(pow2_small(10) == 64*16, 'exact floor prefactor')
    require(5*11 < 56 and 16 < 6*3, 'rational brackets for floor 16/pi')
    require(2*t+4 >= 1903 and 1903-1892 == 11, 'large k comparison')
    require(facts['base_gap_coefficient'] > 4 and facts['unit_gap_coefficient'] > 3,
            'strict large k gaps')
    require(132-129 == 3 and pow2_small(3) > 5, 'N/5 > 2^129')
    require(5 <= pow2_small(4) and 11 >= 2, '5^(-2^(-11q)) >= 1/2 for q>=1')
    require(delta-1 > 0 and lam-1 > 0, 'unit-step mass factors 2delta,2lambda <1')
    # k-4 = 939*2^1892+1; k-3 = 940*2^1892+1.
    require(5-4 == 1 and 4-3 == 1, 'positive exact threshold remainder')
    return dict(integer_identities=facts,symbolic_constants=symbolic_constants(),
        floor_bracket='5 < 56/11 < 16/pi < 16/3 < 6 using 3<pi<22/7',
        huge_witness_evaluated=False)



def budget_diagnostics():
    cutoff = 37+132*11//2
    t = 1882+cutoff*10477
    facts = dict(cutoff=cutoff,t=t,K0_log2=cutoff-2,q_upper_log2=cutoff+1,
        Q134_log2=1882+cutoff*10479,spectrum_log2=74+132*10,
        zeta_multiplier=155+132*18,width_log2=135+4*704,
        sigma_small_term=2*t+769)
    require(facts == dict(cutoff=763,t=7995833,K0_log2=761,q_upper_log2=764,
        Q134_log2=7997359,spectrum_log2=1394,zeta_multiplier=2531,
        width_log2=2951,sigma_small_term=15992435),'full-budget exponent identities')
    require(132*11%2 == 0,'exact half power exponent')
    require(facts['sigma_small_term'] < pow2_small(24),'small exponent margin')
    require(12 < pow2_small(4) and 764+4 == 768,'12q < 2^768')
    require(24 < 768 and 768+1 == 769 and 769 < 9437184,
            'symbolic beta < sigma comparison')
    require(12 > 11 and 2 > 1,'v < w and sigma=uv/2 < uw')
    # Floor bounds are checked exhaustively for bounded rational inputs x>=2.
    floor_cases = 0
    for denominator in range(1,33):
        for numerator in range(2*denominator,513):
            floor = numerator//denominator
            require(floor*denominator <= numerator < (floor+1)*denominator,'floor bracket')
            require(numerator <= 2*denominator*floor,'floor x >= x/2 for x>=2')
            floor_cases += 1
    return dict(integer_identities=facts,rational_floor_cases=floor_cases,
        symbolic_margins=['beta<sigma','sigma<u','2sigma<1','sigma<uw<1'],
        caveat='The nine positive-power thresholds and all six budgets are proved in the article, not by numerical evaluation')


def validate_graph(modulus, points, values):
    bounded(modulus,'modulus',2,MAX_MODULUS)
    if type(points) is not tuple or type(values) is not tuple or len(points) != len(values):
        raise ValueError('equal-length tuples of points and values required')
    bounded(len(points),'point count',1,MAX_POINTS)
    for x in (*points,*values):
        bounded(x,'residue',0,modulus-1)
    if len(set(points)) != len(points):
        raise ValueError('distinct domain points required')


def joint_sum_counts(modulus, points, values, order):
    """Ordered tuple convolution; keys are (domain sum,image sum)."""
    validate_graph(modulus,points,values)
    bounded(order,'Freiman order',1,MAX_ORDER)
    counts = {(0,0):1}
    for _ in range(order):
        nxt = Counter()
        for (x,y),count in counts.items():
            for point,value in zip(points,values):
                nxt[((x+point)%modulus,(y+value)%modulus)] += count
        if len(nxt) > MAX_JOINT_STATES:
            raise ValueError('joint-state cap exceeded')
        counts = dict(nxt)
    return counts


def freiman_diagnostic(modulus, points, values, order):
    joint = joint_sum_counts(modulus,points,values,order)
    domain = Counter(); image_sets = {}
    for (x,y),count in joint.items():
        domain[x] += count
        image_sets.setdefault(x,set()).add(y)
    total = sum(domain.values())
    require(total == len(points)**order,'ordered tuple total')
    energy = sum(count*count for count in domain.values())
    require(modulus*energy >= total*total,'Cauchy-Schwarz energy bound')
    return dict(freiman=all(len(values)==1 for values in image_sets.values()),
        tuple_count=total,domain_counts=tuple(domain.get(i,0) for i in range(modulus)),
        additive_energy=energy,fixed_height_arrangements=modulus**16*energy)


def max_affine_agreement(modulus, points, values):
    """For each slope, count its forced intercepts; never sample affine maps."""
    validate_graph(modulus,points,values)
    best = 0
    for a in range(modulus):
        counts = Counter((f-a*x)%modulus for x,f in zip(points,values))
        best = max(best,max(counts.values()))
    return best


def prime_power_model(prime, exponent, width):
    bounded(prime,'toy prime',2,7)
    if any(prime%d == 0 for d in range(2,prime)):
        raise ValueError('prime required')
    bounded(exponent,'toy exponent',2,10)
    modulus = prime**exponent
    bounded(modulus,'toy prime-power modulus',2,MAX_MODULUS)
    bounded(width,'strip width',1,MAX_POINTS//prime)
    if 8*(width-1) >= modulus//prime or prime*width >= modulus:
        raise ValueError('strict order-eight no-wrap and proper carrier required')
    points = tuple(prime*j for j in range(width)); values = tuple(range(width))
    freiman = freiman_diagnostic(modulus,points,values,8)
    require(freiman['freiman'],'prime-power strip Freiman property')
    require(all(gcd(prime*a-1,modulus)==1 for a in range(modulus)),'unit multiplier')
    restricted = max_affine_agreement(modulus,points,values)
    all_points = tuple(range(prime*width)); all_values = tuple(x//prime for x in all_points)
    enlarged = max_affine_agreement(modulus,all_points,all_values)
    require(restricted == 1,'one agreement on the strip')
    require(enlarged == prime,'p agreements on the enlarged unit interval')
    return dict(prime=prime,exponent=exponent,modulus=modulus,width=width,
        order_eight=True,strip_max_agreement=restricted,unit_interval_max_agreement=enlarged,
        tuple_count=freiman['tuple_count'],energy=freiman['additive_energy'],
        fixed_height_arrangements=freiman['fixed_height_arrangements'])


def alias_set(modulus, radius):
    bounded(modulus,'alias modulus',4,MAX_MODULUS)
    if modulus%2:
        raise ValueError('even alias modulus required')
    bounded(radius,'alias radius',0,16)
    if 4*radius >= modulus:
        raise ValueError('separated aliases required')
    aliases = {(nu*(modulus//2)+s)%modulus for nu in (0,1) for s in range(-radius,radius+1)}
    small_doubles = {r for r in range(modulus) if min((2*r)%modulus,(-2*r)%modulus)<=2*radius}
    require(aliases == small_doubles,'exact spectral alias identity')
    require(len(aliases) == 2*(2*radius+1),'alias cardinality')
    return tuple(sorted(aliases))


def congruence_solutions(modulus, difference, image_difference):
    bounded(modulus,'congruence modulus',2,64)
    bounded(difference,'difference',0,modulus-1)
    bounded(image_difference,'image difference',0,modulus-1)
    values = tuple(a for a in range(modulus) if (difference*a-image_difference)%modulus == 0)
    require(bool(values) == (image_difference%gcd(difference,modulus)==0),'gcd solvability')
    return values


def small_model_diagnostics():
    models = [prime_power_model(*row) for row in
        ((2,5,2),(2,6,4),(2,7,8),(2,8,16),(3,4,3),(5,3,3),(7,3,3))]
    z18_8 = freiman_diagnostic(18,(0,2),(0,1),8)
    z18_9 = freiman_diagnostic(18,(0,2),(0,1),9)
    require(z18_8['freiman'] and not z18_9['freiman'],'Z18 sharp Freiman order')
    require(max_affine_agreement(18,(0,2),(0,1)) == 1,'Z18 nonextension')
    aliases = sum(1 for n in (32,64,128,256) for radius in (0,1,2,4)
                  if alias_set(n,radius))
    congruences = 0
    for modulus in range(2,25):
        for d in range(modulus):
            for e in range(modulus):
                congruence_solutions(modulus,d,e); congruences += 1
    return dict(prime_power_models=models,alias_models=aliases,
        congruence_models=congruences,Z18_order8=True,Z18_order9=False,
        scope='Small finite models only; no Stage137 large modulus is enumerated')


def verify_source_bytes(raw, row):
    if type(raw) is not bytes or len(raw) > MAX_SOURCE_SNAPSHOT_BYTES:
        raise ValueError('bounded source bytes required')
    keys = {'file','repository_path','commit','bytes','sha256','git_blob','verified_url'}
    if type(row) is not dict or set(row) != keys:
        raise ValueError('exact curated source record required')
    if type(row['file']) is not str or not re.fullmatch(r'sources/[A-Za-z0-9_]+\.lean',row['file']):
        raise ValueError('ordinary selected Lean snapshot name required')
    expected_path = 'Combinatorics/Ramsey/Lean/GowersSzemeredi/'+row['file'].split('/')[-1]
    if row['repository_path'] != expected_path:
        raise ValueError('repository path does not match the selected snapshot')
    for key,width in (('commit',40),('git_blob',40),('sha256',64)):
        if type(row[key]) is not str or not re.fullmatch('[0-9a-f]{'+str(width)+'}',row[key]):
            raise ValueError('invalid '+key)
    expected_url = 'https://github.com/VladimirReshetnikov/ProveIt/blob/'+row['commit']+'/'+expected_path
    if row['verified_url'] != expected_url:
        raise ValueError('pinned verified URL does not match repository path and commit')
    bounded(row['bytes'], 'source size', 1, MAX_SOURCE_SNAPSHOT_BYTES)
    git_blob = hashlib.sha1(b'blob '+str(len(raw)).encode('ascii')+b'\0'+raw).hexdigest()
    require(len(raw) == row['bytes'], 'source byte length differs')
    require(git_blob == row['git_blob'], 'Git blob mismatch')
    require(hashlib.sha256(raw).hexdigest() == row['sha256'], 'SHA256 mismatch')
    return git_blob


def validate_source_manifest(manifest, files):
    if type(manifest) is not dict or set(manifest) != {'schema','scope','sources','unchanged_at_later_pins'}:
        raise ValueError('exact curated manifest schema required')
    if manifest['schema'] != 'report280-curated-sources-v1' or type(manifest['scope']) is not str:
        raise ValueError('unsupported curated manifest schema')
    rows = manifest['sources']; later = manifest['unchanged_at_later_pins']
    if type(rows) is not list or not 1 <= len(rows) <= 64 or type(later) is not list or len(later) > 64:
        raise ValueError('bounded curated source record lists required')
    names = set()
    for row in rows:
        if type(row) is not dict or type(row.get('file')) is not str:
            raise ValueError('curated source row required')
        name = 'provenance/'+row['file']
        require(name in files, 'curated snapshot missing')
        verify_source_bytes(files[name],row)
        require(name not in names, 'duplicate curated snapshot row')
        names.add(name)
    require(names == {name for name in files if name.startswith('provenance/sources/')},
            'curated source manifest/file inventory differs')
    later_keys = set()
    for row in later:
        if type(row) is not dict or type(row.get('file')) is not str:
            raise ValueError('curated later-pin row required')
        name = 'provenance/'+row['file']
        require(name in names, 'later-pin row lacks a selected snapshot')
        verify_source_bytes(files[name],row)
        key = (row['file'],row['commit'])
        require(key not in later_keys, 'duplicate later-pin row')
        later_keys.add(key)
    return len(rows),len(later)


def source_diagnostics():
    spec = importlib.util.spec_from_file_location('report280_build', ROOT/'build.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    files = module.verified_snapshot()
    manifest = json.loads(files['provenance/source_manifest.json'])
    count,later = validate_source_manifest(manifest,files)
    return dict(verified_lean_snapshots=count, unchanged_later_pin_checks=later,
        provenance_files=sum(name.startswith('provenance/') for name in files),
        pins=sorted({row['commit'] for row in manifest['sources']+manifest['unchanged_at_later_pins']}),
        scope='Curated source byte identity, SHA256, Git blob and pinned URL checks only; no Lean compilation or axiom audit')


def diagnostics():
    return dict(status='passed',report=280,exponents=exponent_diagnostics(),
        models=small_model_diagnostics(),budgets=budget_diagnostics(),sources=source_diagnostics(),
        caps=dict(modulus=MAX_MODULUS,points=MAX_POINTS,order=MAX_ORDER,
                  joint_states=MAX_JOINT_STATES,evaluated_power_of_two_exponent=30),
        excluded=['No astronomical witness constructed','No floating-point Fourier proof',
                  'No Lean proof, compilation or project audit'])


def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.parse_args(argv)
    print(json.dumps(diagnostics(),indent=2,sort_keys=True))
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
