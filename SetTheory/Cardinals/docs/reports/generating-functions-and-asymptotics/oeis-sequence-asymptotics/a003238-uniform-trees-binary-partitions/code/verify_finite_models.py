"""Supplemental exact finite model/offset checks; no missing b-files required.
OEIS first-line numeric fixtures inspected 2026-10-04 at the cited entry URLs.
This is not an input to the directed nonconvergence certificate.
"""
from pathlib import Path
from itertools import accumulate
import json
from verify_exact import recurrence,sieve,divisible_partitions
ROOT=Path(__file__).resolve().parent
fixtures={
'A003238':(1,'1,1,2,3,5,6,10,11,16,19,26,27,40,41,53,61,77,78,104,105,134,147,175,176,227,233,275,294,350,351,438,439,516,545,624,640,774,775,881,924,1069,1070,1265,1266,1444,1521,1698,1699'),
'A003318':(1,'1,2,4,7,12,18,28,39,55,74,100,127,167,208,261,322,399,477,581,686,820,967,1142,1318,1545,1778,2053,2347,2697,3048,3486,3925,4441,4986,5610,6250,7024,7799,8680,9604,10673,11743,13008,14274,15718,17239,18937,20636'),
'A018819':(0,'1,1,2,2,4,4,6,6,10,10,14,14,20,20,26,26,36,36,46,46,60,60,74,74,94,94,114,114,140,140,166,166,202,202,238,238,284,284,330,330,390,390,450,450,524,524,598,598,692,692,786,786,900,900,1014,1014,1154,1154,1294,1294'),
'A000123':(0,'1,2,4,6,10,14,20,26,36,46,60,74,94,114,140,166,202,238,284,330,390,450,524,598,692,786,900,1014,1154,1294,1460,1626,1828,2030,2268,2506,2790,3074,3404,3734,4124,4514,4964,5414,5938,6462,7060,7658,8350,9042,9828')}
N=10000;a=recurrence(N);aa=sieve(N)
if a!=aa:raise RuntimeError('divisor and sieve recurrences disagree')
S=list(accumulate(a));b=[1]+[0]*N
for n in range(1,N+1):b[n]=b[n-1]+(b[n//2] if n%2==0 else 0)
B=list(accumulate(b));models={'A003238':a,'A003318':S,'A018819':b,'A000123':B};counts={}
for seq,(offset,csv) in fixtures.items():
 f=list(map(int,csv.split(',')));counts[seq]=len(f)
 if models[seq][offset:offset+len(f)]!=f:raise RuntimeError(('OEIS fixture',seq))
for n in range(2,31):
 got=sum(divisible_partitions(n-1-k,k) for k in range(1,n))
 if got!=a[n]:raise RuntimeError(('chain partitions',n))
for n in range(1,1000):
 if S[n+1]!=1+sum(S[n//k] for k in range(1,n+1)):raise RuntimeError(('floor recurrence',n))
for n in range(N//2+1):
 if B[n]!=b[2*n]:raise RuntimeError(('binary cumulative identity',n))
for n in range(2,N):
 if a[n+1]<a[n]+1:raise RuntimeError(('strict increase',n))
res={'status':'PASS','source_check_date':'2026-10-04','source_urls':{x:'https://oeis.org/'+x for x in fixtures},'OEIS_first_line_cases':counts,'divisor_vs_sieve_prefix':N,'direct_chain_partition_cases':29,'summatory_floor_recurrence_cases':999,'binary_cumulative_identity_cases':N//2+1,'strict_increase_cases':N-2,'scope':'Supplemental exact finite checks only; no full b-file comparison is claimed.'}
(ROOT/'FINITE_MODEL_CHECKS.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
