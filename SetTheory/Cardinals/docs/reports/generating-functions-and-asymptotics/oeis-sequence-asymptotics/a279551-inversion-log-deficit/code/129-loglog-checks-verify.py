#!/usr/bin/env python3
"""Independent exact finite companion for Report 129; standard library only."""
import argparse
import hashlib
import itertools
import json
import math
import os
from pathlib import Path
import re
import stat
import sys
from fractions import Fraction as F

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
MEMBERS = ('README.md', 'evidence.json', 'manifest.sha256', 'negative_tests.py', 'provenance.json', 'verify.py')
CHECKS = ('legal_transforms', 'joint_moments_and_root', 'anchor_cancellation', 'corrected_action', 'dual_gap', 'rate_ledger', 'cap_four', 'genuine_time', 'exact_repair', 'inverse_and_moment')
REPORT = 'Report 129: The next logarithmic correction for two inversion sequence classes'
PRIOR_REPORT = 'Report 127: Sharp logarithmic deficit constants for two inversion sequence classes'

class Reject(Exception):
    pass

def need(condition, code):
    if not condition:
        raise Reject(code)

def keys(obj, expected, code):
    need(type(obj) is dict and set(obj) == set(expected), code)

def integer(value, code):
    need(type(value) is int, code)
    return value

def rat(value):
    need(type(value) is str and re.fullmatch(r'-?(0|[1-9][0-9]*)(/[1-9][0-9]*)?', value) is not None, 'schema:rational')
    q = F(value)
    need(str(q) == value, 'schema:rational')
    return q

def unique(pairs):
    obj = {}
    for key, value in pairs:
        need(key not in obj, 'schema:duplicate-key')
        obj[key] = value
    return obj

def parse(path):
    return json.loads(path.read_text(), object_pairs_hook=unique,
                      parse_constant=lambda value: (_ for _ in ()).throw(Reject('schema:nonfinite')))

def digest(data):
    return hashlib.sha256(data).hexdigest()

def encoded(value):
    return (json.dumps(value, indent=2, sort_keys=True) + '\n').encode()

def seal_check():
    entries = list(HERE.iterdir())
    need(sorted(x.name for x in entries) == list(MEMBERS), 'inventory:members')
    need(all(stat.S_ISREG(x.lstat().st_mode) for x in entries), 'inventory:regular')
    lines = (HERE/'manifest.sha256').read_text().splitlines()
    expected = [name for name in MEMBERS if name != 'manifest.sha256']
    need(len(lines) == len(expected), 'manifest:count')
    for line, name in zip(lines, expected):
        need(re.fullmatch(r'[0-9a-f]{64}  ' + re.escape(name), line) is not None, 'manifest:format')
        need(line[:64] == digest((HERE/name).read_bytes()), 'manifest:digest')

def load():
    seal_check()
    e = parse(HERE/'evidence.json')
    keys(e, ('schema', 'scope', 'checks', 'models', 'coverage', 'constants', 'rates'), 'schema:top')
    need(type(e['schema']) is int and e['schema'] == 1, 'schema:version')
    need(e['scope'] == 'finite_exact_regression_only', 'schema:scope')
    need(type(e['checks']) is list and e['checks'] == list(CHECKS), 'schema:checks')
    keys(e['models'], ('759', '247'), 'schema:models')
    for row in e['models'].values():
        keys(row, ('mu', 'x', 'a', 'A0', 'alpha', 'D', 'r'), 'schema:model')
        for v in row.values():
            rat(v)
    keys(e['coverage'], ('p_max', 'b_max', 'n_max', 'brute_max', 'root_steps', 'log_terms', 'levels', 'tilts', 'repair_offsets', 'fill_offsets'), 'schema:coverage')
    cov = e['coverage']
    fixed = {'p_max': 10, 'b_max': 8, 'n_max': 16, 'brute_max': 7, 'root_steps': 48, 'log_terms': 60}
    for key, value in fixed.items():
        need(integer(cov[key], 'schema:integer') == value, 'coverage:'+key)
    need(cov['levels'] == [256, 257, 258, 512, 1024, 10000, 1000000] and all(type(v) is int for v in cov['levels']), 'coverage:levels')
    need(cov['tilts'] == ['4/5', '1', '6/5'], 'coverage:tilts')
    need(cov['repair_offsets'] == ['0', '1/2', '1'], 'coverage:repair-offsets')
    need(cov['fill_offsets'] == [0, 1, 2, 17, 100000000000000000000] and all(type(v) is int for v in cov['fill_offsets']), 'coverage:fill-offsets')
    constants = ('potential_base', 'potential_correction', 'action_correction', 'inverse_lead_denominator', 'inverse_loglog', 'moment_log', 'moment_loglog', 'moment_linear', 'moment_second', 'saddle_lead', 'saddle_second', 'cap_numerator', 'strip_fraction', 'threshold_inverse_correction')
    keys(e['constants'], constants, 'schema:constants')
    for v in e['constants'].values():
        rat(v)
    rate_keys = ('H', 'S', 'theta', 'k', 'anchored_root', 'scaled_drift', 'clock_failure', 'reward_failure', 'mesh_failure', 'bad_space', 'bad_time', 'tube_margin', 'endpoint_cost_log', 'endpoint_time_log')
    keys(e['rates'], rate_keys, 'schema:rates')
    for v in e['rates'].values():
        rat(v)
    p = parse(HERE/'provenance.json')
    keys(p, ('schema', 'analytic_report', 'prior_report', 'primary_source', 'implementation', 'runtime_dependencies'), 'schema:provenance')
    need(type(p['schema']) is int and p['schema'] == 1, 'provenance:version')
    need(p['analytic_report'] == REPORT and p['prior_report'] == PRIOR_REPORT, 'provenance:report')
    need(p['primary_source'] == 'https://arxiv.org/html/2512.21943v3', 'provenance:source')
    need(p['implementation'] == 'independent-standard-library-rational-jets' and p['runtime_dependencies'] == [], 'provenance:implementation')
    return e

# A degree-three, two-variable Taylor algebra. Coefficients are divided by factorials.
class Jet:
    degree = 3
    def __init__(self, value=0):
        self.c = {k:F(v) for k,v in value.items() if v and sum(k)<=self.degree} if isinstance(value, dict) else ({(0,0):F(value)} if value else {})
    def __add__(self, other):
        other = J(other); out = dict(self.c)
        for k,v in other.c.items(): out[k] = out.get(k, F(0))+v
        return Jet(out)
    __radd__ = __add__
    def __neg__(self): return Jet({k:-v for k,v in self.c.items()})
    def __sub__(self, other): return self+-J(other)
    def __rsub__(self, other): return J(other)+-self
    def __mul__(self, other):
        other=J(other); out={}
        for (i,j),a in self.c.items():
            for (k,l),b in other.c.items():
                if i+j+k+l<=self.degree:
                    key=(i+k,j+l); out[key]=out.get(key,F(0))+a*b
        return Jet(out)
    __rmul__ = __mul__
    def __pow__(self, power):
        need(type(power) is int and power>=0, 'internal:power')
        result=Jet(1)
        for _ in range(power): result=result*self
        return result
    def inverse(self):
        a=self.c.get((0,0),F(0)); need(a!=0, 'internal:inverse')
        h=self/a-1 if a!=1 else self-1
        return sum(((-h)**i for i in range(self.degree+1)),Jet())/a
    def __truediv__(self, other):
        if isinstance(other, Jet): return self*other.inverse()
        return Jet({k:v/F(other) for k,v in self.c.items()})
    def exp(self):
        need(self.c.get((0,0),0)==0, 'internal:exp-origin')
        return sum((self**i/math.factorial(i) for i in range(self.degree+1)),Jet())
    def log(self):
        need(self.c.get((0,0),0)==1, 'internal:log-origin')
        h=self-1
        return sum(((-1)**(i+1)*h**i/i for i in range(1,self.degree+1)),Jet())
    def sub(self, x, y):
        return sum((v*x**i*y**j for (i,j),v in self.c.items()),Jet())
    def at(self,i,j): return self.c.get((i,j),F(0))
    def __eq__(self,other): return self.c==J(other).c

def J(x): return x if isinstance(x,Jet) else Jet(x)
LX, EY = Jet({(1,0):1}), Jet({(0,1):1})

def choose(n,k): return math.comb(n,k) if 0<=k<=n else 0

def cat(b): return math.comb(2*b,b)//(b+1)

def mult(j,ell,b):
    return cat(b)*(choose(ell,b) if j=='759' else choose(b+1,ell-b))

def transforms(j,X,Y):
    if j=='759':
        A=Y/(9*(1-1/(3*X))) if not isinstance(X,Jet) else Y/(9*(1-X.inverse()/3))
        R=4*Y/(9*(1-1/(3*X))*(1-X*Y/3)) if not isinstance(X,Jet) else 4*Y/(9*(1-X.inverse()/3)*(1-X*Y/3))
    else:
        A=Y*(1+1/(2*X))/8 if not isinstance(X,Jet) else Y*(1+X.inverse()/2)/8
        R=Y*(1+1/(2*X))/(2*(1-X*Y/4)) if not isinstance(X,Jet) else Y*(1+X.inverse()/2)/(2*(1-X*Y/4))
    return A,R

def raw_row(j,p,X,Y):
    mu,x=(9,3) if j=='759' else (8,2)
    q=F(x,mu)*X*Y; row=q
    for ell in range(p):
        for b in range(ell+1):
            m=mult(j,ell,b)
            if not m: continue
            bulk=(q/(1-q))**b
            drop=(X**ell).inverse()/x**ell if isinstance(X,Jet) else (x*X)**(-ell)
            row += F(m,mu)*Y*drop*bulk
    return row

def cdf(j,p,b,X):
    if p<=b: return F(0)
    if j=='759':
        z=1/(3*X); term=(1-z)**(b+1); ans=term
        for k in range(1,p-b):
            term *= F(b+k,k)*z; ans+=term
        return ans
    z=1/(2*X+1); term=(1-z)**(b+1); ans=term
    for k in range(1,min(p-b-1,b+1)+1):
        term *= F(b+2-k,k)*z/(1-z); ans+=term
    return ans

def cdf_row(j,p,X,Y):
    mu,x=(9,3) if j=='759' else (8,2)
    A,R=transforms(j,X,Y)
    return F(x,mu)*X*Y + A*sum((F(cat(b),4**b)*R**b*cdf(j,p,b,X) for b in range(p)), F(0))

def duration_moments(j,p,X,Y):
    mu,x=(9,3) if j=='759' else (8,2)
    q=F(x,mu)*X*Y; out=[q]*6
    for ell in range(p):
        for b in range(ell+1):
            m=mult(j,ell,b)
            if not m: continue
            mass=F(m,mu)*Y*(x*X)**(-ell)*(q/(1-q))**b
            w=F(b)/(1-q); var=F(b)*q/(1-q)**2
            de=w-ell; le=w+1
            vals=[1,de,le,var+de**2,var+de*le,var+le**2]
            out=[a+mass*v for a,v in zip(out,vals)]
    return out

def legal_and_moments(e):
    count=0; roots=[]; jetcount=0
    for j in ('759','247'):
        row={k:rat(v) for k,v in e['models'][j].items()}
        mu,x=(9,3) if j=='759' else (8,2)
        alpha=F(3,2) if j=='759' else F(4,3)
        D=F(1) if j=='759' else F(1,2)
        A,R=transforms(j,F(1),F(1))
        actual={'mu':F(mu),'x':F(x),'a':F(x,mu),'A0':A,'alpha':alpha,'D':D,'r':F(x,mu)+2*A}
        need(row==actual, 'math:model')
        need(1-row['r']==2*A and R==1, 'math:scalar-balance')
        for p in range(e['coverage']['p_max']+1):
            for X in map(F,e['coverage']['tilts']):
                for Y in map(F,e['coverage']['tilts']):
                    direct=raw_row(j,p,X,Y); other=cdf_row(j,p,X,Y)
                    need(direct==other, 'math:legal-row'); count+=1
                    if p<=5:
                        jet=raw_row(j,p,X*LX.exp(),Y*EY.exp())
                        jm=[jet.at(0,0),jet.at(1,0),jet.at(0,1),2*jet.at(2,0),jet.at(1,1),2*jet.at(0,2)]
                        mm=duration_moments(j,p,X,Y)
                        need(jm==mm,'math:joint-moments')
                        mass,ed,el,ed2,edl,el2=mm
                        need(el>0,'math:clock-positive')
                        slope=-ed/el; curvature=-(ed2+2*slope*edl+slope*slope*el2)/el
                        level=jet.sub(LX,slope*LX+curvature*LX**2/2)
                        need(level.at(1,0)==0 and level.at(2,0)==0 and curvature<=0, 'math:implicit-drift')
                        jetcount+=1
        for p in (1,2,4,8):
            X=F(1); lo=F(0); hi=F(5,2) if j=='759' else F(3)
            need(raw_row(j,p,X,lo)<1<raw_row(j,p,X,hi),'math:root-bracket-initial')
            for _ in range(e['coverage']['root_steps']):
                mid=(lo+hi)/2
                if raw_row(j,p,X,mid)<1: lo=mid
                else: hi=mid
            need(raw_row(j,p,X,lo)<1<=raw_row(j,p,X,hi) and hi-lo<=F(3,2**48),'math:root-bracket')
            roots.append({'class':j,'p':p,'exp_eta_lower':str(lo),'exp_eta_upper':str(hi)})
        # Exact row-one roots at p=1, followed by their implicit drift ratio.
        root=F(mu,x+1); mm=duration_moments(j,1,F(1),root)
        need(mm[0]==1 and -mm[1]/mm[2]==-F(x,x+1),'math:small-root')
    return {'row_equalities':count,'joint_jet_and_implicit_equalities':jetcount,'root_brackets':roots}

def anchors(e):
    output={}
    for j in ('759','247'):
        A,R=transforms(j,LX.exp(),EY.exp()); logR=R.log()
        alpha=rat(e['models'][j]['alpha']); D=rat(e['models'][j]['D'])
        need(logR.at(1,0)==0 and logR.at(0,1)==alpha and logR.at(2,0)==alpha*D/2, 'math:root-jet')
        anchored=logR.sub(LX,EY-D*LX**2/2)-logR.sub(Jet(),EY)
        need(all(v==0 for (i,k),v in anchored.c.items() if i+2*k<3), 'math:anchored-cancellation')
        # Exact per-b joint cumulants, including the nonzero clock covariance.
        variance=2*logR.at(2,0); cov=logR.at(1,1); clockvar=2*logR.at(0,2)
        need(variance/alpha==D and cov==clockvar and cov>0,'math:diffusion-clock')
        conditioned=(variance-cov*cov/clockvar)/alpha
        need(conditioned==(F(1,2) if j=='759' else F(1,6)), 'math:conditioned-warning')
        output[j]={'log_R_jet':{str(k):str(v) for k,v in sorted(logR.c.items())},'D':str(D),'conditioned_D':str(conditioned),'anchored_low_weight_terms':0}
    return output

# Sparse Laurent polynomials in formal A, g, x. Negative exponents are permitted.
def padd(a,b):
    out=dict(a)
    for k,v in b.items(): out[k]=out.get(k,F(0))+v
    return {k:v for k,v in out.items() if v}

def pmul(a,b):
    out={}
    for ka,va in a.items():
        for kb,vb in b.items():
            k=tuple(x+y for x,y in zip(ka,kb)); out[k]=out.get(k,F(0))+va*vb
    return {k:v for k,v in out.items() if v}

def algebra(e):
    c={k:rat(v) for k,v in e['constants'].items()}
    base=F(1,2)*F(2,3); corr=F(1,2)*F(1,3)+1
    need(c['potential_base']==base and c['potential_correction']==corr, 'math:potential-correction')
    action=F(2,3)*corr/base
    need(c['action_correction']==action, 'math:action-correction')
    need(c['threshold_inverse_correction']==action, 'math:threshold-inverse')
    # Invert log a(n)=lambda*n-deficit: delta n = deficit(s)/lambda.
    # Substitution perturbation is S(s)^2/s, polynomially below S(s)/log(s).
    need(F(2,3)-1 < F(1,3), 'math:threshold-remainder')
    # Binomial jet of (1 + (7/2) z)^(2/3), not a decimal approximation.
    binomial=[F(1)]
    for k in range(1,4): binomial.append(binomial[-1]*(F(2,3)-(k-1))/k*(corr/base))
    need(binomial[1]==action and binomial[2]==-F(49,36),'math:action-second')
    left={(1,0,-1):F(1),(1,-2,1):F(1),(1,-1,0):F(-2)}
    square=pmul({(0,0,0):F(1),(0,-1,1):F(-1)}, {(0,0,0):F(1),(0,-1,1):F(-1)})
    right=pmul({(1,0,-1):F(1)},square)
    need(padd(left,{k:-v for k,v in right.items()})=={},'math:dual-square')
    # Far-gap sample arithmetic complements, and does not replace, the proof's all-x split.
    gap_samples=[]
    for ratio in (F(1,8),F(1,4),F(1,2),F(1),F(2),F(3),F(8)):
        gap=(1-ratio)**2
        if ratio<=F(1,2) or ratio>=2: need(gap>=F(1,4),'math:dual-far')
        gap_samples.append({'x_over_g':str(ratio),'gap_times_x_over_A':str(gap)})
    # Inverse d(n)=y: n=C*y^3/log(y)^2*(1+b*loglog(y)/log(y)+O(1/log(y))).
    invden=3**2
    inverse_corr=4*F(1,3)-action
    need(c['inverse_lead_denominator']==invden and c['inverse_loglog']==inverse_corr,'math:inverse-correction')
    # Cubed deficit substitution: b-4/3+(3*action)/3 must cancel.
    need(inverse_corr-F(4,3)+action==0,'math:inverse-substitution')
    # Independent saddle log-equation coefficient of loglog(k)/log(k).
    # y/3 contributes d/3, (2/3)log(y) contributes -4/9,
    # log(1+(a log(y)+b+2)/y) contributes a/3.
    need(inverse_corr/3-F(4,9)+action/3==0,'math:saddle-substitution')
    # The constant c = log(3)-3log(sigma) cancels coefficientwise.
    log3=Jet({(1,0):1}); logsigma=Jet({(0,1):1})
    cc=log3-3*logsigma
    need(cc/3+2*log3/3+logsigma-log3==Jet(), 'math:saddle-constant')
    # Saddle has d(n)=3k*(1+O(1/log k)); this affects only the unreported O(k/log k) term.
    saddle_lead=F(3**3,invden)
    need(c['saddle_lead']==saddle_lead and c['saddle_second']==inverse_corr,'math:saddle-correction')
    need(c['moment_log']==3 and c['moment_loglog']==-2 and c['moment_linear']==-3 and c['moment_second']==inverse_corr,'math:moment-correction')
    return {'potential':str(corr),'action':str(action),'coefficient_threshold_relative_correction':str(action),'action_binomial_jet':list(map(str,binomial)), 'dual_gap_samples':gap_samples,'inverse_relative_loglog':str(inverse_corr),'saddle_lead_times_sigma_cubed':str(saddle_lead),'moment_k_loglog_over_log':str(inverse_corr)}

def rates(e):
    H,S=F(2,3),F(1,3); theta=H-1; k=S-1; d=-F(1,12)
    actual={'H':H,'S':S,'theta':theta,'k':k,
      'anchored_root':1-S-F(3,2)*H,
      'scaled_drift':-F(3,4)*H-theta,
      'clock_failure':1+H-2-2*d,
      'reward_failure':1-2*H-2*d,
      'mesh_failure':H-1+F(1,6),
      'bad_space':2*d+H,'bad_time':1+d,'tube_margin':d+F(1,14),
      'endpoint_cost_log':-F(6,2),'endpoint_time_log':-F(6)*F(3,2)}
    need({key:rat(v) for key,v in e['rates'].items()}==actual,'math:rate-ledger')
    need(2*H==1+S and 3*H==2 and H+S==1 and 2*theta==k,'math:scale-powers')
    need(actual['bad_space']>S and actual['bad_time']>H and actual['tube_margin']<0,'math:rate-separation')
    c=e['constants']; cap=rat(c['cap_numerator']); fraction=rat(c['strip_fraction'])
    need(cap==4 and fraction==F(1,2) and cap*fraction==2,'math:cap-four')
    capcases=[]
    for n,ceH in ((1,F(1,3)),(20,F(7,5)),(100,F(16)),(101,F(201,2))):
        m=ceil(F(cap*n,ceH))+1
        need(m*ceH*fraction>2*n,'math:cap-strict')
        capcases.append({'n':n,'ceH':str(ceH),'cap':m,'mean_floor':str(m*ceH*fraction)})
    return {'powers':{k:str(v) for k,v in actual.items()},'cap_cases':capcases}

def ceil(x): return -((-x.numerator)//x.denominator)

def elementary(j,N):
    rows=[{(0,0):1}]; boundary=[{0:1}]
    for n in range(N):
        nxt={}
        def add(key,value): nxt[key]=nxt.get(key,0)+value
        for (p,c),value in rows[-1].items():
            add((p+1,c),value)
            if c: add((p+1,c-1),value)
            else:
                for ell in range(p):
                    for b in range(ell+1):
                        m=mult(j,ell,b)
                        if m: add((p-ell,b),value*m)
        rows.append(nxt); boundary.append({p:v for (p,c),v in nxt.items() if c==0})
    return boundary

def cycle_renewal(j,N):
    rows=[{} for _ in range(N+1)]; rows[0][0]=1
    for t in range(N):
        for p,value in list(rows[t].items()):
            rows[t+1][p+1]=rows[t+1].get(p+1,0)+value
            for ell in range(p):
                for b in range(ell+1):
                    m=mult(j,ell,b)
                    if not m: continue
                    if b==0:
                        rows[t+1][p-ell]=rows[t+1].get(p-ell,0)+value*m
                    else:
                        for w in range(b,N-t):
                            end=p+w-ell; L=w+1
                            rows[t+L][end]=rows[t+L].get(end,0)+value*m*choose(w-1,b-1)
    return rows

def countdown(b,W):
    states={b:1}; first={}
    for w in range(1,W+1):
        out={}
        for c,v in states.items():
            out[c]=out.get(c,0)+v
            if c==1: first[w]=first.get(w,0)+v
            else: out[c-1]=out.get(c-1,0)+v
        states=out
    return first

def brute_counts(n):
    counts={'759':0,'247':0}
    for seq in itertools.product(*(range(k) for k in range(1,n+1))):
        allowed759=allowed247=True
        for i in range(n):
            for j in range(i+1,n):
                for k in range(j+1,n):
                    if seq[i]<=seq[j] and seq[i]>=seq[k]:
                        allowed247=False
                        if seq[j]!=seq[k]: allowed759=False
        counts['759']+=int(allowed759); counts['247']+=int(allowed247)
    return counts

def recurrence(e):
    N=e['coverage']['n_max']; result={}
    firstcount=0
    brute=[brute_counts(n) for n in range(e['coverage']['brute_max']+1)]
    for b in range(1,e['coverage']['b_max']+1):
        found=countdown(b,N)
        for w in range(1,N+1):
            need(found.get(w,0)==choose(w-1,b-1),'math:first-return'); firstcount+=1
    for j in ('759','247'):
        a=elementary(j,N); b=cycle_renewal(j,N)
        need(a==b,'math:genuine-time')
        coeff=[sum(v for p,v in row.items() if j=='759' or p<=2) for row in a]
        need(coeff[:4]==[1,1,2,5] if j=='759' else coeff[:4]==[1,1,2,4], 'math:terminal-extraction')
        need(all(coeff[n]==brute[n][j] for n in range(len(brute))),'math:brute-avoidance')
        result[j]={'coefficients':coeff,'boundary_sha256':digest(encoded([{str(k):v for k,v in sorted(row.items())} for row in a]))}
    return {'original_time_max':N,'brute_avoidance_max':e['coverage']['brute_max'],'first_return_cases':firstcount,'classes':result}

# log(x)=2 sum z^(2i+1)/(2i+1), z=(x-1)/(x+1), after binary reduction.
def log_interval(n,terms):
    need(type(n) is int and n>=1,'internal:log-input')
    power=n.bit_length()-1; q=F(n,2**power)
    def partial(z):
        total=sum((2*z**(2*i+1)/F(2*i+1) for i in range(terms)),F(0))
        rem=2*z**(2*terms+1)/(F(2*terms+1)*(1-z*z))
        return total,total+rem
    l2,u2=partial(F(1,3)); lo,hi=partial((q-1)/(q+1))
    return power*l2+lo,power*u2+hi

def certified_floor(n,scale,terms):
    lo,hi=log_interval(n,terms); lo*=scale; hi*=scale
    need(hi-lo<F(1,10**25),'math:log-width')
    need(lo.numerator//lo.denominator==hi.numerator//hi.denominator,'math:log-floor')
    return lo.numerator//lo.denominator

def level(k,terms):
    return certified_floor(k+1,k*k,terms),certified_floor(k+1,k,terms)

def support(j,p,b,ell,w,moderate=True):
    need(b>=1 and w>=b and ell>=b and ell<=p-1,'math:repair-support')
    if j=='247': need(ell<=2*b+1,'math:repair-support')
    alpha=F(3,2) if j=='759' else F(4,3)
    if moderate: need(abs(ell-alpha*b)<=F(b,8) and abs(w-alpha*b)<=F(b,8),'math:repair-window')
    return p+w-ell,w+1

def fill(U,L,R):
    need(R>0 and L>R and 2*R*U>=L*L-R*R,'math:fill-threshold')
    m=ceil(F(U,L+R)); low=L-R; excess=U-m*low
    need(0<=excess<=2*R*m,'math:fill-excess')
    full,res=divmod(excess,2*R)
    runs=[]
    if full: runs.append((L+R,full))
    if res: runs.append((low+res,1))
    count=m-full-(1 if res else 0)
    if count: runs.append((low,count))
    need(sum(length*num for length,num in runs)==U and sum(num for _,num in runs)==m and all(low<=a<=L+R and b>0 for a,b in runs),'math:fill-exact')
    return runs

def repairs(e):
    levels=e['coverage']['levels']; terms=e['coverage']['log_terms']; cached={}
    for k in range(256,259): cached[k]=level(k,terms)
    for k in levels+[k+1 for k in levels]: cached[k]=level(k,terms)
    stage_tests=fill_tests=assemblies=0; samples=[]
    for j in ('759','247'):
        alpha=F(3,2) if j=='759' else F(4,3)
        for K in levels:
            p,R=cached[K]; pnext,_=cached[K+1]; b=p//4; ell=(alpha*b+F(1,2)).numerator//(alpha*b+F(1,2)).denominator; L=ell+1; gap=pnext-p
            for sign in (-1,1):
                end,dur=support(j,p if sign==1 else pnext,b,ell,ell+sign*gap)
                need(end==(pnext if sign==1 else p),'math:stage-endpoint'); stage_tests+=1
            for shift in (-R,0,R):
                end,dur=support(j,p,b,ell+shift,ell+shift)
                need(end==p and dur==L+shift,'math:return-duration'); stage_tests+=1
            U0=ceil(F(L*L-R*R,2*R))
            for off in e['coverage']['fill_offsets']:
                U=U0+off; runs=fill(U,L,R); fill_tests+=1
                for length,num in runs: support(j,p,b,length-1,length-1)
            # All residues modulo 2R at the smallest selected level.
            if K==256:
                for off in range(2*R): fill(U0+off,L,R); fill_tests+=1
            for g in sorted({0,gap//2,gap-1}):
                end,up=support(j,p,b,ell,ell+g)
                need(end==p+g,'math:bridge-up')
                end,down=support(j,p+g,b,ell,ell-g)
                need(end==p,'math:bridge-down')
                # A complete small staircase repair, including genuine integer lengths.
                if K<=258:
                    cursor=p+g; total=0
                    end,Ldown=support(j,cursor,b,ell,ell-g); cursor=end; total+=Ldown
                    U=U0+17+g; runs=fill(U,L,R); total+=sum(a*z for a,z in runs)
                    for k0 in range(K-1,255,-1):
                        pl,_=cached[k0]; ph,_=cached[k0+1]; bb=pl//4; ee=round_fraction(alpha*bb)
                        need(cursor==ph,'math:repair-chain'); cursor,dd=support(j,cursor,bb,ee,ee-(ph-pl)); total+=dd
                    base=cached[256][0]
                    need(cursor==base,'math:repair-base')
                    # b=0 unit-drop edges, legal from p>=3 and ending at 2.
                    need(mult(j,1,0)==1 and base>=3,'math:repair-unit-drop')
                    total+=base-2; cursor=2
                    fixed=down+sum(round_fraction(alpha*(cached[k0][0]//4))-(cached[k0+1][0]-cached[k0][0])+1 for k0 in range(256,K))+base-2
                    need(cursor==2 and total==fixed+U,'math:repair-exact-time'); assemblies+=1
            samples.append({'class':j,'k':K,'p':p,'R':R,'L':L,'threshold':U0})
    return {'certified_levels':len(cached),'stage_return_tests':stage_tests,'fill_tests':fill_tests,'complete_repairs':assemblies,'samples':samples}

def round_fraction(x): return (x+F(1,2)).numerator//(x+F(1,2)).denominator

def run():
    e=load()
    legal=legal_and_moments(e)
    return {'schema':1,'status':'PASS','scope':'finite_exact_regression_only','checks':list(CHECKS),
        'legal_and_moments':legal,'anchor':anchors(e),'algebra':algebra(e),
        'rates_and_cap':rates(e),'genuine_time':recurrence(e),'repair':repairs(e),
        'analytic_report':REPORT,'prior_report':PRIOR_REPORT}

def output(data,path):
    if path is None:
        sys.stdout.buffer.write(data); return
    target=Path(path).absolute()
    need(not target.is_symlink(),'output:symlink')
    resolved=target.resolve(strict=False)
    # Never write into this immutable sealed directory; existing files anywhere are protected.
    need(HERE not in [resolved,*resolved.parents],'output:sealed-directory')
    need(target.parent.exists() and target.parent.is_dir(),'output:parent')
    try:
        fd=os.open(target,os.O_WRONLY|os.O_CREAT|os.O_EXCL|getattr(os,'O_NOFOLLOW',0),0o600)
    except FileExistsError:
        raise Reject('output:exists')
    with os.fdopen(fd,'wb') as handle: handle.write(data)

def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('--output'); args=parser.parse_args()
    try:
        # Check protection before expensive work, and again atomically when opening output.
        if args.output:
            p=Path(args.output).absolute(); r=p.resolve(strict=False)
            need(not p.is_symlink(),'output:symlink')
            need(HERE not in [r,*r.parents],'output:sealed-directory')
            need(not p.exists(),'output:exists')
        output(encoded(run()),args.output)
    except (Reject,ValueError,TypeError,KeyError,ZeroDivisionError,OSError,json.JSONDecodeError) as exc:
        code=str(exc) if isinstance(exc,Reject) else 'invalid-input:'+type(exc).__name__
        print('FAIL '+code,file=sys.stderr); return 1
    return 0

if __name__=='__main__': sys.exit(main())
