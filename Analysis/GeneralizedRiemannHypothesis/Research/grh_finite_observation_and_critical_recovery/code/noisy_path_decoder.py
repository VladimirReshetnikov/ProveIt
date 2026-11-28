#!/usr/bin/env python3
"""Arithmetic probes for sampled Li--Levy paths.

Input JSON: {"time_step": h, "positions": [x0,...,xN],
             "level_noise_bound": epsilon}.
The positions may already include arbitrary errors of the specified magnitude.
This implements the first-order estimator proved in the accompanying paper.
No conductor, character or zero list is used. Reported standard deviations are
asymptotic scales, not finite-sample certified confidence intervals.

Example: python3 noisy_path_decoder.py samples.json --primes 2 3 5
Dependencies: numpy, scipy. This script does not simulate an exact Levy path.
"""
from functools import lru_cache
from math import log, pi, sqrt
from pathlib import Path
import argparse
import json
import numpy as np
from scipy.integrate import quad


def _raw_weight(u):
    x = u-1.0
    return np.exp(-1.0/(x*(1.0-x))) if 0.0 < x < 1.0 else 0.0


@lru_cache(maxsize=1)
def weight_constants():
    normalizer = quad(_raw_weight,1.0,2.0,epsabs=1e-14,epsrel=1e-13)[0]
    square_integral = quad(lambda u: (_raw_weight(u)/normalizer)**2,
                           1.0,2.0,epsabs=1e-12,epsrel=1e-12)[0]
    return normalizer,square_integral


def choose_bandwidth(time_step, increment_noise_bound):
    """Conservative bandwidth satisfying the paper's CLT conditions asymptotically."""
    mesh_band = time_step**(-0.25)
    noise_band = increment_noise_bound**(-1.0/3.0) if increment_noise_bound else float('inf')
    return min(mesh_band,noise_band)


def decode(positions,time_step,primes,level_noise_bound=0.0,bandwidth=None):
    x = np.asarray(positions,dtype=float)
    if x.ndim != 1 or len(x)<2 or not np.all(np.isfinite(x)):
        raise ValueError('positions must be a finite one-dimensional array of length >=2')
    if not time_step>0 or level_noise_bound<0:
        raise ValueError('time_step must be positive and the error bound nonnegative')
    for p in primes:
        if not isinstance(p,int) or p<2 or any(p%d==0 for d in range(2,int(sqrt(p))+1)):
            raise ValueError(f'{p} is not a prime')
    eta = 2*level_noise_bound
    T = choose_bandwidth(time_step,eta) if bandwidth is None else float(bandwidth)
    if not T>=2:
        raise ValueError('bandwidth must be >=2; the automatic asymptotic regime has not been reached')
    t = (len(x)-1)*time_step
    y = np.abs(np.diff(x))
    lower = 2*np.arctan(1/(4*T))
    upper = 2*np.arctan(1/(2*T))
    selected = (y>lower)&(y<upper)
    heights = 1/(2*np.tan(y[selected]/2))
    z = heights/T-1
    norm,J = weight_constants()
    weights = np.exp(-1/(z*(1-z)))/norm
    estimates = {}
    for p in primes:
        a = pi*sqrt(p)/log(p)
        estimate = -a*np.sum(weights*np.cos(heights*log(p)))/(t*T)
        asymptotic_sd = sqrt(J*pi*p/(2*t*log(p)**2)*log(T)/T)
        estimates[str(p)]={'estimate_real_character_value':float(estimate),
                           'asymptotic_standard_deviation':asymptotic_sd}
    return {'bandwidth':T,'duration':t,'grid_intervals':len(x)-1,
            'increment_noise_bound':eta,'selected_observed_increments':int(selected.sum()),
            'weight_square_integral':J,'estimates':estimates,
            'clt_mesh_quantity':time_step*T**3.5*log(T)**1.5,
            'clt_noise_quantity':eta*T**2.5*sqrt(log(T)),
            'interpretation':'The two CLT quantities must tend to zero in a sequence of observations. '
                             'They are not universal finite-sample error certificates.'}


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',type=Path)
    parser.add_argument('--primes',type=int,nargs='+',default=[2,3,5])
    parser.add_argument('--bandwidth',type=float)
    args=parser.parse_args()
    data=json.loads(args.input.read_text())
    result=decode(data['positions'],float(data['time_step']),args.primes,
                  float(data.get('level_noise_bound',0.0)),args.bandwidth)
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
