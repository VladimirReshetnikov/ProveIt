#!/usr/bin/env python3
"""Exact rational threshold constants used by the uniform-order argument.

The extension from these threshold inequalities to every integer r>=38 uses
analytic inequalities and monotonicity proved in the report. This script checks
the finite rational identities, without claiming to prove that analytic step.
"""
from fractions import Fraction as Q
from pathlib import Path
import json
import os

OUT=Path(os.environ.get('HISTORIC_TREE_OUTPUT_DIR', Path(__file__).resolve().parent))
r=38
log2_lower=2*(Q(1,3)+Q(1,81))
modulus_upper=50*(Q(1,r-1)-Q(1,2*r-1))
phase_lower=10*log2_lower-Q(1000,6*(r-1)**2)
modulus_margin=log2_lower-modulus_upper
phase_margin=phase_lower-Q(44,7)
checks={
    'log2_lower_two_terms_equals_56_over_81':log2_lower==Q(56,81),
    'modulus_upper_at38_equals_76_over_111':modulus_upper==Q(76,111),
    'modulus_margin_equals_20_over_2997':modulus_margin==Q(20,2997),
    'modulus_margin_positive':modulus_margin>0,
    'phase_lower_at38_equals_753140_over_110889':phase_lower==Q(753140,110889),
    'phase_margin_equals_392864_over_776223':phase_margin==Q(392864,776223),
    'phase_margin_positive':phase_margin>0,
}
assert all(checks.values())
record={
    'status':'Exact rational identities; uniform analytic inference is in the report.',
    'threshold_r':r,'threshold_m':r-1,'phase_test_b':10,
    'log2_strict_lower_bound':str(log2_lower),
    'log_modulus_strict_upper_bound_at_threshold':str(modulus_upper),
    'log_modulus_margin':str(modulus_margin),
    'phase_lower_bound_at_threshold':str(phase_lower),
    'two_pi_strict_upper_bound':'44/7',
    'phase_margin':str(phase_margin),
    'checks':checks,'all_exact_checks_pass':all(checks.values()),
}
(OUT/'uniform_threshold_certificate.json').write_text(json.dumps(record,indent=2)+'\n')
print('PASS: 56/81 - 76/111 = 20/2997 > 0.')
print('PASS: 753140/110889 - 44/7 = 392864/776223 > 0.')
