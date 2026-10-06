#!/usr/bin/env python3
import sys
if not sys.flags.isolated:
    sys.stderr.write('REJECTED: isolated Python (-I) is required before any imports\n')
    raise SystemExit(2)
sys.dont_write_bytecode = True
"""Offline Report140 verifier. Review executable provenance before running.
Hashes establish internal consistency, not authorship or safety of replaced code.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import io
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import types
import zipfile

ROOT = Path(__file__).absolute().parent
MAX_FILE = 16 * 1024 * 1024
MAX_TOTAL = 64 * 1024 * 1024
MAX_MEMBERS = 128
EPOCH = 1790899200
MANIFEST = 'manifest.json'
DIRECTORIES = frozenset({'code', 'checks', 'sources', 'dependencies'})
SOURCE_HASHES = {'check_avoidance_recurrence.json': '3d1e8c00ae1437d6602f919c6f457a7982ed83b304140b476ff03606794448c3', 'independent_extension_checks.json': 'b2b5353fec92dd9b7864db215aeef5bb6795c78cee8f6842a4b47e96868ccb1f'}
DEPENDENCY_HASH = '360c9db76eb482a21b75396b0b71941e1399ad27803441e25f945c6c03c2c484'
BASELINE_HASHES = {'Report138.tex': '7d8c2a5a280658ef5f09ea2f7caea3f27b68206a7a3e99fa9c25ebebb7f8d428',
                  'Report138.pdf': '7624a807149ae5f898b3acc02f44709a1e6033aae7ff432172c6283b897b013a'}
PAYLOAD = frozenset({'README.md', 'SOURCES.md', 'Report140.tex', 'Report140.pdf', 'verify.py',
                     'code/exact.py', 'checks/fixtures.json', 'sources/inventory.json',
                     'dependencies/Report138_reproducible.zip'}) | frozenset('sources/'+s for s in SOURCE_HASHES)
CONTRACTS = {'checks/fixtures.json': ('dict', {'arithmetic': ('text',), 'binomial_product': ('dict', {'binomial_recurrence_comparisons': ('int',), 'coefficient_comparisons': ('int',), 'exact_zero_coefficients_beyond_polynomial_degree': ('int',), 'j_k_range': ('list', [('int',), ('int',)]), 'model_pairs': ('int',), 'n_range': ('list', [('int',), ('int',)]), 'recurrence_j_range': ('list', [('int',), ('int',)]), 'recurrence_n_range': ('list', [('int',), ('int',)]), 'status': ('literal', 'PASS')}), 'characters_and_half_corrections': ('dict', {'characters_checked': ('int',), 'half_examples': ('list', [('dict', {'B': ('rational',), 'boundary': ('list', [('int',), ('int',), ('int',), ('int',)]), 'h': ('rational',), 'independent_shifted_avoidance': ('dict', {'A_s_plus_1_multiplier': ('int',), 'B': ('rational',), 'h': ('rational',)}), 'scale': ('rational',), 'six_character_terms': ('list', [('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])})])}), ('dict', {'B': ('rational',), 'boundary': ('list', [('int',), ('int',), ('int',), ('int',)]), 'h': ('rational',), 'independent_shifted_avoidance': ('dict', {'A_s_plus_1_multiplier': ('int',), 'B': ('rational',), 'h': ('rational',)}), 'scale': ('rational',), 'six_character_terms': ('list', [('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])})])}), ('dict', {'B': ('rational',), 'boundary': ('list', [('int',), ('int',), ('int',), ('int',)]), 'h': ('rational',), 'scale': ('rational',), 'six_character_terms': ('list', [('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])}), ('dict', {'B_summand': ('rational',), 'D_F': ('rational',), 'D_G': ('rational',), 'J_F': ('rational',), 'J_G': ('rational',), 'h_summand': ('rational',), 'tau': ('list', [('int',), ('int',)])})])})]), 'maximum_rows': ('int',), 'method': ('text',), 'partition_size_range': ('list', [('int',), ('int',)]), 'status': ('literal', 'PASS')}), 'discrete_taylor': ('dict', {'d_range': ('list', [('int',), ('int',)]), 'exact_remainder_identity_comparisons': ('int',), 'j_range': ('list', [('int',), ('int',)]), 'n_range': ('list', [('int',), ('int',)]), 's_range': ('text',), 'status': ('literal', 'PASS')}), 'gamma_ratio': ('dict', {'coefficient_comparisons': ('int',), 'coefficient_degree_range': ('list', [('int',), ('int',)]), 'methods': ('list', [('text',), ('text',)]), 'model_index_range': ('list', [('int',), ('int',)]), 'models': ('list', [('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)}), ('dict', {'coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'j': ('int',), 'x': ('rational',)})]), 'status': ('literal', 'PASS')}), 'gaussian': ('dict', {'alpha1': ('rational',), 'largest_total_polynomial_degree': ('int',), 'method': ('text',), 'moments': ('dict', {'Q2': ('rational',), 'Q2_squared': ('rational',), 'Q4': ('rational',)}), 'normalizing_polynomial_moment': ('rational',), 'status': ('literal', 'PASS')}), 'inverse_reversion': ('dict', {'a_degrees': ('list', [('int',), ('int',), ('int',), ('int',)]), 'integer_threshold_rounding_certified': ('bool',), 'polynomials': ('list', [('dict', {'terms': ('list', [('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])})]), 'variables': ('list', [('text',), ('text',), ('text',), ('text',), ('text',), ('text',)])}), ('dict', {'terms': ('list', [('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])})]), 'variables': ('list', [('text',), ('text',), ('text',), ('text',), ('text',), ('text',)])}), ('dict', {'terms': ('list', [('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])})]), 'variables': ('list', [('text',), ('text',), ('text',), ('text',), ('text',), ('text',)])}), ('dict', {'terms': ('list', [('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',), ('int',)])})]), 'variables': ('list', [('text',), ('text',), ('text',), ('text',), ('text',), ('text',)])})]), 'residual_coefficients_through_order': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'status': ('literal', 'PASS'), 'symbolic_variables': ('list', [('text',), ('text',), ('text',), ('text',), ('text',), ('text',)]), 'verified_orders': ('int',)}), 'moment_stirling': ('dict', {'finite_sequence_support': ('list', [('int',), ('int',)]), 'first_required_subtraction_order': ('int',), 'infinite_moments_numerically_approximated': ('bool',), 'model_partial_sum_N_range': ('list', [('int',), ('int',)]), 'model_partial_sum_comparisons': ('int',), 'model_partial_sum_condition': ('text',), 'model_partial_sum_j_range': ('list', [('int',), ('int',)]), 'model_partial_sum_l_range': ('list', [('int',), ('int',)]), 'moment_orders': ('list', [('int',), ('int',)]), 'moment_transform_comparisons': ('int',), 'power_identity_comparisons': ('int',), 'regularization_exponent_checks': ('list', [('dict', {'last_subtracted_model': ('int',), 'moment_order': ('int',), 'weighted_tail_exponent': ('rational',)}), ('dict', {'last_subtracted_model': ('int',), 'moment_order': ('int',), 'weighted_tail_exponent': ('rational',)}), ('dict', {'last_subtracted_model': ('int',), 'moment_order': ('int',), 'weighted_tail_exponent': ('rational',)}), ('dict', {'last_subtracted_model': ('int',), 'moment_order': ('int',), 'weighted_tail_exponent': ('rational',)}), ('dict', {'last_subtracted_model': ('int',), 'moment_order': ('int',), 'weighted_tail_exponent': ('rational',)}), ('dict', {'last_subtracted_model': ('int',), 'moment_order': ('int',), 'weighted_tail_exponent': ('rational',)})]), 'status': ('literal', 'PASS')}), 'ratio_and_shift': ('dict', {'alpha1_cancellation_verified': ('bool',), 'exponential_factor': ('rational',), 'orders': ('list', [('int',), ('int',)]), 'sample_coefficient_comparisons': ('int',), 'samples': ('list', [('dict', {'ratio_coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'sample': ('int',), 'shifted_coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)])}), ('dict', {'ratio_coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'sample': ('int',), 'shifted_coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)])}), ('dict', {'ratio_coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)]), 'sample': ('int',), 'shifted_coefficients': ('list', [('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',), ('rational',)])})]), 'shift': ('rational',), 'status': ('literal', 'PASS'), 'symbolic_first_ratio_correction': ('dict', {'terms': ('list', [('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',)])}), ('dict', {'coefficient': ('rational',), 'powers': ('list', [('int',), ('int',), ('int',), ('int',), ('int',)])})]), 'variables': ('list', [('text',), ('text',), ('text',), ('text',), ('text',)])})}), 'schema': ('literal', 'report140-independent-exact-v1'), 'scope': ('text',), 'status': ('literal', 'PASS'), 'triangular_matching': ('dict', {'T1_U0_coefficient': ('rational',), 'first_direct_convolution_coefficients': ('dict', {'B0_U0_m0': ('rational',), 'B1_U0_m1': ('rational',), 'B1_U1_m0': ('rational',), 'B2_U0_m2': ('rational',), 'B2_U1_m1': ('rational',), 'B2_U2_m0': ('rational',)}), 'matrix_dimension': ('int',), 'matrix_inverse_entries_checked': ('int',), 'orders': ('list', [('int',), ('int',)]), 'shift_polynomial_coefficients_compared': ('int',), 'status': ('literal', 'PASS')})}), 'sources/check_avoidance_recurrence.json': ('dict', {'source': ('text',), 'solved_relative_coefficients': ('dict', {'a1': ('rational',), 'a2': ('rational',)}), 'status': ('literal', 'PASS')}), 'sources/independent_extension_checks.json': ('dict', {'characters': ('dict', {'tests': ('int',), 'max_size': ('int',), 'max_rows': ('int',), 'status': ('literal', 'PASS')}), 'gaussian': ('dict', {'normalizing_polynomial_moment': ('rational',), 'moments': ('dict', {'Q2': ('rational',), 'Q2_squared': ('rational',), 'Q4': ('rational',)}), 'alpha1': ('rational',), 'alpha2_independent_extra': ('rational',), 'status': ('literal', 'PASS')}), 'gamma_ratio': ('dict', {'coefficient_comparisons': ('int',), 'degree_range': ('text',), 'model_range': ('text',), 'status': ('literal', 'PASS')}), 'coefficient_prescriptions': ('dict', {'orders': ('text',), 'independent_bilinear_coefficients_compared': ('int',), 'status': ('literal', 'PASS')}), 'inverse': ('dict', {'verified_orders': ('int',), 'P1': ('text',), 'P2': ('text',), 'P3': ('text',), 'P4': ('text',), 'status': ('literal', 'PASS')}), 'elapsed_seconds': ('number',)}), 'sources/inventory.json': ('dict', {'files': ('dict', {'check_avoidance_recurrence.json': ('dict', {'bytes': ('int',), 'captured': ('text',), 'origin': ('text',), 'purpose': ('text',), 'sha256': ('hash',)}), 'independent_extension_checks.json': ('dict', {'bytes': ('int',), 'captured': ('text',), 'origin': ('text',), 'purpose': ('text',), 'sha256': ('hash',)})}), 'schema': ('literal', 'report140-source-inventory-v1')}), 'manifest.json': ('dict', {'schema': ('literal', 'report140-sha256-v1'), 'files': ('dict', {'README.md': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'Report140.pdf': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'Report140.tex': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'SOURCES.md': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'checks/fixtures.json': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'code/exact.py': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'dependencies/Report138_reproducible.zip': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'sources/check_avoidance_recurrence.json': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'sources/independent_extension_checks.json': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'sources/inventory.json': ('dict', {'bytes': ('int',), 'sha256': ('hash',)}), 'verify.py': ('dict', {'bytes': ('int',), 'sha256': ('hash',)})})})}

class Rejected(Exception):
    pass

def require(condition, message):
    if not condition:
        raise Rejected(message)

def digest(raw):
    return hashlib.sha256(raw).hexdigest()

def json_bytes(value):
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False)+'\n').encode('ascii')

def reject_constant(token):
    raise Rejected('nonfinite JSON token: '+token)

def parse_int(token):
    require(len(token) <= 128, 'oversized JSON integer')
    return int(token)

def parse_float(token):
    require(len(token) <= 128, 'oversized JSON float')
    result = float(token)
    require(math.isfinite(result), 'nonfinite or overflowing JSON float')
    return result

def unique_pairs(pairs):
    result = {}
    for key, value in pairs:
        require(key not in result, 'duplicate JSON key: '+key)
        result[key] = value
    return result

def parse_json(raw):
    require(type(raw) is bytes and len(raw) <= MAX_FILE, 'JSON size/type limit')
    return json.loads(raw.decode('utf-8'), object_pairs_hook=unique_pairs,
                      parse_constant=reject_constant, parse_int=parse_int, parse_float=parse_float)

def keys(value, expected, label):
    require(type(value) is dict and set(value) == set(expected), label+' closed keys/type')

def typed(value, schema, label='value'):
    kind = schema[0]
    if kind == 'dict':
        keys(value, schema[1], label)
        for name, subschema in schema[1].items():
            typed(value[name], subschema, label+'.'+name)
    elif kind == 'list':
        require(type(value) is list and len(value) == len(schema[1]), label+' list length/type')
        for index, subschema in enumerate(schema[1]):
            typed(value[index], subschema, label+'['+str(index)+']')
    elif kind == 'int':
        require(type(value) is int and abs(value).bit_length() <= 4096, label+' bounded integer required (bool excluded)')
    elif kind == 'number':
        require(type(value) in (int, float) and value >= 0 and
                (type(value) is int or math.isfinite(value)), label+' finite nonnegative number required')
    elif kind == 'bool':
        require(type(value) is bool, label+' boolean required')
    elif kind == 'literal':
        require(type(value) is type(schema[1]) and value == schema[1], label+' fixed literal')
    elif kind == 'rational':
        require(type(value) is str and len(value) <= 1024 and re.fullmatch(r'-?(?:0|[1-9][0-9]*)(?:/[1-9][0-9]*)?', value) is not None, label+' rational syntax')
        require(str(Fraction(value)) == value, label+' canonical rational required')
    elif kind == 'hash':
        require(type(value) is str and re.fullmatch('[0-9a-f]{64}', value) is not None, label+' SHA256 syntax')
    elif kind == 'text':
        require(type(value) is str and 0 < len(value) <= 16384, label+' bounded nonempty text required')
    else:
        raise Rejected('unknown executable schema kind')

def path_absolute(value):
    require(type(value) in (str, Path) or isinstance(value, Path), 'path type')
    raw = str(value)
    require(not raw.startswith('//') and '\x00' not in raw and '\\' not in raw, 'ambiguous path spelling')
    require('..' not in raw.split('/'), 'parent traversal refused')
    path = Path(raw)
    return path if path.is_absolute() else Path.cwd()/path

def ancestors(path, absent_leaf=False):
    path = path_absolute(path)
    current = Path(path.anchor)
    for index, part in enumerate(path.parts[1:]):
        current /= part
        leaf = index == len(path.parts)-2
        try:
            mode = current.lstat().st_mode
        except FileNotFoundError:
            require(leaf and absent_leaf, 'missing path ancestor: '+str(current))
            return
        require(not stat.S_ISLNK(mode), 'symlink path component refused: '+str(current))
        if not leaf:
            require(stat.S_ISDIR(mode), 'non-directory ancestor')

def read_regular(path, limit=MAX_FILE):
    ancestors(path)
    fd = os.open(path, os.O_RDONLY | getattr(os, 'O_NOFOLLOW', 0) | getattr(os, 'O_NONBLOCK', 0))
    with os.fdopen(fd, 'rb') as stream:
        info = os.fstat(stream.fileno())
        require(stat.S_ISREG(info.st_mode), 'nonregular input refused')
        require(info.st_size <= limit, 'input size limit')
        raw = stream.read(limit+1)
        require(len(raw) <= limit, 'bounded input read exceeded')
        return raw

def output_path(value):
    ancestors(ROOT)
    path = path_absolute(value)
    ancestors(path, absent_leaf=True)
    require(not path.exists() and not path.is_symlink(), 'output already exists')
    root = ROOT.resolve(strict=True)
    path = path.resolve(strict=False)
    require(path != root and root not in path.parents, 'output must be outside bundle')
    require(path.parent.is_dir(), 'output parent must already exist')
    return path

def mkdir(path):
    ancestors(path, absent_leaf=True)
    os.mkdir(path, 0o700)

def write_new(path, raw):
    ancestors(path, absent_leaf=True)
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | getattr(os, 'O_NOFOLLOW', 0), 0o600)
    with os.fdopen(fd, 'wb') as stream:
        stream.write(raw)

def inventory(root=ROOT, sealing=False):
    ancestors(root)
    require(root.is_dir(), 'bundle root must be directory')
    found = {}; dirs = set(); total = 0
    for directory, subdirs, files in os.walk(root, followlinks=False):
        for name in subdirs:
            path = Path(directory)/name; relative = path.relative_to(root).as_posix()
            require(relative in DIRECTORIES and stat.S_ISDIR(path.lstat().st_mode), 'unexpected or symlink directory: '+relative)
            dirs.add(relative)
        for name in files:
            path = Path(directory)/name; relative = path.relative_to(root).as_posix()
            require(relative in PAYLOAD | {MANIFEST}, 'unexpected file: '+relative)
            found[relative] = read_regular(path)
            total += len(found[relative]); require(total <= MAX_TOTAL, 'aggregate bundle size limit')
    expected = PAYLOAD | {MANIFEST}
    if sealing and MANIFEST not in found:
        expected = PAYLOAD
    require(dirs == DIRECTORIES and set(found) == expected, 'closed bundle inventory differs')
    return found

def make_manifest(data):
    return {'schema': 'report140-sha256-v1', 'files': {name: {'bytes': len(data[name]), 'sha256': digest(data[name])} for name in sorted(PAYLOAD)}}

def validate_manifest(data):
    manifest = parse_json(data[MANIFEST])
    keys(manifest, {'schema', 'files'}, 'manifest')
    require(manifest['schema'] == 'report140-sha256-v1', 'manifest schema')
    keys(manifest['files'], PAYLOAD, 'manifest files')
    for name, record in manifest['files'].items():
        keys(record, {'bytes', 'sha256'}, 'manifest record')
        require(type(record['bytes']) is int and record['bytes'] == len(data[name]), 'manifest bytes type/value')
        require(type(record['sha256']) is str and record['sha256'] == digest(data[name]), 'manifest SHA256: '+name)

def archive_members(raw, prefix, expected=None):
    require(type(raw) is bytes and len(raw) <= MAX_FILE, 'ZIP input size limit')
    result = {}; total = 0
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        require(not archive.comment, 'ZIP comments refused')
        entries = archive.infolist()
        require(len(entries) <= MAX_MEMBERS, 'ZIP member count limit')
        for info in entries:
            name = info.filename
            require(type(name) is str and name.startswith(prefix+'/') and name.isascii() and '\\' not in name and '\x00' not in name, 'unsafe ZIP path')
            parts = name.split('/')
            require(all(part not in ('', '.', '..') for part in parts), 'ZIP traversal/empty path')
            relative = '/'.join(parts[1:])
            require(relative not in result, 'duplicate ZIP member')
            require(not info.is_dir() and stat.S_ISREG(info.external_attr >> 16), 'ZIP nonregular member')
            require(info.create_system == 3 and info.compress_type == zipfile.ZIP_STORED and info.flag_bits == 0 and not info.extra and not info.comment, 'unsupported ZIP metadata')
            require(info.file_size <= MAX_FILE and info.compress_size == info.file_size, 'ZIP member size/compression limit')
            total += info.file_size; require(total <= MAX_TOTAL, 'ZIP aggregate size limit')
            with archive.open(info) as stream:
                content = stream.read(MAX_FILE+1)
                require(len(content) == info.file_size and len(content) <= MAX_FILE, 'ZIP bounded read/size mismatch')
            result[relative] = content
    if expected is not None:
        require(set(result) == set(expected), 'ZIP closed member inventory')
    return result

def dependency(data):
    raw = data['dependencies/Report138_reproducible.zip']
    require(DEPENDENCY_HASH != 'UNFROZEN' and digest(raw) == DEPENDENCY_HASH, 'dependency ZIP frozen hash')
    members = archive_members(raw, 'Report138')
    require('manifest.json' in members, 'dependency manifest absent')
    manifest = parse_json(members['manifest.json'])
    keys(manifest, {'schema', 'files'}, 'dependency manifest')
    require(manifest['schema'] == 'report138-sha256-v1', 'dependency manifest schema')
    keys(manifest['files'], set(members)-{'manifest.json'}, 'dependency inventory')
    for name, rec in manifest['files'].items():
        keys(rec, {'bytes', 'sha256'}, 'dependency record')
        require(type(rec['bytes']) is int and rec['bytes'] == len(members[name]), 'dependency bytes')
        require(type(rec['sha256']) is str and rec['sha256'] == digest(members[name]), 'dependency member hash')
    for name, expected in BASELINE_HASHES.items():
        require(name in members and digest(members[name]) == expected, 'frozen baseline '+name)
    return members

def validate_payload(data):
    for filename, schema in CONTRACTS.items():
        if filename == MANIFEST and filename not in data:
            continue  # External sealing has no installed manifest yet.
        typed(parse_json(data[filename]), schema, filename)
    source_inventory = parse_json(data['sources/inventory.json'])
    for name, expected in SOURCE_HASHES.items():
        raw = data['sources/'+name]
        require(digest(raw) == expected, 'pinned provenance hash: '+name)
        record = source_inventory['files'][name]
        require(type(record['bytes']) is int and record['bytes'] == len(raw), 'source inventory bytes')
        require(record['sha256'] == expected, 'source inventory hash')
    require(data['Report140.pdf'].startswith(b'%PDF-'), 'PDF header')
    require(b'\\begin{document}' in data['Report140.tex'] and b'\\end{document}' in data['Report140.tex'], 'TeX document markers')
    dependency(data)

def verify():
    data = inventory(); validate_manifest(data); validate_payload(data)
    return data

def replay(data):
    module = types.ModuleType('report140_exact')
    module.__file__ = str(ROOT/'code/exact.py')
    exec(compile(data['code/exact.py'], 'code/exact.py', 'exec'), module.__dict__)
    result = module.run()
    typed(result, CONTRACTS['checks/fixtures.json'], 'computed exact result')
    require(result == parse_json(data['checks/fixtures.json']), 'independently recomputed mathematics differs from fixture')
    return result

def zip_bytes(data, prefix='Report140'):
    target = io.BytesIO()
    with zipfile.ZipFile(target, 'w', compression=zipfile.ZIP_STORED) as archive:
        for name in sorted(data):
            info = zipfile.ZipInfo(prefix+'/'+name, date_time=(1980,1,1,0,0,0))
            info.create_system = 3; info.external_attr = (stat.S_IFREG | 0o644) << 16
            info.compress_type = zipfile.ZIP_STORED
            archive.writestr(info, data[name])
    raw = target.getvalue(); require(len(raw) <= MAX_FILE, 'packed ZIP size limit')
    return raw

def extract_checked(raw, destination):
    members = archive_members(raw, 'Report140', PAYLOAD | {MANIFEST})
    # Validate everything before creating any output, and never use extractall.
    validate_manifest(members); validate_payload(members)
    mkdir(destination)
    for folder in sorted(DIRECTORIES): mkdir(destination/folder)
    for name, content in members.items(): write_new(destination/name, content)
    return members

def pack(data, output):
    raw = zip_bytes(data); write_new(output, raw)
    return {'sha256': digest(raw), 'bytes': len(raw)}

def build(data, output):
    mkdir(output); write_new(output/'Report140.tex', data['Report140.tex'])
    env = {key: value for key, value in os.environ.items() if key in ('PATH','SYSTEMROOT','WINDIR')}
    env.update(SOURCE_DATE_EPOCH=str(EPOCH), FORCE_SOURCE_DATE='1', TZ='UTC', LC_ALL='C')
    for key, name in [('HOME','home'),('TEXMFHOME','texmf-home'),('TEXMFVAR','texmf-var'),('TEXMFCONFIG','texmf-config'),('TEXMFCACHE','texmf-cache'),('XDG_CACHE_HOME','xdg-cache')]:
        mkdir(output/name); env[key] = str(output/name)
    if Path('/usr/share/texlive/texmf-dist').is_dir():
        env['TEXMF'] = '{/usr/share/texlive/texmf-dist,/usr/share/texmf}'
    env['TEXFORMATS'] = str(output)+'//:'
    commands = [['pdftex','-ini','-etex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-jobname=pdflatex','pdflatex.ini']]
    source = r'\pdfmapfile{+cm.map}\pdfmapfile{+cmextra.map}\pdfmapfile{+symbols.map}\pdfmapfile{+lm.map}\input{Report140.tex}'
    command = ['pdflatex','-no-shell-escape','-interaction=nonstopmode','-halt-on-error','-file-line-error',source]
    commands += [command]*3
    console = b''
    for command in commands:
        process = subprocess.run(command, cwd=output, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
        require(len(process.stdout) <= MAX_FILE, 'build log size limit')
        console += process.stdout
        if process.returncode:
            write_new(output/'build-console.txt', console)
            raise Rejected('clean TeX build failed; see build-console.txt')
    write_new(output/'build-console.txt', console)
    log = read_regular(output/'Report140.log').decode('utf-8', errors='replace')
    for warning in (r'Overfull \hbox',r'Overfull \vbox','undefined references','multiply defined','undefined citations','Missing character:','Label(s) may have changed'):
        require(warning not in log, 'TeX QA warning: '+warning)
    pdf = read_regular(output/'Report140.pdf')
    version = subprocess.run(['pdftex','--version'], env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=30).stdout.decode('utf-8').splitlines()[0]
    result = {'status':'PASS','pdf_sha256':digest(pdf),'matches_frozen_pdf_bytes':pdf == data['Report140.pdf'],'source_date_epoch':EPOCH,'pdftex_version':version}
    write_new(output/'build-result.json', json_bytes(result))
    return result

def invoke(root, args, optimized=False, isolated=True, success=True):
    cmd = [sys.executable]+(['-I'] if isolated else [])+['-B']+(['-O'] if optimized else [])+[str(root/'verify.py')]+args
    process = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=1200)
    require((process.returncode == 0) == success, 'unexpected subprocess exit: '+repr(args)+' '+process.stderr.decode('utf-8', errors='replace'))
    return process

def expect_rejection(function, label):
    try:
        function()
    except (Rejected, ValueError, TypeError, KeyError, OSError, zipfile.BadZipFile, RecursionError):
        return
    raise Rejected('guard accepted mutation: '+label)

def walk_schema(schema, path=()):
    yield path, schema
    if schema[0] == 'dict':
        for name, child in schema[1].items():
            yield from walk_schema(child, path+(name,))
    elif schema[0] == 'list':
        for index, child in enumerate(schema[1]):
            yield from walk_schema(child, path+(index,))

def replace_path(value, path, replacement):
    result = copy.deepcopy(value)
    if not path: return replacement
    node = result
    for key in path[:-1]: node = node[key]
    node[path[-1]] = replacement
    return result

def schema_selftest(data):
    count = 0; fields = 0
    for filename, schema in CONTRACTS.items():
        value = parse_json(data[filename]); typed(value, schema, filename)
        for path, subschema in walk_schema(schema):
            fields += 1
            node = value
            for key in path: node = node[key]
            variants = [None]
            kind = subschema[0]
            if kind == 'dict':
                variants += [dict(node, __unexpected__=1)]
                for key in node:
                    removed = dict(node); removed.pop(key); variants.append(removed)
            elif kind == 'list':
                variants += [node+[None], node[:-1] if node else [None], {}]
            elif kind in ('int','number'): variants += [True, False, '1']
            elif kind == 'bool': variants += [0,1,'true']
            else: variants += [False, 1, {}, []]
            if kind == 'int': variants += [1.0]
            if kind == 'number': variants += [float('inf'),float('-inf'),float('nan'),-1]
            if kind == 'rational': variants += ['2/2','1/0','01','0.5','__import__("os")']
            if kind == 'hash': variants += ['g'*64,'0'*63]
            for bad in variants:
                changed = replace_path(value, path, bad)
                expect_rejection(lambda:typed(changed, schema, filename), filename+repr(path))
                count += 1
        # Duplicate keys, overflow and nonfinite tokens in every JSON contract.
        for raw in (b'{"x":1,"x":2}', b'{"x":NaN}', b'{"x":Infinity}', b'{"x":-Infinity}', b'{"x":1e999}', b'{"x":-1e999}', b'{"x":'+b'1'*129+b'}'):
            expect_rejection(lambda:parse_json(raw), filename+' parser'); count += 1
    return {'fields_exercised':fields,'rejected_mutations':count}

def selftest(data, output):
    mkdir(output); cases=[]
    summary = schema_selftest(data); cases.append('closed_typed_all_field_mutations')
    def clone(label, revised=None):
        root=output/label; mkdir(root)
        for folder in sorted(DIRECTORIES): mkdir(root/folder)
        for name, content in (data if revised is None else revised).items(): write_new(root/name,content)
        return root
    clean=clone('clean')
    for optimized in (False,True): invoke(clean,['check'],optimized=optimized)
    cases.append('normal_and_optimized_integrity')
    changes=[('extra_file',lambda p:write_new(p/'extra',b'x')),
             ('extra_directory',lambda p:mkdir(p/'extra')),
             ('missing_pdf',lambda p:(p/'Report140.pdf').unlink()),
             ('changed_code',lambda p:(p/'code/exact.py').write_bytes(data['code/exact.py']+b'\n')),
             ('symlink_file',lambda p:(p/'README.md').unlink() or (p/'README.md').symlink_to(clean/'README.md')),
             ('broken_symlink',lambda p:(p/'extra').symlink_to(p/'absent')),
             ('symlink_code_directory',lambda p:((p/'code').rename(p/'moved-code'),(p/'code').symlink_to(p/'moved-code',target_is_directory=True)))]
    if hasattr(os,'mkfifo'): changes.append(('fifo',lambda p:os.mkfifo(p/'README.md') if not (p/'README.md').exists() else ((p/'README.md').unlink(),os.mkfifo(p/'README.md'))))
    for label, change in changes:
        root=clone(label);change(root)
        for optimized in (False,True): invoke(root,['check'],optimized=optimized,success=False)
        cases.append(label)
    for filename in CONTRACTS:
        revised=dict(data); revised[filename]=data[filename].replace(b'{',b'{"__duplicate__":0,"__duplicate__":1,',1)
        if filename != MANIFEST: revised[MANIFEST]=json_bytes(make_manifest(revised))
        root=clone('duplicate-'+filename.replace('/','_'),revised)
        for optimized in (False,True): invoke(root,['check'],optimized=optimized,success=False)
        cases.append('duplicate_'+filename)
    for label, mutation in [('missing',lambda m:m['files'].pop('README.md')),('extra',lambda m:m['files'].update(extra={})),('bool_size',lambda m:m['files']['README.md'].update(bytes=True)),('float_size',lambda m:m['files']['README.md'].update(bytes=1.0)),('hash_type',lambda m:m['files']['README.md'].update(sha256=1)),('extra_record_key',lambda m:m['files']['README.md'].update(extra=1))]:
        revised=dict(data);manifest=parse_json(data[MANIFEST]);mutation(manifest);revised[MANIFEST]=json_bytes(manifest);root=clone('manifest-'+label,revised)
        for optimized in (False,True): invoke(root,['check'],optimized=optimized,success=False)
        cases.append('manifest_'+label)
    revised=dict(data);fixture=parse_json(data['checks/fixtures.json'])
    leaf=next(path for path,schema in walk_schema(CONTRACTS['checks/fixtures.json']) if schema[0]=='rational')
    value=fixture
    for key in leaf:value=value[key]
    fixture=replace_path(fixture,leaf,str(Fraction(value)+1));revised['checks/fixtures.json']=json_bytes(fixture);revised[MANIFEST]=json_bytes(make_manifest(revised))
    root=clone('well-typed-false',revised);invoke(root,['check'])
    for optimized in (False,True):
        result_path=output/('false-result-'+str(optimized));invoke(root,['replay','--output',str(result_path)],optimized=optimized,success=False)
        require(not result_path.exists(),'failed arithmetic replay created output')
    cases.append('well_typed_resealed_false_fixture_rejected_by_recomputation')
    marker=output/'UNSAFE_MARKER';root=clone('shadow')
    write_new(root/'argparse.py',('open('+repr(str(marker))+',"w").write("unsafe")\n').encode())
    for optimized in (False,True):
        process=invoke(root,['check'],optimized=optimized,isolated=False,success=False)
        require(b'isolated Python (-I) is required' in process.stderr and not marker.exists(),'early isolation guard failed')
        invoke(root,['check'],optimized=optimized,success=False)
        require(not marker.exists(),'isolated shadow import executed')
    cases.append('early_isolation_before_shadowable_imports')
    direct=clone('direct-shadow');write_new(direct/'code/fractions.py',('open('+repr(str(marker))+',"w").write("unsafe")\n').encode())
    for optimized in (False,True):
        process=subprocess.run([sys.executable,'-B']+(['-O'] if optimized else [])+[str(direct/'code/exact.py')],stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=60)
        require(process.returncode==2 and b'isolated Python (-I) is required' in process.stderr and not marker.exists(),'direct math early isolation guard')
    cases.append('direct_math_isolation_guard')
    existing=output/'existing';mkdir(existing);file=output/'existing-file';write_new(file,b'preserve');link=output/'linked';link.symlink_to(existing,target_is_directory=True)
    guards=[existing,file,clean/'generated',clean/'code/generated',link,link/'new',existing/'..'/'new',output/'absent/new','//'+str(clean/'new').lstrip('/')]
    for index,path in enumerate(guards):
        for command in ('replay','selftest','pack','build','seal','reproduce'):
            invoke(clean,[command,'--output',str(path)],success=False)
        cases.append('output_path_guard_'+str(index))
    require(read_regular(file)==b'preserve','existing output overwritten')
    alias=output/'linked-bundle';alias.symlink_to(clean,target_is_directory=True);invoke(alias,['check'],success=False)
    invoke(clean/'..'/'clean',['check'],success=False);cases.append('symlink_and_traversal_bundle_paths')
    # Bounded input rejects a sparse oversized file without allocating its contents.
    sparse=output/'oversized';write_new(sparse,b'')
    with open(sparse,'r+b') as stream:stream.truncate(MAX_FILE+1)
    expect_rejection(lambda:read_regular(sparse),'bounded read');cases.append('bounded_regular_reads')
    raw=zip_bytes(data)
    members=archive_members(raw,'Report140',PAYLOAD|{MANIFEST})
    def bad_zip(names):
        stream=io.BytesIO()
        with zipfile.ZipFile(stream,'w',compression=zipfile.ZIP_STORED) as archive:
            for name,mode in names:
                info=zipfile.ZipInfo(name);info.create_system=3;info.external_attr=mode<<16;archive.writestr(info,b'x')
        return stream.getvalue()
    for label,names in [('traversal',[('Report140/../bad',stat.S_IFREG|0o644)]),('absolute',[('/Report140/bad',stat.S_IFREG|0o644)]),('backslash',[('Report140/a\\b',stat.S_IFREG|0o644)]),('duplicate',[('Report140/a',stat.S_IFREG|0o644)]*2),('symlink',[('Report140/a',stat.S_IFLNK|0o777)]),('directory',[('Report140/a/',stat.S_IFDIR|0o755)])]:
        expect_rejection(lambda:archive_members(bad_zip(names),'Report140'),label);cases.append('ZIP_'+label)
    oversized_members=bad_zip([('Report140/file'+str(i),stat.S_IFREG|0o644) for i in range(MAX_MEMBERS+1)])
    expect_rejection(lambda:archive_members(oversized_members,'Report140'),'ZIP member count');cases.append('ZIP_member_count_limit')
    extra_comment=io.BytesIO(raw)
    with zipfile.ZipFile(extra_comment,'a') as archive: archive.comment=b'not permitted'
    expect_rejection(lambda:archive_members(extra_comment.getvalue(),'Report140'),'ZIP comment');cases.append('ZIP_comment_guard')
    compressed=io.BytesIO()
    with zipfile.ZipFile(compressed,'w',compression=zipfile.ZIP_DEFLATED) as archive:
        info=zipfile.ZipInfo('Report140/a');info.create_system=3;info.external_attr=(stat.S_IFREG|0o644)<<16;info.compress_type=zipfile.ZIP_DEFLATED;archive.writestr(info,b'x'*100)
    expect_rejection(lambda:archive_members(compressed.getvalue(),'Report140'),'ZIP compression');cases.append('ZIP_compression_guard')
    invalid_destination=output/'invalid-extraction'
    expect_rejection(lambda:extract_checked(bad_zip([('Report140/../bad',stat.S_IFREG|0o644)]),invalid_destination),'unsafe extraction')
    require(not invalid_destination.exists(),'invalid extraction created output');cases.append('invalid_ZIP_no_output')
    first=output/'first.zip';write_new(first,raw);extracted=output/'extracted';extract_checked(raw,extracted)
    second=output/'second.zip';invoke(extracted,['pack','--output',str(second)])
    require(read_regular(first)==read_regular(second),'fresh extraction/repack mismatch');cases.append('bounded_extraction_deterministic_repack')
    receipts=[]
    for optimized in (False,True):
        target=output/('replay-'+str(optimized));invoke(clean,['replay','--output',str(target)],optimized=optimized)
        receipts.append(read_regular(target/'replay-result.json'))
    require(receipts[0]==receipts[1],'normal/optimized exact replay mismatch');cases.append('normal_optimized_exact_replay_byte_identical')
    # Run the entire field schema mutation suite under -O independently too.
    process=invoke(clean,['schema-test'],optimized=True)
    require(parse_json(process.stdout)==summary,'optimized schema guard count differs');cases.append('optimized_all_field_mutations')
    result={'status':'PASS','cases':cases,'schema_guards':summary,'case_count':len(cases)}
    write_new(output/'selftest-result.json',json_bytes(result));return result

def reproduce(data, output):
    mkdir(output)
    tests=selftest(data,output/'selftest')
    one=build(data,output/'build-one');two=build(data,output/'build-two')
    require(one['matches_frozen_pdf_bytes'] and two['matches_frozen_pdf_bytes'] and one['pdf_sha256']==two['pdf_sha256'],'fresh PDF bytes differ from each other or frozen PDF')
    result={'status':'PASS','selftest_cases':tests['case_count'],'schema_guards':tests['schema_guards'],'fresh_builds_identical':True,'frozen_pdf_reproduced':True,'pdf_sha256':one['pdf_sha256'],'archive_sha256':digest(read_regular(output/'selftest/first.zip'))}
    write_new(output/'reproduction-result.json',json_bytes(result));return result

def main():
    # sys.argv preserves traversal spellings that Path.__file__ may normalize.
    path_absolute(sys.argv[0]);ancestors(ROOT)
    parser=argparse.ArgumentParser(description='Report140 offline companion; use isolated Python -I')
    sub=parser.add_subparsers(dest='command',required=True)
    sub.add_parser('check');sub.add_parser('schema-test')
    for command in ('replay','selftest','pack','build','seal','reproduce'):
        part=sub.add_parser(command);part.add_argument('--output',required=True)
    args=parser.parse_args();output=output_path(args.output) if hasattr(args,'output') else None
    if args.command=='seal':
        data=inventory(sealing=True);validate_payload(data);write_new(output,json_bytes(make_manifest(data)));print('External manifest written; review before installation');return
    data=verify()
    if args.command=='check':print('PASS: closed inventory, strict schemas, pinned provenance, frozen dependency and SHA256')
    elif args.command=='schema-test':print(json.dumps(schema_selftest(data),sort_keys=True))
    elif args.command=='replay':
        result=replay(data);mkdir(output);write_new(output/'replay-result.json',json_bytes(result));print('PASS: independent finite exact arithmetic replay')
    elif args.command=='pack':print(json.dumps(pack(data,output),sort_keys=True))
    elif args.command=='build':print(json.dumps(build(data,output),sort_keys=True))
    elif args.command=='selftest':print(json.dumps(selftest(data,output),sort_keys=True))
    elif args.command=='reproduce':print(json.dumps(reproduce(data,output),sort_keys=True))

if __name__=='__main__':
    try:main()
    except (Rejected,ValueError,KeyError,TypeError,OSError,RuntimeError,RecursionError,zipfile.BadZipFile,subprocess.CalledProcessError,subprocess.TimeoutExpired) as error:
        print('REJECTED: '+str(error),file=sys.stderr);sys.exit(1)
