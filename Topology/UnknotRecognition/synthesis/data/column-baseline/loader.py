"""Load the retained pre-column native path without mutating current modules."""
import importlib.util
from pathlib import Path
import sys


def load():
    here = Path(__file__).parent
    modules = {}
    for name in ('core_handlebody', 'core_handlebody_verify', 'bundle_boundary_kernel',
                 'bundle_boundary_kernel_verify', 'normal_cut_handlebodies',
                 'normal_cut_handlebodies_verify'):
        qualified = 'fastunknot._column_baseline_' + name
        spec = importlib.util.spec_from_file_location(qualified, here/(name+'.py'))
        module = importlib.util.module_from_spec(spec)
        sys.modules[qualified] = module
        spec.loader.exec_module(module)
        modules[name] = module
    core, kernel = modules['core_handlebody'], modules['bundle_boundary_kernel']
    for name in ('_forest', '_occurrences', 'capped_cancellation_plan', 'leaf_cancellation_plan'):
        setattr(kernel, name, getattr(core, name))
    consumer = modules['normal_cut_handlebodies']
    consumer.core_handlebody_certificate = core.core_handlebody_certificate
    consumer.bundle_boundary_kernel = kernel.bundle_boundary_kernel
    verifier = modules['normal_cut_handlebodies_verify']
    verifier.verify_core_handlebody_certificate = modules['core_handlebody_verify'].verify_core_handlebody_certificate
    verifier.replay_bundle_boundary_kernel = modules['bundle_boundary_kernel_verify'].replay_bundle_boundary_kernel
    return modules
