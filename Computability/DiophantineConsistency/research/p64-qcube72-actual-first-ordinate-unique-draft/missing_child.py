"""Distinguish an exited child from one still live when an RSS sample misses it."""
import subprocess


def finished_or_raise(proc, grace=0.25):
    try:
        return proc.wait(timeout=grace)
    except subprocess.TimeoutExpired as exc:
        raise RuntimeError('live child missing from group RSS sample') from exc
