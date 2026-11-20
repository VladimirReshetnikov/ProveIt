#!/bin/sh
set -eu
cd "$(dirname "$0")"
lake build
lake env lean Validation.lean
