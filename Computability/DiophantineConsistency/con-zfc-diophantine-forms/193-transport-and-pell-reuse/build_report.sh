#!/bin/sh
set -eu
report_package_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
python3 "$report_package_dir/report/build_report.py"
