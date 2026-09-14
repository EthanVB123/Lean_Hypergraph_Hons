#!/bin/bash

set -u

# ============================================================
# CONFIGURATION
# ============================================================

REPO_URL="git@github.com:EthanVB123/Lean_Hypergraph_Hons.git"
PROJECT_DIR="$(pwd)"
LOG_DIR="$PROJECT_DIR/benchmark_logs"

mkdir -p "$LOG_DIR"

echo "========================================"
echo "LEAN / MATHLIB BENCHMARK"
echo "========================================"
echo "Date:    $(date)"
echo "Project: $PROJECT_DIR"
echo

# ============================================================
# SYSTEM INFORMATION
# ============================================================

echo "=== System ==="
uname -a
lscpu | grep -E 'Model name|CPU\(s\)'
free -h
df -h .

echo
echo "=== Lean ==="
lean --version
lake --version

# ============================================================
# 1. TRULY FRESH MATHLIB BUILD — 5 RUNS
# ============================================================
#
# Each run:
#   1. Fresh git clone
#   2. No .lake/packages exists
#   3. No compiled mathlib exists
#   4. lake build downloads/builds mathlib
#   5. Temporary clone is deleted
#
# This therefore measures:
#
#   git clone + dependency download + mathlib compilation
#   + project compilation
#
# ============================================================

echo
echo "========================================"
echo "1. TRULY FRESH MATHLIB BUILD — 5 RUNS"
echo "========================================"

for i in {1..5}; do

    echo
    echo "========================================"
    echo "FRESH MATHLIB BUILD — RUN $i / 5"
    echo "========================================"

    FRESH_DIR="/tmp/lean_fresh_run_$i"

    # Make absolutely sure this run starts clean.
    rm -rf "$FRESH_DIR"

    echo
    echo "=== Git clone ==="

    git clone "$REPO_URL" "$FRESH_DIR" \
        2>&1 | tee "$LOG_DIR/fresh_mathlib_clone_${i}.log"

    if [ "${PIPESTATUS[0]}" -ne 0 ]; then
        echo "Git clone failed on run $i"
        exit 1
    fi

    cd "$FRESH_DIR" || exit 1

    echo
    echo "=== Fresh build ==="

    /usr/bin/time -v \
        lake build \
        2>&1 | tee "$LOG_DIR/fresh_mathlib_build_${i}.log"

    BUILD_STATUS=${PIPESTATUS[0]}

    cd "$PROJECT_DIR" || exit 1

    echo
    echo "=== Cleaning temporary clone ==="

    rm -rf "$FRESH_DIR"

    if [ "$BUILD_STATUS" -ne 0 ]; then
        echo "Build failed on fresh mathlib run $i"
        exit "$BUILD_STATUS"
    fi

done


# ============================================================
# 2. FULL PROJECT REBUILD — MATHLIB ALREADY COMPILED — 10 RUNS
# ============================================================
#
# lake clean removes the current project's build products.
#
# The compiled dependency packages remain available, so mathlib
# does not need to be rebuilt.
#
# ============================================================

echo
echo "========================================"
echo "2. FULL PROJECT REBUILD"
echo "MATHLIB ALREADY COMPILED — 10 RUNS"
echo "========================================"

for i in {1..10}; do

    echo
    echo "========================================"
    echo "PROJECT REBUILD — RUN $i / 10"
    echo "========================================"

    lake clean

    /usr/bin/time -v \
        lake build \
        2>&1 | tee "$LOG_DIR/project_rebuild_${i}.log"

    BUILD_STATUS=${PIPESTATUS[0]}

    if [ "$BUILD_STATUS" -ne 0 ]; then
        echo "Project build failed on run $i"
        exit "$BUILD_STATUS"
    fi

done


# ============================================================
# 3. INDIVIDUAL FILE — 10 RUNS
# ============================================================

echo
echo "========================================"
echo "3. INDIVIDUAL FILE — 10 RUNS"
echo "========================================"

for i in {1..10}; do

    echo
    echo "========================================"
    echo "INDIVIDUAL FILE — RUN $i / 10"
    echo "========================================"

    /usr/bin/time -v \
        lake env lean \
        LeanHypergraph2/RandomColourings.lean \
        2>&1 | tee "$LOG_DIR/individual_file_${i}.log"

    BUILD_STATUS=${PIPESTATUS[0]}

    if [ "$BUILD_STATUS" -ne 0 ]; then
        echo "Individual file check failed on run $i"
        exit "$BUILD_STATUS"
    fi

done


# ============================================================
# FINISHED
# ============================================================

echo
echo "========================================"
echo "BENCHMARK COMPLETE"
echo "========================================"
echo
echo "Logs:"
echo "$LOG_DIR"
echo
echo "Fresh mathlib builds:  5"
echo "Project rebuilds:      10"
echo "Individual file runs:  10"
echo "Total timed runs:      25"