#!/usr/bin/env bash
set -euo pipefail

CC=${CC:-gcc}
CFLAGS="-std=c11 -Wall -Wextra -O2"

SRC="hw3.c"
EXE="./hw3"

echo "[build] $CC $CFLAGS -o assembler $SRC"
$CC $CFLAGS -o assembler "$SRC"

run_ok () {
  local name="$1"
  local in="testinput${name}.tk"
  local inter="testint${name}.tk"
  local out="testout${name}.tko"

  rm -f "$inter" "$out"
  echo "[OK  ] $name"
  if ! $EXE "$in" "$inter" "$out" >/dev/null 2>&1; then
    echo "  expected success, got failure"
    exit 1
  fi
  if [[ ! -s "$inter" ]]; then
    echo "  expected non-empty intermediate, got empty"
    exit 1
  fi
  if [[ ! -s "$out" ]]; then
    echo "  expected non-empty output, got empty"
    exit 1
  fi
}

run_fail () {
  local name="$1"
  local in="testinput${name}.tk"
  local inter="testint${name}.tk"
  local out="testout${name}.tko"

  rm -f "$inter" "$out"
  echo "[FAIL] $name"
  if $EXE "$in" "$inter" "$out" >/dev/null 2>&1; then
    echo "  expected failure, got success"
    exit 1
  fi

  # Optional check: some autograders want intermediate cleared on failure.
  # If you expect intermediate to be empty on failure, enforce it:
  if [[ -f "$inter" && -s "$inter" ]]; then
    echo "  expected empty/cleared intermediate on failure, but it has contents"
    exit 1
  fi
}

# -------------------
# Passing tests
# -------------------
run_ok 1
run_ok 2
run_ok 3

# -------------------
# Failing tests (match your failing categories)
# -------------------
run_fail 4
run_fail 5

echo "All tests passed."