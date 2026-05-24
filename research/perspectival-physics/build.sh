#!/usr/bin/env bash
# Reproducible build script for the Perspectival Physics Lean project.
#
# Requires: Lean 4.29.1 (via elan or direct install) and `lake` on PATH.
# Network: needs github.com (Mathlib pull); lakecache.blob.core.windows.net
# for cache acceleration; falls back to full source compile if cache
# is unreachable (slow — ~1-2 hours on 4 cores).

set -euo pipefail

cd "$(dirname "$0")"

echo "==> Checking Lean..."
if ! command -v lean >/dev/null 2>&1; then
  echo "ERROR: lean not on PATH. Install Lean 4.29.1 first."
  echo "  via elan: curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain 4.29.1"
  echo "  or direct: download lean-4.29.1-linux.tar.zst from leanprover/lean4 releases"
  exit 1
fi

echo "==> Lean version:"
lean --version

echo "==> Resolving Mathlib dependency..."
lake update

echo "==> Attempting to fetch Mathlib cache..."
if ! lake exe cache get 2>/dev/null; then
  echo "WARNING: cache fetch failed — will build Mathlib from source."
  echo "         This takes ~1-2 hours on 4 cores."
fi

echo "==> Building Perspectival..."
lake build

echo "==> Build complete."
echo
echo "Modules built:"
ls Perspectival/ | sed 's/^/  /'
echo
echo "To check the verified theorems, see STATUS.md and FINDINGS.md."
