#!/usr/bin/env bash
set -euo pipefail

# Bootstrap: Paper 3 (Phase7_Density) Lean placeholders
# Usage:
#   ./scripts/bootstrap_paper3.sh /path/to/your/lean/project/root
#
# This script is conservative: it will NOT overwrite existing files.

ROOT="${1:-.}"

mkdir -p "$ROOT/Phase7_Density"
mkdir -p "$ROOT/scripts"

copy_if_missing () {
  local src="$1"
  local dst="$2"
  if [ -f "$dst" ]; then
    echo "[skip] $dst exists"
  else
    echo "[write] $dst"
    cp "$src" "$dst"
  fi
}

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
SRC_ROOT="$(cd "$HERE/.." && pwd)"

copy_if_missing "$SRC_ROOT/Phase7_Density/Interfaces.lean" "$ROOT/Phase7_Density/Interfaces.lean"
copy_if_missing "$SRC_ROOT/Phase7_Density/TopologicalAxioms.lean" "$ROOT/Phase7_Density/TopologicalAxioms.lean"
copy_if_missing "$SRC_ROOT/Phase7_Density/DensitySolitons.lean" "$ROOT/Phase7_Density/DensitySolitons.lean"
copy_if_missing "$SRC_ROOT/Phase7_Density/ApproxToExact.lean" "$ROOT/Phase7_Density/ApproxToExact.lean"
copy_if_missing "$SRC_ROOT/Phase7_Density/FourierLift.lean" "$ROOT/Phase7_Density/FourierLift.lean"
copy_if_missing "$SRC_ROOT/Phase7_Density/ScleronomicLiftTheorem.lean" "$ROOT/Phase7_Density/ScleronomicLiftTheorem.lean"
copy_if_missing "$SRC_ROOT/Phase7_Density/Phase7_Density.lean" "$ROOT/Phase7_Density/Phase7_Density.lean"

echo
echo "Done. Next:"
echo "  1) Add `import Phase7_Density.Phase7_Density` to your master file."
echo "  2) Instantiate `ScleronomicModel` in `Interfaces.lean` with your concrete operators."
