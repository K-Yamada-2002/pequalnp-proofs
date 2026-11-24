#!/usr/bin/env bash
# Run with "lake env bash /path/to/replay.sh" from the upstream lean directory.
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
export LEAN_PATH="$out:${LEAN_PATH:-}"
for mod in LocalPrice SparseFailure UpwardPrice Pencil PencilPrice; do
    lean -j2 --root="$src" -o "$out/$mod.olean" "$src/$mod.lean"
done
cat > "$out/Audit.lean" <<'LEAN'
import PencilPrice
#print axioms PlaneLocalPrice.charged_gate
#print axioms PlaneLocalPrice.sparse_failure
#print axioms PlaneLocalPrice.sound_of_local_cap
#print axioms PlaneLocalPrice.pencil_masks
#print axioms PlaneLocalPrice.pencil_child
LEAN
lean "$out/Audit.lean"
python3 "$src/check_examples.py"
