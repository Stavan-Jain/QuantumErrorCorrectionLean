#!/usr/bin/env bash
# Prune stale .ilean / .olean files that prevent the Lean 4 LSP from starting
# after a toolchain bump. Four failure modes are handled:
#
#   0. macOS duplicates: files with " 2" before the extension (e.g.
#      "Foo 2.ilean") created when a write collided with an existing file
#      during parallel extraction. There can be thousands of these.
#   1. Orphan ileans: build artifact has no matching source .lean (module
#      was deleted or renamed upstream).
#   2. Stub ileans: ilean JSON has no "decls" field (deprecation-stub modules
#      cached against a slightly older Lean produce these; new LSP rejects).
#   3. Old-format ileans: reference usage tuples are not length 4 or 5
#      (artifact was produced by an older Lean toolchain — `lake build` will
#      not rebuild because the source hash matches, so the file is stuck
#      unless deleted).
#
# Run this from the project root after every `lean-toolchain` change.
# Safe to run any time — only deletes build artifacts; never touches sources.

set -euo pipefail

cd "$(dirname "$0")/.."

declare -a SCAN_ROOTS=(
  ".lake/build"
  ".lake/packages/mathlib/.lake/build"
)

PKG_MATHLIB="$(pwd)/.lake/packages/mathlib"

remove_stem() {
  local stem="$1" ir_stem="$2"
  rm -f "$stem".ilean "$stem".ilean.hash \
        "$stem".olean "$stem".olean.hash \
        "$stem".olean.private "$stem".olean.private.hash \
        "$stem".olean.server "$stem".olean.server.hash \
        "$stem".ir "$stem".ir.hash "$stem".trace
  rm -f "$ir_stem".c "$ir_stem".c.hash "$ir_stem".setup.json
}

# Pick the source root that corresponds to a build root.
src_root_for() {
  case "$1" in
    .lake/build)                                    echo "." ;;
    .lake/packages/mathlib/.lake/build)             echo "$PKG_MATHLIB" ;;
    *)                                              echo "" ;;
  esac
}

total=0

# Phase 0: macOS-style duplicate files ("Foo 2.ilean", "Foo 2.olean", etc.)
# These are pure junk — no real source ever has " 2" in its name.
echo "Phase 0: removing macOS-style duplicates..."
phase0=0
for BLD in "${SCAN_ROOTS[@]}"; do
  [ -d "$BLD" ] || continue
  while IFS= read -r f; do
    rm -f "$f"
    phase0=$((phase0 + 1))
  done < <(find "$BLD" -name "* 2.*" -type f 2>/dev/null)
done
echo "  removed $phase0 duplicate(s)"
total=$((total + phase0))

for BLD in "${SCAN_ROOTS[@]}"; do
  [ -d "$BLD/lib/lean" ] || continue
  SRC_ROOT="$(src_root_for "$BLD")"

  while IFS= read -r f; do
    rel="${f#$BLD/lib/lean/}"
    src="$SRC_ROOT/${rel%.ilean}.lean"
    stem="${f%.ilean}"
    ir_stem="$BLD/ir/${rel%.ilean}"

    reason=""

    # (1) Orphan: source file no longer exists.
    if [ ! -f "$src" ]; then
      reason="orphan"
    # (2) Stub: no "decls" field.
    elif ! grep -q '"decls"' "$f"; then
      reason="stub"
    # (3) Old-format: reference usages of length != {4,5}.
    elif python3 - "$f" <<'PY' >/dev/null 2>&1; then :
import json, sys
d = json.load(open(sys.argv[1]))
for v in d.get("references", {}).values():
    for u in v.get("usages", []):
        if len(u) not in (4, 5):
            sys.exit(0)
sys.exit(1)
PY
      reason="old-format"
    fi

    if [ -n "$reason" ]; then
      remove_stem "$stem" "$ir_stem"
      echo "[$reason] $rel"
      total=$((total + 1))
    fi
  done < <(find "$BLD/lib/lean" -name "*.ilean" 2>/dev/null)
done

echo "---"
echo "Pruned $total stale ilean(s)."
