#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-proof-status.sh — the status-drift gate.
#
# docs/status/PROOF-STATUS.adoc claims numbers; the per-prover MANIFESTs are
# the ground truth check-proofs.sh actually enforces. This script recomputes
# the counts from every MANIFEST and fails if the document disagrees, so the
# status file cannot drift into fiction (the estate's recurring failure mode:
# status docs saying "proved" while nothing was checked).
#
# Contract: for each verification/proofs/<prover>/MANIFEST the document must
# contain the exact line
#
#   // gate:<prover> gated=<N> quarantined=<M>
#
# and must not contain such a line for a prover with no MANIFEST.

set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
DOC="docs/status/PROOF-STATUS.adoc"
[ -f "$DOC" ] || { echo "FAIL: $DOC missing" >&2; exit 1; }

fails=0
found_any=0

for mf in verification/proofs/*/MANIFEST; do
  [ -f "$mf" ] || continue
  found_any=1
  prover="$(basename "$(dirname "$mf")")"
  gated="$(awk -F'|' '$0 !~ /^[[:space:]]*(#|$)/ && $3 == "gated"' "$mf" | wc -l)"
  quar="$(awk -F'|' '$0 !~ /^[[:space:]]*(#|$)/ && $3 == "quarantine"' "$mf" | wc -l)"
  want="// gate:$prover gated=$gated quarantined=$quar"
  if grep -qxF "$want" "$DOC"; then
    echo "OK: $prover — $gated gated, $quar quarantined (document agrees)"
  else
    echo "FAIL: $DOC does not contain the line:"
    echo "        $want"
    echo "      ($mf ground truth: $gated gated, $quar quarantined)"
    fails=$((fails + 1))
  fi
done

# A marker for a prover with no MANIFEST is a stale claim.
while IFS= read -r line; do
  p="$(sed -E 's|^// gate:([A-Za-z0-9_-]+) .*|\1|' <<<"$line")"
  if [ ! -f "verification/proofs/$p/MANIFEST" ]; then
    echo "FAIL: stale marker in $DOC for prover '$p' (no MANIFEST on disk)"
    fails=$((fails + 1))
  fi
done < <(grep -E '^// gate:' "$DOC" || true)

[ "$found_any" -eq 1 ] || echo "note: no MANIFESTs found — only staleness was checked"

if [ "$fails" -gt 0 ]; then
  echo "RESULT: FAIL ($fails drift(s) between PROOF-STATUS.adoc and MANIFEST ground truth)"
  exit 1
fi
echo "RESULT: PASS — PROOF-STATUS.adoc matches MANIFEST ground truth"
