#!/usr/bin/env bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# check-proofs.sh <prover>            prover in: idris2 | lean4 | agda | coq
#
# The single source of truth for "do the <prover> proofs in this repo compile?".
# build/just/proofs.just calls this (`just proof-check-<prover>`), and CI should
# too, so a green local run and a green CI run mean the same thing.
#
# It replaces four separate "checks that could not fail" that let non-compiling
# proofs sit in estate repos for months while every status file said "proved":
#
#   1. `command -v <prover> || { echo SKIP; exit 0; }` — a MISSING TOOLCHAIN
#      reported success.  A gate that cannot run must never report OK: it
#      manufactures false confidence, which is worse than having no gate.
#   2. `<prover> --check <full/path/To/Mod>` — Idris2 (and friends) derive the
#      expected module name from the path they are handed, so a module checked
#      from the wrong directory fails on a name mismatch rather than its real
#      errors, and verdicts invert.  Every module here is checked from its own
#      SOURCE ROOT (declared in the MANIFEST).
#   3. Path-filtered CI that only looked at one directory — nothing checked the
#      rest.  Here, a proof file present on disk but absent from the MANIFEST is
#      an ERROR, so new proofs are gated by default, not by remembering.
#   4. `idris2 --check X && ok` — `idris2 --check` EXITS 0 ON A MISSING IMPORT
#      (verified against 0.7.0) while printing `Error: ...`.  Testing the exit
#      code alone is unsound; for idris2 we require exit 0 AND no `Error:` line.
#
# They share one shape: a null check that emits reassuring text.  If you extend
# this script, the test to apply is not "does it pass?" but "have I watched it
# fail?".
#
# CONVENTION: proofs live under verification/proofs/<prover>/ ; the MANIFEST for
# a prover is verification/proofs/<prover>/MANIFEST, one entry per line:
#
#   <source-root>|<module-path-relative-to-source-root>|gated|quarantine|<note>
#
#     source-root : directory the prover is invoked from, chosen so the module's
#                   declared name matches its path (getting this wrong is hole #2).
#     gated       : MUST compile.  A failure fails this script and CI.
#     quarantine  : known-broken, tracked in STATE.a2ml.  Must CONTINUE to fail;
#                   if one starts compiling the script fails and tells you to
#                   promote it, so the list cannot rot into a permanent excuse.
#
# Blank lines and lines starting with # are ignored.
#
# Exit: 0 = every gated module compiles AND every quarantined module still fails
#           AND every proof file on disk is listed; 1 = otherwise; 2 = misuse.

set -euo pipefail

PROVER="${1:-}"
case "$PROVER" in
  idris2|lean4|agda|coq) ;;
  *) echo "usage: $(basename "$0") <idris2|lean4|agda|coq>" >&2; exit 2 ;;
esac

# This script lives in <repo-root>/scripts/ ; run everything from the repo root.
cd "$(dirname "${BASH_SOURCE[0]}")/.."
ROOT="$PWD"
PROOF_DIR="verification/proofs/$PROVER"
MANIFEST_FILE="$PROOF_DIR/MANIFEST"

# --- per-prover configuration -------------------------------------------------
# CMD      : executable that must be on PATH (absent => FAIL, never skip).
# EXT      : file extension, for the "unlisted proof" coverage scan.
# ERROR_RE : if non-empty, output must not match it even when the exit code is 0.
#            Only idris2 needs this (its --check exits 0 on a missing import);
#            for lean4 it is a harmless belt-and-braces guard.
case "$PROVER" in
  idris2) CMD=idris2; EXT=idr;  ERROR_RE='^Error:' ;;
  lean4)  CMD=lean;   EXT=lean; ERROR_RE='error:'  ;;
  agda)   CMD=agda;   EXT=agda; ERROR_RE=''        ;;
  coq)    CMD=coqc;   EXT=v;    ERROR_RE=''        ;;
esac

check_one() {
  # $1 source-root (rel to ROOT), $2 module (rel to source-root).
  # Sets LAST_OUT to the tool output on failure; returns 0 iff the module compiles.
  local root="$1" rel="$2" out rc
  set +e
  case "$PROVER" in
    idris2) out="$(cd "$ROOT/$root" && idris2 --check "$rel" 2>&1)"; rc=$? ;;
    lean4)
      # In a lake package, per-file `lake env lean` fails on a fresh checkout
      # (imports have no .olean yet), so build the module by name instead —
      # `lake build Systemet.L1.Normal` compiles its dependency closure and
      # exits non-zero on any error. Bare lean covers standalone files.
      if [ -f "$ROOT/$root/lakefile.toml" ] || [ -f "$ROOT/$root/lakefile.lean" ]; then
        local mod; mod="${rel%.lean}"; mod="${mod//\//.}"
        out="$(cd "$ROOT/$root" && lake build "$mod" 2>&1)"; rc=$?
      else
        out="$(cd "$ROOT/$root" && lean "$rel" 2>&1)"; rc=$?
      fi ;;
    agda)   out="$(cd "$ROOT/$root" && agda --safe    "$rel" 2>&1)"; rc=$? ;;
    coq)    out="$(cd "$ROOT/$root" && coqc           "$rel" 2>&1)"; rc=$? ;;
  esac
  set -e
  if [ "$rc" -eq 0 ] && { [ -z "$ERROR_RE" ] || ! grep -qE "$ERROR_RE" <<<"$out"; }; then
    LAST_OUT=""; return 0
  fi
  LAST_OUT="$out"; return 1
}

echo "=== $PROVER proof check ==="

# --- toolchain: absent means FAIL, never skip ---------------------------------
if ! command -v "$CMD" >/dev/null 2>&1; then
  {
    echo "FAIL: '$CMD' not found on PATH."
    echo
    echo "This is deliberately fatal.  The previous recipe did 'exit 0' here with"
    echo "\"SKIP: $CMD not installed\", so every $PROVER proof reported green on any"
    echo "machine that could not check it.  Install the $PROVER toolchain, or run"
    echo "this in CI where the workflow installs it."
  } >&2
  exit 1
fi
"$CMD" --version 2>/dev/null | head -1 || true
echo

# --- a repo with proofs but no MANIFEST is itself a failure -------------------
if [ ! -f "$MANIFEST_FILE" ]; then
  if [ -d "$PROOF_DIR" ] && [ -n "$(find "$PROOF_DIR" -name "*.$EXT" 2>/dev/null)" ]; then
    echo "FAIL: $PROOF_DIR contains .$EXT proofs but has no MANIFEST." >&2
    echo "      Create $MANIFEST_FILE listing each as 'gated' or 'quarantine'." >&2
    exit 1
  fi
  echo "no $PROOF_DIR/*.$EXT proofs and no MANIFEST — nothing to check."
  exit 0
fi

fails=0
unexpected_pass=0
listed_tmp="$(mktemp)"
trap 'rm -f "$listed_tmp"' EXIT

while IFS='|' read -r root rel status note; do
  # skip blank lines and comments
  [ -z "${root// }" ] && continue
  case "${root#"${root%%[![:space:]]*}"}" in \#*) continue ;; esac
  printf '  %-30s %-24s ' "$root" "$rel"
  echo "$root/$rel" >>"$listed_tmp"
  if check_one "$root" "$rel"; then
    if [ "$status" = gated ]; then
      echo "PASS"
    else
      echo "PASS -- UNEXPECTED (quarantined module now compiles)"
      echo "        Promote '$rel' to 'gated' in $MANIFEST_FILE and update STATE.a2ml."
      unexpected_pass=$((unexpected_pass + 1))
    fi
  else
    if [ "$status" = gated ]; then
      echo "FAIL"
      printf '%s\n' "${LAST_OUT//$'\n'/$'\n        '}" | sed '1s/^/        /'
      fails=$((fails + 1))
    else
      echo "fail (quarantined, expected)"
      [ -n "${note// }" ] && echo "        reason:$note"
    fi
  fi
done < "$MANIFEST_FILE"

# --- coverage: every proof on disk must be listed -----------------------------
# The anti-recurrence rule: proofs went unchecked for months because nothing
# forced them onto anyone's list.  A file absent from the MANIFEST is an error.
echo
echo "=== manifest coverage ($PROOF_DIR) ==="
listed="$(sort -u "$listed_tmp")"
found="$(cd "$ROOT" && find "$PROOF_DIR" -name "*.$EXT" -not -path '*/build/*' -not -path '*/.lake/*' 2>/dev/null | sort)"
unlisted="$(comm -13 <(printf '%s\n' "$listed") <(printf '%s\n' "$found") || true)"
missing="$(comm -23 <(printf '%s\n' "$listed") <(printf '%s\n' "$found") || true)"

if [ -n "${unlisted//[[:space:]]/}" ]; then
  echo "FAIL: .$EXT proofs on disk but absent from $MANIFEST_FILE:"
  printf '  %s\n' $unlisted
  echo "      List each as 'gated' or 'quarantine'; new proofs are gated by default."
  fails=$((fails + 1))
fi
if [ -n "${missing//[[:space:]]/}" ]; then
  echo "FAIL: MANIFEST lists modules that do not exist (stale entries):"
  printf '  %s\n' $missing
  fails=$((fails + 1))
fi
[ -z "${unlisted//[[:space:]]/}${missing//[[:space:]]/}" ] && \
  echo "  all $(printf '%s\n' "$found" | grep -c .) .$EXT file(s) accounted for"

# --- lean4 lake package: whole-package build + transitive axiom audit ---------
# Per-file checks above prove each MANIFESTed module elaborates, but only a
# package build proves the import graph is complete, and only `#print axioms`
# proves no theorem depends on sorryAx/an axiom smuggled in transitively.
if [ "$PROVER" = lean4 ] && { [ -f "$PROOF_DIR/lakefile.toml" ] || [ -f "$PROOF_DIR/lakefile.lean" ]; }; then
  echo
  echo "=== lake build ($PROOF_DIR) ==="
  set +e
  build_out="$(cd "$ROOT/$PROOF_DIR" && lake build 2>&1)"; build_rc=$?
  set -e
  printf '%s\n' "$build_out" | tail -5
  if [ "$build_rc" -ne 0 ] || grep -qE "declaration uses 'sorry'|error:" <<<"$build_out"; then
    echo "FAIL: lake build failed or reported sorry/errors"
    fails=$((fails + 1))
  fi

  AUDIT_FILE="$PROOF_DIR/Systemet/Audit.lean"
  if [ -f "$AUDIT_FILE" ]; then
    echo
    echo "=== axiom audit (Systemet/Audit.lean) ==="
    set +e
    audit_out="$(cd "$ROOT/$PROOF_DIR" && lake env lean Systemet/Audit.lean 2>&1)"; audit_rc=$?
    set -e
    printf '%s\n' "$audit_out" | sed 's/^/  /'
    # The trusted base is exactly Lean's three core axioms (propext,
    # Classical.choice, Quot.sound) — they enter via omega/simp/WF recursion
    # and are sound. ANYTHING else (sorryAx, a user `axiom`) fails: a stub
    # axiom compiles green, so "builds" must never be read as "proved".
    expected="$(grep -c '^#print axioms' "$ROOT/$AUDIT_FILE" || true)"
    ok=0; bad=0
    while IFS= read -r line; do
      case "$line" in
        *"does not depend on any axioms"*) ok=$((ok + 1)) ;;
        *"depends on axioms:"*)
          axlist="${line#*depends on axioms: [}"; axlist="${axlist%%]*}"
          rest="$(tr ',' '\n' <<<"$axlist" | sed 's/^ *//; s/ *$//' \
                    | grep -vE '^(propext|Classical\.choice|Quot\.sound)$' || true)"
          if [ -n "${rest//[[:space:]]/}" ]; then
            bad=$((bad + 1))
            echo "  DISALLOWED axiom(s) beyond the trusted base: $rest"
          else
            ok=$((ok + 1))
          fi ;;
      esac
    done <<<"$audit_out"
    if [ "$audit_rc" -ne 0 ] || grep -q 'sorryAx' <<<"$audit_out" || [ "$bad" -ne 0 ] || [ "$ok" -ne "$expected" ]; then
      echo "FAIL: axiom audit — $ok/$expected item(s) within the trusted base, $bad with disallowed axioms$(grep -q sorryAx <<<"$audit_out" && echo '; sorryAx PRESENT')"
      fails=$((fails + 1))
    else
      echo "  audit: $ok/$expected headline items within the trusted base (no sorryAx, no user axioms)"
    fi
  else
    echo
    echo "FAIL: lake package present but Systemet/Audit.lean missing — the axiom audit is mandatory"
    fails=$((fails + 1))
  fi
fi

echo
if [ "$fails" -gt 0 ] || [ "$unexpected_pass" -gt 0 ]; then
  echo "RESULT: FAIL ($fails failure(s), $unexpected_pass unexpected pass(es))"
  exit 1
fi
echo "RESULT: PASS -- gated modules compile; quarantined modules still fail as recorded"
