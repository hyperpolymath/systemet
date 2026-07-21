#!/bin/bash
# SPDX-License-Identifier: MPL-2.0
# Copyright (c) 2026 Jonathan D.A. Jewell (hyperpolymath) <j.d.a.jewell@open.ac.uk>
#
# RSR Template Validation Script
# Verifies that a repository follows the RSR template structure and contains all required files
#
# Exit codes:
#   0 = validation passed
#   1 = validation failed with errors
#   2 = validation failed with warnings (but can proceed)

set -euo pipefail

REPO_ROOT="${1:-.}"
VERBOSE="${2:-0}"
ERRORS=0
WARNINGS=0

# ANSI colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Helper functions
log_error() {
    echo -e "${RED}ERROR${NC}: $*" >&2
    ERRORS=$((ERRORS + 1))
}

log_warning() {
    echo -e "${YELLOW}WARN${NC}: $*" >&2
    WARNINGS=$((WARNINGS + 1))
}

log_info() {
    echo -e "${BLUE}INFO${NC}: $*" >&2
}

log_pass() {
    echo -e "${GREEN}PASS${NC}: $*" >&2
}

check_file_exists() {
    local file="$1"
    local description="${2:-}"
    if [ -f "$REPO_ROOT/$file" ]; then
        [ "$VERBOSE" = "1" ] && log_pass "File exists: $file"
        return 0
    else
        log_error "Required file missing: $file ${description:+(${description})}"
        return 1
    fi
}

check_dir_exists() {
    local dir="$1"
    local description="${2:-}"
    if [ -d "$REPO_ROOT/$dir" ]; then
        [ "$VERBOSE" = "1" ] && log_pass "Directory exists: $dir"
        return 0
    else
        log_error "Required directory missing: $dir ${description:+(${description})}"
        return 1
    fi
}

# systemet IS-NOT check: this is a theory repo — no runnable code lives here
# (see CLAUDE.md / EXPLAINME "Boundary"). The template's ABI/FFI seam was
# removed; its reappearance is drift, so absence is ENFORCED, not tolerated.
check_absent() {
    local path="$1"
    local description="${2:-}"
    if [ -e "$REPO_ROOT/$path" ]; then
        log_error "IS-NOT violation: $path exists ${description:+(${description})}"
        return 1
    fi
    [ "$VERBOSE" = "1" ] && log_pass "Correctly absent: $path"
    return 0
}

has_spdx_header() {
    local file="$1"
    if head -10 "$file" | grep -q "SPDX-License-Identifier"; then
        return 0
    fi
    return 1
}

has_placeholder() {
    local file="$1"
    if grep -q "{{REPO\|{{OWNER\|{{FORGE\|{{PROJECT\|{{project\|{{AUTHOR" "$file" 2>/dev/null; then
        return 0
    fi
    return 1
}

#==============================================================================
# VALIDATION PHASE 1: CORE STRUCTURE
#==============================================================================

echo ""
log_info "Phase 1: Core repository structure"
echo ""

# Root files
check_file_exists "0-AI-MANIFEST.a2ml" "AI manifest (universal entry point)"
check_file_exists "README.adoc" "High-level pitch"
check_file_exists "EXPLAINME.adoc" "Developer deep-dive"
check_file_exists "LICENSE" "License file"
check_file_exists "Justfile" "Task runner"
check_file_exists "AUDIT.adoc" "Release audit gate"

# Directories
check_dir_exists ".machine_readable" "Machine-readable metadata"
check_dir_exists ".github" "GitHub community metadata"
check_dir_exists "docs" "Documentation"
check_dir_exists "docs/theory" "The theory spec (systemet's actual content)"

#==============================================================================
# VALIDATION PHASE 2: MACHINE-READABLE METADATA
#==============================================================================

echo ""
log_info "Phase 2: Machine-readable metadata (.machine_readable/)"
echo ""

check_file_exists ".machine_readable/6a2/STATE.a2ml" "Project state"
check_file_exists ".machine_readable/6a2/META.a2ml" "Architecture decisions"
check_file_exists ".machine_readable/6a2/ECOSYSTEM.a2ml" "Ecosystem position"
check_file_exists ".machine_readable/6a2/anchors/ANCHOR.a2ml" "Semantic boundary anchor"
check_file_exists ".machine_readable/policies/MAINTENANCE-AXES.a2ml" "Maintenance axes"

#==============================================================================
# VALIDATION PHASE 3: REQUIRED WORKFLOWS (17 minimum)
#==============================================================================

echo ""
log_info "Phase 3: GitHub Actions workflows"
echo ""

REQUIRED_WORKFLOWS=(
    "hypatia-scan.yml"
    "codeql.yml"
    "scorecard.yml"
    "quality.yml"
    "mirror.yml"
    "instant-sync.yml"
    "guix-policy.yml"
    "security-policy.yml"
    "wellknown-enforcement.yml"
    "workflow-linter.yml"
    "npm-bun-blocker.yml"
    "ts-blocker.yml"
    "secret-scanner.yml"
)

# Check required workflows
for workflow in "${REQUIRED_WORKFLOWS[@]}"; do
    if [ -f "$REPO_ROOT/.github/workflows/$workflow" ]; then
        [ "$VERBOSE" = "1" ] && log_pass "Workflow found: $workflow"
    else
        log_error "Required workflow missing: $workflow"
    fi
done

# Verify all workflows have SPDX headers and proper structure
WORKFLOW_FILES=$(find "$REPO_ROOT/.github/workflows" -name "*.yml" -type f 2>/dev/null || true)
WORKFLOW_COUNT=$(echo "$WORKFLOW_FILES" | grep -c "." || true)

if [ "$WORKFLOW_COUNT" -ge 15 ]; then
    log_pass "Found $WORKFLOW_COUNT workflows (>= 15 expected)"
else
    log_warning "Found only $WORKFLOW_COUNT workflows (expected >= 15)"
fi

# Spot-check workflow files for issues
while IFS= read -r workflow_file; do
    if [ -z "$workflow_file" ]; then continue; fi

    # Check for SPDX header (optional in YAML workflows, but best practice)
    if ! head -5 "$workflow_file" | grep -q "SPDX-License-Identifier"; then
        log_warning "Workflow missing SPDX header: $(basename "$workflow_file")"
    fi

    # Check for proper YAML structure
    if ! grep -q "^name:" "$workflow_file"; then
        log_error "Workflow missing 'name' field: $(basename "$workflow_file")"
    fi
done <<< "$WORKFLOW_FILES"

#==============================================================================
# VALIDATION PHASE 4: THEORY-REPO SHAPE (IS-NOT ENFORCEMENT)
#==============================================================================

echo ""
log_info "Phase 4: theory-repo shape — no runnable code (IS-NOT)"
echo ""

# systemet is the theory; the template's ABI/FFI seam does not belong here.
check_absent "src" "theory repo: no runnable code — kernel lives in anytype"
check_absent "abi.ipkg" "removed with the ABI seam"

# The theory spec + obligation ledger must exist.
check_file_exists "docs/theory/OBLIGATIONS.adoc" "ET obligation ledger"
check_file_exists "docs/theory/README.adoc" "theory index"

#==============================================================================
# VALIDATION PHASE 5: PLACEHOLDER TOKENS
#==============================================================================

echo ""
log_info "Phase 5: Placeholder token replacement (skipped in template repo)"
echo ""

# Note: Template repo is allowed to have placeholders
# For derived repos, we'd check that placeholders are replaced
if [ "$(basename "$REPO_ROOT")" = "rsr-template-repo" ]; then
    log_pass "Skipping placeholder check for template repo"
else
    # Check that key files don't have unresolved placeholders
    for file in "$REPO_ROOT/README.adoc" "$REPO_ROOT/Justfile" "$REPO_ROOT/.machine_readable/6a2/STATE.a2ml"; do
        if [ -f "$file" ]; then
            if has_placeholder "$file"; then
                log_warning "File contains unresolved placeholders: $(basename "$file")"
            fi
        fi
    done
fi

#==============================================================================
# VALIDATION PHASE 6: SPDX LICENSE HEADERS
#==============================================================================

echo ""
log_info "Phase 6: SPDX License Headers"
echo ""

# Check code-bearing files for SPDX headers (scripts + proof developments;
# there is no src/ in this theory repo)
SOURCE_FILES=$(find "$REPO_ROOT/scripts" "$REPO_ROOT/verification" -type f \
              \( -name "*.sh" -o -name "*.lean" -o -name "*.idr" -o -name "*.agda" -o -name "*.v" \) \
              2>/dev/null || true)
SOURCE_COUNT=$(echo "$SOURCE_FILES" | grep -c "." || true)
SPDX_COUNT=0

while IFS= read -r src_file; do
    if [ -z "$src_file" ]; then continue; fi
    if has_spdx_header "$src_file"; then
        SPDX_COUNT=$((SPDX_COUNT + 1))
    else
        log_warning "Source file missing SPDX header: $(basename "$src_file")"
    fi
done <<< "$SOURCE_FILES"

if [ "$SOURCE_COUNT" -gt 0 ]; then
    PERCENT=$((SPDX_COUNT * 100 / SOURCE_COUNT))
    log_pass "SPDX headers: $SPDX_COUNT/$SOURCE_COUNT ($PERCENT%)"
    if [ "$PERCENT" -lt 100 ]; then
        log_warning "Not all source files have SPDX headers"
    fi
fi

#==============================================================================
# VALIDATION PHASE 7: BUILD VERIFICATION
#==============================================================================

echo ""
log_info "Phase 7: Build system verification"
echo ""

# There is no build system in a theory repo. The one verifiable artefact
# class is the proof developments; those are gated by scripts/check-proofs.sh
# (prover-absent = FAIL), not here. Defer, and say so.
if [ -f "$REPO_ROOT/scripts/check-proofs.sh" ]; then
    log_pass "Proof gate present (scripts/check-proofs.sh) — run it separately"
else
    log_warning "scripts/check-proofs.sh not present yet (lands with the mechanization PR)"
fi

#==============================================================================
# VALIDATION PHASE 8: DOCUMENTATION
#==============================================================================

echo ""
log_info "Phase 8: Documentation requirements"
echo ""

# TOPOLOGY may live at root or under docs/architecture/, .md or .adoc
if [ -f "$REPO_ROOT/TOPOLOGY.adoc" ] || [ -f "$REPO_ROOT/TOPOLOGY.md" ] || \
   [ -f "$REPO_ROOT/docs/architecture/TOPOLOGY.adoc" ] || [ -f "$REPO_ROOT/docs/architecture/TOPOLOGY.md" ]; then
    [ "$VERBOSE" = "1" ] && log_pass "Architecture topology found"
else
    log_error "Required file missing: TOPOLOGY (root or docs/architecture/, .adoc or .md)"
fi
# CONTRIBUTING.md may live at root or in .github/ (GitHub auto-discovers either)
if [ -f "$REPO_ROOT/CONTRIBUTING.md" ] || [ -f "$REPO_ROOT/.github/CONTRIBUTING.md" ]; then
    [ "$VERBOSE" = "1" ] && log_pass "Contribution guide found"
else
    log_error "Required file missing: CONTRIBUTING.md (root or .github/)"
fi

# Governance can be at root or in docs/governance/
if [ -f "$REPO_ROOT/GOVERNANCE.adoc" ] || [ -f "$REPO_ROOT/GOVERNANCE.md" ] || [ -d "$REPO_ROOT/docs/governance" ]; then
    [ "$VERBOSE" = "1" ] && log_pass "Governance files found"
else
    log_warning "Governance documentation not found"
fi

#==============================================================================
# VALIDATION SUMMARY
#==============================================================================

echo ""
echo "═══════════════════════════════════════════════════════════════════════════════"
echo "VALIDATION SUMMARY"
echo "═══════════════════════════════════════════════════════════════════════════════"
echo ""
echo -e "Errors:   ${RED}${ERRORS}${NC}"
echo -e "Warnings: ${YELLOW}${WARNINGS}${NC}"
echo ""

if [ "$ERRORS" -eq 0 ]; then
    echo -e "${GREEN}✓ Validation PASSED${NC}"
    [ "$WARNINGS" -gt 0 ] && echo -e "  (with $WARNINGS warnings)"
    exit 0
else
    echo -e "${RED}✗ Validation FAILED${NC}"
    echo "  Please fix the errors above."
    exit 1
fi
