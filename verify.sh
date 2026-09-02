#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")"

echo "[1/5] Building the independent kappa_y^8 epsilon^-6 final stack"
lake build \
  BilevelLowerBoundLean.KappaEightPopulationClass \
  BilevelLowerBoundLean.KappaEightSimultaneousCertificates \
  BilevelLowerBoundLean.KappaEightPaperFinalTheorem \
  BilevelLowerBoundLean.KappaEightImportSmokeTest

echo "[2/5] Building the paper-facing and complete kappa-eight audits"
lake build \
  BilevelLowerBoundLean.KappaEightAudit \
  BilevelLowerBoundLean.KappaEightCompleteAudit

echo "[3/5] Auditing the paper-facing declarations and their dependencies"
lake env lean BilevelLowerBoundLean/KappaEightAudit.lean

echo "[4/5] Auditing every theorem loaded from this project's modules"
lake env lean BilevelLowerBoundLean/KappaEightCompleteAudit.lean

echo "[5/5] Scanning all Lean sources for sorry, admit, and custom axioms"
if rg -n \
  '^[[:space:]]*(sorry|admit|axiom)\b|:=[[:space:]]*(by[[:space:]]*)?(sorry|admit)\b' \
  BilevelLowerBoundLean BilevelLowerBoundLean.lean; then
  echo "Placeholder or custom axiom declaration found."
  exit 1
fi

echo "Independent kappa_y^8 epsilon^-6 verification completed successfully."
