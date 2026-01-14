#!/bin/bash
# CMI Navier-Stokes Build & Verification Script
# When all checks pass, copies to NavierStokesPaper

CMI_DIR="/home/tracy/development/QFD-Universe/formalization/CMI"
DEST_DIR="/home/tracy/development/GeminiTest3/NavierStokesPaper"

echo "=== CMI Navier-Stokes Build Check ==="
echo ""

# Count sorries
SORRIES=$(grep -rn "sorry" ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null | wc -l)
echo "Sorries found: $SORRIES"

# Count trivials (actual tactic, not Nontrivial type)
TRIVIALS=$(grep -rn "^\s*trivial\s*$\|by\s*trivial\|· trivial" ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null | wc -l)
echo "Trivials found: $TRIVIALS"

# Count axioms
AXIOMS=$(grep -rn "^axiom " ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null | wc -l)
echo "Axioms found: $AXIOMS"

# Count `: True` stubs
STUBS=$(grep -rn ": True :=" ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null | wc -l)
echo "True stubs found: $STUBS"

echo ""
TOTAL=$((SORRIES + TRIVIALS + AXIOMS + STUBS))

if [ $TOTAL -eq 0 ]; then
    echo "✅ ALL CHECKS PASS - Zero sorry/trivial/axiom/stub!"
    echo ""
    echo "Copying to NavierStokesPaper..."
    mkdir -p ${DEST_DIR}
    cp -r ${CMI_DIR}/* ${DEST_DIR}/
    echo "✅ Copied to ${DEST_DIR}"
else
    echo "❌ NOT READY - $TOTAL issues remaining"
    echo ""
    echo "Details:"
    if [ $SORRIES -gt 0 ]; then
        echo "--- Sorries ---"
        grep -rn "sorry" ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null
    fi
    if [ $TRIVIALS -gt 0 ]; then
        echo "--- Trivials ---"
        grep -rn "trivial" ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null | grep -v "^--"
    fi
    if [ $AXIOMS -gt 0 ]; then
        echo "--- Axioms ---"
        grep -rn "^axiom " ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null
    fi
    if [ $STUBS -gt 0 ]; then
        echo "--- True Stubs ---"
        grep -rn ": True :=" ${CMI_DIR}/*.lean ${CMI_DIR}/**/*.lean 2>/dev/null
    fi
fi
