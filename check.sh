#!/usr/bin/env bash
set -e

echo "📦 Checking Agda project CanonicalEquivalence..."
agda CanonicalEquivalence.agda
echo "✅ Type-check passed with no errors."
