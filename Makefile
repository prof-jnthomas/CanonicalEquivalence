# CanonicalEquivalence Makefile

AGDA_MAIN = CanonicalEquivalence.agda

.PHONY: all check clean

all: check

check:
	@echo "📦 Checking Agda project CanonicalEquivalence..."
	@agda $(AGDA_MAIN)
	@echo "✅ Type-check passed with no errors."

clean:
	@echo "🧹 Cleaning generated .agdai files..."
	@find . -name '*.agdai' -delete
	@echo "✅ Clean complete."
