.PHONY: build doc graph clean

build:
	lake build

doc:
	DOCGEN_SRC="vscode" DISABLE_EQUATIONS=1 lake build Capless:docs

graph:
	lake exe graph dependencies.pdf

clean:
	lake clean
