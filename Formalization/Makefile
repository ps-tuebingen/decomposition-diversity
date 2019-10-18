# The coq compiler
CC = coqc
# Compiler Flags
COQFLAGS =
# Flags for Coqdep
COQDEPFLAGS = -noglob
# Coq dependency resolver
COQDEP = coqdep
# Coq documentation
COQDOC = coqdoc
# Options for coqdoc
COQDOCOPTIONS = --html -d docs -g --multi-index
# Contains all files ending in .v of the current directory
SRC = $(wildcard *.v)
# SRC with %.v replaced by %.d and %.vo, respectively.
DEP = $(SRC:.v=.d)
OBJ = $(SRC:.v=.vo)

# The default target
all: Eval.vo Progress.vo Preservation.vo LiftMatch.vo LiftComatch.vo InlineLiftMatch.vo InlineComatch.vo CtorizeIII.vo DtorizeIII.vo XfuncSubst.vo XfuncInverse.vo TypecheckProgram.vo Sublists.vo DtorizeIV.vo CtorizeIV.vo ProgramEquivalence.vo Results.vo

%.d: %.v
	$(COQDEP) $(COQDEPFLAGS) $*.v | head -n1 | sed 's/\s*[a-zA-Z]*\.v\.beautified//g' > $*.d


-include $(DEP)

%.vo: %.v
	$(CC) $(COQFLAGS) $*.v

# Delete all .vo and .glob files
.PHONY: clean
clean: cleandep
	@find . -name "*.vo" -type f -delete
	@find . -name "*.glob" -type f -delete
	@find . -name "*.v.d" -type f -delete
	@find . -name "*.hs" -type f -delete
	@echo "Deleted all files with extensions .v .glob .v.d and .hs"

# Clean all .d files
.PHONY: cleandep
cleandep:
	@find . -name "*.d" -type f -delete
	@echo "Deleted all *.d dependency files"

.PHONY: tags
tags:
	@coqtags *.v
	@echo "Created Tags file"

# Create HTML Documentation in folder /docs
docs: all
	@mkdir -p docs
	@$(COQDOC) $(COQDOCOPTIONS) $(SRC)
	@echo "Created documentation in subdirectory ./docs"

# Print the dependency graph for a given file
%.dot: %.v
	$(COQDEP) -dumpgraph $*.dot $*.v
%.png: %.dot
	dot -Tpng $*.dot > $*.png

# Extract Haskell Files in subdirectory "haskell/"
extract: Extraction.vo
	@mkdir -p haskell
	@find . -name "*.hs" -type f -delete
	@echo "Delete the old extracted files"
	@$(CC) $(COQFLAGS) Extraction.v
	@echo "Prepend necessary imports to .hs files."
	@sh ./prepend-imports.sh
	@mv *.hs ./haskell
	@echo "Extracted Haskell Code and moved to subdirectory ./haskell"

Readme.pdf : README.md
	pandoc --from markdown -o Readme.pdf README.md

.PHONY: dist
dist:
	@echo "-----------------------"
	@echo "Creating a tarball with Coq Sources"
	@echo "-----------------------"
	# Creating a fresh dist directory
	rm -rf dist
	mkdir -p dist
	# Copying the files of the Coq part
	cp *.v dist
	cp Makefile dist/Makefile
	# Compiling the Readme.pdf for the formalization
	# $(MAKE) Readme.pdf
	# cp Readme.pdf dist/
	# Zipping the contents of the directory
	tar -cf archive.tar dist/
	# Removing the dist directory
	rm -rf dist
	@echo "-----------------------"
