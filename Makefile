.PHONY: all
all:
	@echo "-----------------------"
	@$(MAKE) extract
	@echo "-----------------------"
	@echo "Building the stack project"
	@$(MAKE) --directory=Repl/
	@echo "-----------------------"

.PHONY: extract
extract: 
	@echo "Extracting the Coq Files"
	@$(MAKE) --directory=Formalization/ extract
	@echo "-----------------------"
	@echo "Copying the extracted Files to the Stack project"
	@mkdir -p ./Repl/extracted
	@cp ./Formalization/haskell/*.hs ./Repl/extracted

.PHONY: dist
dist:
	@echo "-----------------------"
	@echo "Creating a tarball"
	@echo "-----------------------"
	@$(MAKE) extract
	@echo "-----------------------"
	rm -rf dist
	mkdir -p dist
	mkdir -p dist/Formalization
	mkdir -p dist/Repl
	mkdir -p dist/Repl/app
	# -------------------------------
	@echo "Copy the Coq formalization into the dist directory..."
	cp Formalization/*.v dist/Formalization
	cp Formalization/Makefile dist/Formalization/Makefile
	cp Formalization/additional_imports.txt dist/Formalization/additional_imports.txt
	cp Formalization/prepend-imports.sh dist/Formalization/prepend-imports.sh
	echo "Copy the Coq formalization into the dist directory..."
	# -------------------------------
	@echo "Copying the toplevel Makefile and README.md"
	cp Makefile dist/Makefile
	cp README.md dist/README.md
	# Copying the files of the Haskell / Repl part
	cp Repl/package.yaml dist/Repl/package.yaml
	cp Repl/stack.yaml dist/Repl/stack.yaml
#	cp Repl/Repl.cabal dist/Repl/Repl.cabal
	cp Repl/package.yaml dist/Repl/package.yaml
	cp Repl/Setup.hs dist/Repl/Setup.hs
	cp Repl/Makefile dist/Repl/Makefile
	cp -r Repl/src dist/Repl/src
	cp -r Repl/test dist/Repl/test
	cp -r Repl/extracted dist/Repl/extracted
	cp Repl/app/* dist/Repl/app/
	@echo "Copying examples to the Repl directory"
	cp Repl/extended-example-1.ub dist/Repl/extended-example-1.ub
	cp Repl/extended-example-2.ub dist/Repl/extended-example-2.ub
	cp Repl/extended-example-3.ub dist/Repl/extended-example-3.ub
	cp Repl/extended-example-4.ub dist/Repl/extended-example-4.ub
	cp Repl/extended-example-5.ub dist/Repl/extended-example-5.ub
	cp Repl/trafficlights.ub dist/Repl/trafficlights.ub
	cp Repl/natprog_nested.ub dist/Repl/natprog_nested.ub
	# Archiving and zipping the dist directory
	tar -cf DataCodata.tar dist/
	rm -rf dist
	@echo "-----------------------"


.PHONY: clean
clean:
	$(MAKE) --directory=Formalization/ clean
	$(MAKE) --directory=Repl/ clean

