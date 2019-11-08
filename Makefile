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

.PHONY: clean
clean:
	$(MAKE) --directory=Formalization/ clean
	$(MAKE) --directory=Repl/ clean

