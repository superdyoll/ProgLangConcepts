# 
# Rules for compiling and linking the typechecker/evaluator
#
# Type
#   make         to rebuild the executable file c
#   make clean   to remove all intermediate and temporary files
#   make depend  to rebuild the intermodule dependency graph that is used
#                  by make to determine which order to schedule 
#	           compilations.  You should not need to do this unless
#                  you add new modules or new dependencies between 
#                  existing modules.  (The graph is stored in the file
#                  .depend)

# These are the object files needed to rebuild the main executable file
#
OBJS = parser.cmo lexer.cmo River.cmo main.cmo

COMMONOBJS = str.cma

# Files that need to be generated from other files
DEPEND += lexer.ml parser.ml  

# When "make" is invoked with no arguments, we build an executable 
# typechecker, after building everything that it depends on
all: $(DEPEND) $(OBJS) mysplinterpreter

# Include an automatically generated list of dependencies between source files
include .depend


# Build an executable typechecker
mysplinterpreter: $(OBJS) main.cmo 
	@echo Linking $@
	ocamlc -g -o $@ $(COMMONOBJS) $(OBJS) 

# Compile an ML module interface
%.cmi : %.mli
	ocamlc -c -g $<

# Compile an ML module implementation
%.cmo : %.ml
	ocamlc -c -g $<

# Generate ML files from a parser definition file
parser.ml parser.mli: parser.mly
	@rm -f parser.ml parser.mli
	ocamlyacc -v parser.mly
	@chmod -w parser.ml parser.mli

# Generate ML files from a lexer definition file
%.ml %.mli: %.mll
	@rm -f $@
	ocamllex $<
	@chmod -w $@

# Clean up the directory
clean::
	rm -rf lexer.ml parser.ml parser.mli *.o *.cmo *.cmi parser.output \
	   c TAGS *~ 

# Rebuild intermodule dependencies
depend:: $(DEPEND) 
	ocamldep $(INCLUDE) *.mli *.ml > .depend

# 
test::
	bash test.sh
