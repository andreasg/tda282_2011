all: runtime bnfc compiler

bnfc:
	bnfc -haskell Javalette.cf
	happy -gca ParJavalette.y
	alex -g LexJavalette.x

compiler:
	ghc --make Jl.hs -o ../jlc

runtime:
	javac Runtime.java
	mv Runtime.class ../lib/Runtime.class
clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocJavalette.ps
	-rm -f ../jlc
	-rm -f ../jlc.exe
distclean: clean
	-rm -f DocJavalette.* LexJavalette.* ParJavalette.* LayoutJavalette.* SkelJavalette.* PrintJavalette.* TestJavalette.* AbsJavalette.* TestJavalette ErrM.* SharedString.* Javalette.dtd XMLJavalette.*

