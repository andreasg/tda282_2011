all: bnfc runtime jlc

bnfc:
	bnfc -haskell Javalette.cf
	happy -gca ParJavalette.y
	alex -g LexJavalette.x

jlc:
	ghc --make Jl.hs -o ../jlc

runtime:
	llvm-as runtime.ll
	mv runtime.bc ../lib/runtime.bc

clean:
	-rm -f *.log *.aux *.hi *.o *.dvi
	-rm -f DocJavalette.ps
	-rm -f ../jlc
	-rm -f ../jlc.exe
	-rm -f ../*.bc
	-rm -f ../*.exe
	-rm -f ../*.ll
distclean: clean
	-rm -f DocJavalette.* LexJavalette.* ParJavalette.* LayoutJavalette.* SkelJavalette.* PrintJavalette.* TestJavalette.* AbsJavalette.* TestJavalette ErrM.* SharedString.* Javalette.dtd XMLJavalette.*

