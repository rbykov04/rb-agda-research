.PHONY: run clean

#exports
run: Free2List
	./Free2List

Free2List: Example/Experimental/Free2List.agda
	agda  -i. --compile  --library=standard-library-2.2 Example/Experimental/Free2List.agda

runRep: Reproduce
	./Reproduce

Reproduce: MAlonzo
	ghc -O -o Reproduce \
		-Werror -i. \
		-main-is MAlonzo.Code.Example.Reproduce \
		MAlonzo/Code/Example/Reproduce.hs \
		--make -fwarn-incomplete-patterns




MAlonzo: Example/Reproduce.agda
	agda  -i. --ghc-dont-call-ghc --compile --library=standard-library-2.2 Example/Reproduce.agda

run1: build/jAgda.Example.IO.js
	NODE_PATH=./build node build/jAgda.Example.IO.js

IO: Example/IO.agda
	agda  -i. --compile  --library=standard-library-2.2 Example/IO.agda

build/jAgda.Example.IO.js: Example/IO.agda
	agda  -i. --js --compile-dir=build --library=standard-library-2.2 Example/IO.agda

Teletype: Example/Teletype.agda
	agda  -i. --compile --library=standard-library-2.2 Example/Teletype.agda

CustomOutHandler: Example/CustomOutHandler.agda
	agda  -i. --compile --library=standard-library-2.2 Example/CustomOutHandler.agda

clean:
	rm -rf Malonzo
	rm -rf Reproduce
	rm -rf dist-newstyle
	rm -rf *.agdai
	rm -rf Mystdlib/*.agdai
	rm -rf Example/*.agdai
	rm -rf Effect/*.agdai
	rm -rf Effect/Free/*.agdai
	rm -rf Effect/Hefty/*.agdai
	rm -f Hefty
	rm -f Teletype
	rm -f IO
	rm -f CustomOutHandler
	rm -f *.js
	rm -rf build
	rm -f Free2List
